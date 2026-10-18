import ModalityInference.Proofs.ComparisonNestedAnchorContexts
import ModalityInference.Proofs.ComparisonDeclaredEdgeCompleteness

/-! Eventual acceptance when structural interpolation reconstructs original
declared endpoints. Shape inconsistency discharges only the shape check;
every original type edge and scalar guard is still certified. -/
namespace ModalityInference.ComparisonNestedAnchors

open ComparisonPartialPropagation ComparisonDeclaredAnchors

def Seeded (Δ : Bounds) (pair : CompareTy × CompareTy) : Prop :=
  pair.1 = pair.2 ∨ ∃a b : Ty, pair = (.ofTy a,.ofTy b) ∧ Constraint.sub a b ∈ Δ

theorem vertices_pair {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    {pair : CompareTy × CompareTy} (h : pair ∈ (obligations p σ).flatMap comparisons) :
    pair.1 ∈ vertices p σ ∧ pair.2 ∈ vertices p σ := by
  constructor
  all_goals
    apply List.mem_dedup.mpr
    apply List.mem_append_left
    refine List.mem_flatMap.mpr ⟨pair,h,?_⟩
  · exact List.mem_append_left _ (expose_self _ _)
  · exact List.mem_append_right _ (expose_self _ _)

theorem initialGraph_refl {Δ : Bounds} {nodes : List CompareTy} {a : CompareTy}
    (ha : a ∈ nodes) : ∃c, (initialGraph Δ nodes).get a a = some c := by
  refine Graph.get_fold_add_seed (g := Graph.empty nodes) (c := .refl a)
    (by simp [Graph.empty]) ?_ ?_ ?_
  · apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨a,ha,by simp [axioms]⟩
  · simpa [Graph.empty, Certificate.left] using ha
  · simpa [Graph.empty, Certificate.right] using ha

theorem checkPair_seeded {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    {pair : CompareTy × CompareTy}
    (hp : pair ∈ (obligations p σ).flatMap comparisons)
    (hs : Seeded p.assumptions pair) (edges : List (ModExpr × ModExpr))
    {fuel : Nat} (hf : 0 < fuel) :
    checkPair fuel p .infeasibleAssumptions edges
      (initialGraph p.assumptions (vertices p σ)) pair = .success true := by
  have hv := vertices_pair hp
  have hex : ∃c, (initialGraph p.assumptions (vertices p σ)).get pair.1 pair.2 = some c := by
    rcases hs with he | ⟨a,b,rfl,hab⟩
    · rw [← he]
      exact initialGraph_refl hv.1
    · exact initialGraph_bound hab hv.1 hv.2
  obtain ⟨c,hc⟩ := hex
  have hcheck : (initialGraph p.assumptions (vertices p σ)).Checked
      (shapeCheck .infeasibleAssumptions) (fun a b => edges.contains (a,b)) p.assumptions := by
    apply initialGraph_checked
    intro a ha c hc
    exact axioms_checked (fun _ _ => rfl) rfl hc
  obtain ⟨hl,hr,hcert⟩ := hcheck _ _ _ hc
  cases fuel with
  | zero => omega
  | succ fuel =>
      simpa [checkPair,saturate,hc,hl,hr,bind,pure,RunResult.bind] using hcert

theorem checkPairs_seeded {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (hs : ∀pair ∈ (obligations p σ).flatMap comparisons, Seeded p.assumptions pair)
    (edges : List (ModExpr × ModExpr)) {fuel : Nat} (hf : 0 < fuel) :
    checkPairs fuel p .infeasibleAssumptions edges
      (initialGraph p.assumptions (vertices p σ))
      ((obligations p σ).flatMap comparisons) = .success true := by
  have go : ∀ps, (∀pair ∈ ps, pair ∈ (obligations p σ).flatMap comparisons) →
      checkPairs fuel p .infeasibleAssumptions edges
        (initialGraph p.assumptions (vertices p σ)) ps = .success true := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons pair ps ih =>
        intro hp
        have hpair := hp pair (by simp)
        simp only [checkPairs,checkPair_seeded hpair (hs pair hpair) edges hf,
          bind,RunResult.bind,Bool.not_true,Bool.false_eq_true,↓reduceIte]
        exact ih (fun q hq => hp q (by simp [hq]))
  exact go _ (fun _ h => h)

theorem prepare_no_models {p : SchemePreparation.Prepared}
    (h : ¬∃ρ, ComparisonShape.Models p.assumptions ρ) :
    ∃n, ∀fuel ≥ n, ComparisonShapeSolver.prepare fuel p = .success .infeasibleAssumptions := by
  obtain ⟨n,result,hr,hn⟩ := ComparisonShapeSolver.unify_eventually (fun _ => true)
    (ComparisonShape.pairs p.assumptions)
  cases result with
  | exhausted => exact False.elim (hr rfl)
  | success σ =>
      exact False.elim (h ⟨ComparisonShapeSolver.action σ,
        ComparisonShapeSolver.unify_sound (hn n le_rfl)⟩)
  | rejected reason =>
      exact ⟨n,fun fuel hf => by simp [ComparisonShapeSolver.prepare,hn fuel hf]⟩

/-- This completeness rule applies to arbitrary nested endpoint syntax. Its
premises mention the computed interpolant, literal declared edges, and the
original scalar guards; there is no assumed successful certificate. -/
theorem attempt_seeded_complete {p : SchemePreparation.Prepared}
    (hm : p.firstMode = p.nextMode)
    (hnone : ¬∃ρ, ComparisonShape.Models p.assumptions ρ)
    (hs : ∀pair ∈ (obligations p (action p)).flatMap comparisons,
      Seeded p.assumptions pair)
    (hg : ∀η, ModeModels p.assumptions η →
      ModeModels ((obligations p (action p)).flatMap guards) η) :
    ∃n result, ∀fuel ≥ n, attempt fuel p = .success (some result) := by
  obtain ⟨n,hn⟩ := prepare_no_models hnone
  obtain ⟨k,edges,he,hk⟩ := modeEdges_eventual_sound p.assumptions
    (modeLabels (vertices p (action p)))
  obtain ⟨j,report,hj⟩ := ConcreteBackend.decideFormula_complete
    (.imp (boundsModeFormula p.assumptions)
      (boundsModeFormula (edges.map (fun (a,b) => Constraint.mode a b) ++
        (obligations p (action p)).flatMap guards)))
  have hj' : ∀fuel ≥ j, ConcreteBackend.entails fuel p.assumptions
      (edges.map (fun (a,b) => Constraint.mode a b) ++
        (obligations p (action p)).flatMap guards) = .success report := hj
  have hv : report.valid = true := by
    apply (ConcreteBackend.entails_correct (hj' j le_rfl)).mpr
    intro η hη c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨⟨a,b⟩,hab,rfl⟩ := List.mem_map.mp hc
      exact (he a b hab).denote hη
    · exact hg η hη c hc
  refine ⟨max (max n k) (max j 1),⟨.infeasibleAssumptions,action p,edges,report⟩,
    fun fuel hf => ?_⟩
  have hn' := (Nat.le_max_left n k).trans ((Nat.le_max_left _ _).trans hf)
  have hk' := (Nat.le_max_right n k).trans ((Nat.le_max_left _ _).trans hf)
  have hj'' := (Nat.le_max_left j 1).trans ((Nat.le_max_right _ _).trans hf)
  have hf' : 0 < fuel := Nat.lt_of_lt_of_le (by decide : 0 < 1)
    ((Nat.le_max_right j 1).trans ((Nat.le_max_right _ _).trans hf))
  simp [attempt,hm,hn fuel hn',shapeCheck,hk fuel hk',hj' fuel hj'',hv,
    checkPairs_seeded hs edges hf',bind,pure,RunResult.bind]

end ModalityInference.ComparisonNestedAnchors

namespace ModalityInference

theorem checkSubsumption_of_nested_result {fuel : Nat} {source target : Scheme}
    {action : CompareSubstitution}
    (hn : ComparisonNestedAnchors.run fuel source target = .success action)
    (hd : checkSubsumption fuel source target ≠ .exhausted) :
    ∃e, checkSubsumption fuel source target = .success e := by
  cases hc : ComparisonChecker.run fuel source.requireDefinedInstances target with
  | success e => exact ⟨e,by simp [checkSubsumption,hc]⟩
  | exhausted => exact False.elim (hd (by simp [checkSubsumption,hc]))
  | rejected reason =>
      cases hj : ComparisonJointChecker.run fuel source target with
      | success σ => exact ⟨jointSubsumptionEvidence source target σ,
          by simp [checkSubsumption,hc,comparisonFallback,hj,bind,pure,RunResult.bind]⟩
      | exhausted => exact False.elim (hd
          (by simp [checkSubsumption,hc,comparisonFallback,hj,bind,RunResult.bind]))
      | rejected reason =>
          cases ha : ComparisonDeclaredAnchors.run fuel source target with
          | success σ => exact ⟨jointSubsumptionEvidence source target σ,
              by simp [checkSubsumption,hc,comparisonFallback,hj,ha,bind,pure,RunResult.bind]⟩
          | exhausted => exact False.elim (hd
              (by simp [checkSubsumption,hc,comparisonFallback,hj,ha,bind,RunResult.bind]))
          | rejected reason => exact ⟨jointSubsumptionEvidence source target action,
              by simp [checkSubsumption,hc,comparisonFallback,hj,ha,hn,bind,pure,RunResult.bind]⟩

/-- Nested structural interpolation that recovers declared or reflexive whole
edges is eventually accepted by the public interface, including contexts whose
declared shape equations have no finite model. -/
theorem checkSubsumption_nested_seeded_complete (source target : Scheme)
    (hm : (SchemePreparation.prepare [] source.requireDefinedInstances target).firstMode =
      (SchemePreparation.prepare [] source.requireDefinedInstances target).nextMode)
    (hnone : ¬∃ρ, ComparisonShape.Models
      (SchemePreparation.prepare [] source.requireDefinedInstances target).assumptions ρ)
    (hs : let p := SchemePreparation.prepare [] source.requireDefinedInstances target
      ∀pair ∈ (ComparisonDeclaredAnchors.obligations p
        (ComparisonNestedAnchors.action p)).flatMap ComparisonDeclaredAnchors.comparisons,
      ComparisonNestedAnchors.Seeded p.assumptions pair)
    (hg : let p := SchemePreparation.prepare [] source.requireDefinedInstances target
      ∀η, ModeModels p.assumptions η → ModeModels
        ((ComparisonDeclaredAnchors.obligations p (ComparisonNestedAnchors.action p)).flatMap
          ComparisonDeclaredAnchors.guards) η) :
    ∃n, ∀fuel ≥ n, ∃e, checkSubsumption fuel source target = .success e := by
  obtain ⟨n,result,hr,hn⟩ := checkSubsumption_terminates source target
  obtain ⟨m,r,hm'⟩ := ComparisonNestedAnchors.attempt_seeded_complete hm hnone hs hg
  refine ⟨max n m,fun fuel hf => ?_⟩
  apply checkSubsumption_of_nested_result
    (action := ComparisonPreparation.reconstruct
      (SchemePreparation.prepare [] source.requireDefinedInstances target) r.action)
  · simp [ComparisonNestedAnchors.run,hm' fuel ((Nat.le_max_right _ _).trans hf),
      bind,pure,RunResult.bind]
  · rw [hn fuel ((Nat.le_max_left _ _).trans hf)]
    exact hr

end ModalityInference
