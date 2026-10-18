import ModalityInference.Proofs.ComparisonPartialPropagationSeeds
import ModalityInference.Proofs.ComparisonDeclaredAnchorsTermination
import ModalityInference.Proofs.BackendComplete
import ModalityInference.Proofs.ComparisonDeclaredAnchors
import ModalityInference.Proofs.ComparisonSubsumptionTermination

/-! Eventual public acceptance of literal declared whole-type edges. No finite
shape model, residual-bounds restriction, or consistency premise is required. -/
namespace ModalityInference

private def EventualSuccess {α : Type} (P : α → Prop) (f : Nat → RunResult α) : Prop :=
  ∃n x, P x ∧ ∀fuel ≥ n, f fuel = .success x

private theorem EventualSuccess.bind {α β : Type} {P : α → Prop} {Q : β → Prop}
    {f : Nat → RunResult α} {g : Nat → α → RunResult β}
    (hf : EventualSuccess P f) (hg : ∀x, P x → EventualSuccess Q (fun fuel => g fuel x)) :
    EventualSuccess Q (fun fuel => (f fuel).bind (g fuel)) := by
  obtain ⟨n, x, hx, hn⟩ := hf
  obtain ⟨m, y, hy, hm⟩ := hg x hx
  exact ⟨max n m, y, hy, fun fuel hf => by
    dsimp only
    rw [hn fuel ((Nat.le_max_left _ _).trans hf)]
    exact hm fuel ((Nat.le_max_right _ _).trans hf)⟩

private theorem EventualSuccess.pure {α : Type} {P : α → Prop} {x : α} (hx : P x) :
    EventualSuccess P (fun _ => .success x) := ⟨0, x, hx, fun _ _ => rfl⟩

private theorem EventualSuccess.forIn {α β : Type} {P : β → Prop}
    (xs : List α) {f : Nat → α → β → RunResult (ForInStep β)}
    (hf : ∀x ∈ xs, ∀s, P s → EventualSuccess
      (fun r => match r with | .done s | .yield s => P s) (fun fuel => f fuel x s))
    (initial : β) (hi : P initial) :
    EventualSuccess P (fun fuel => forIn xs initial (f fuel)) := by
  induction xs generalizing initial with
  | nil => exact .pure hi
  | cons x xs ih =>
      simp only [List.forIn_cons]
      apply EventualSuccess.bind (hf x (by simp) initial hi)
      intro next hn
      cases next with
      | done s => exact .pure hn
      | yield s => exact ih (fun x hx => hf x (by simp [hx])) s hn

namespace ComparisonPartialPropagation

theorem modeEdges_eventual_sound (assumptions : Bounds) (labels : List ModExpr) :
    ∃n edges, (∀a b, (a,b) ∈ edges → Submode assumptions a b) ∧
      ∀fuel ≥ n, modeEdges fuel assumptions labels = .success edges := by
  let Valid := fun edges : List (ModExpr × ModExpr) => ∀a b, (a,b) ∈ edges → Submode assumptions a b
  change EventualSuccess Valid _
  unfold modeEdges
  apply EventualSuccess.bind (P := Valid)
  · apply EventualSuccess.forIn (P := Valid)
    · intro a ha result hresult
      apply EventualSuccess.bind (P := Valid)
      · apply EventualSuccess.forIn (P := Valid)
        · intro b hb result hresult
          obtain ⟨n, report, hn⟩ := ConcreteBackend.decideFormula_complete
            (.imp (boundsModeFormula assumptions) (boundsModeFormula [.mode a b]))
          have hs : ∀fuel ≥ n, ConcreteBackend.entails fuel assumptions [.mode a b] =
              .success report := hn
          refine ⟨n, .yield (if report.valid then (a,b) :: result else result), ?_, ?_⟩
          · dsimp only
            split
            · rename_i hv
              intro x y hxy
              rcases List.mem_cons.mp hxy with he | hm
              · have he' := Prod.mk.inj he
                rcases he' with ⟨rfl, rfl⟩
                exact ConcreteBackend.entails_submode (hs n le_rfl) hv
              · exact hresult x y hm
            · exact hresult
          · intro fuel hf
            simp only [hs fuel hf, bind, pure, RunResult.bind]
            split <;> rfl
        · exact hresult
      · intro result hr
        exact EventualSuccess.pure hr
    · intro a b hab
      simp at hab
  · intro result hr
    exact EventualSuccess.pure hr

theorem wellShaped_ofTy (shapes : TypeVar → ComparisonShape) (a : Ty) :
    wellShaped shapes (.ofTy a) = true := by
  induction a <;> simp_all [CompareTy.ofTy, wellShaped]

theorem expose_wellShaped {shapes : TypeVar → ComparisonShape} {a : CompareTy}
    (ha : wellShaped shapes a = true) (m : ModExpr) {t : CompareTy}
    (ht : t ∈ expose a m) : wellShaped shapes t = true := by
  induction a generalizing m t with
  | var v | unit | credit =>
      simp only [expose, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
      have hab : wellShaped shapes a = true ∧ wellShaped shapes b = true := by
        simpa only [wellShaped, Bool.and_eq_true] using ha
      simp only [expose, List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | rfl | ht | ht
      · exact ha
      · exact ha
      · exact iha hab.1 _ ht
      · exact ihb hab.2 _ ht
  | modal a n ih =>
      simp only [expose, List.mem_cons, List.mem_append, or_assoc] at ht
      rcases ht with rfl | rfl | ht | ht
      · exact ha
      · exact ha
      · exact ih ha _ ht
      · exact ih ha _ ht
  | join a b iha ihb | meet a b iha ihb =>
      have hab : wellShaped shapes a = true ∧ wellShaped shapes b = true := by
        exact (show (wellShaped shapes a = true ∧ wellShaped shapes b = true) ∧ _
          from by simpa only [wellShaped, Bool.and_eq_true] using ha).1
      simp only [expose, List.mem_cons, List.mem_append] at ht
      rcases ht with rfl | rfl | ht | ht
      · exact ha
      · exact ha
      · exact iha hab.1 _ ht
      · exact ihb hab.2 _ ht

theorem expose_self (a : CompareTy) (m : ModExpr) : a ∈ expose a m := by
  cases a <;> simp [expose]

end ComparisonPartialPropagation
namespace ComparisonDeclaredAnchors

open ComparisonPartialPropagation

@[simp] theorem shapeCheck_modal (shapes : ComparisonShapeSolver.Result)
    (a : CompareTy) (m : ModExpr) : shapeCheck shapes (.modal a m) = shapeCheck shapes a := by
  cases shapes <;> rfl

theorem shapeCheck_expose_ofTy (shapes : ComparisonShapeSolver.Result) (a : Ty)
    (m : ModExpr) {t : CompareTy} (ht : t ∈ expose (.ofTy a) m) :
    shapeCheck shapes t = true := by
  cases shapes with
  | infeasibleAssumptions => rfl
  | solved shapes => exact expose_wellShaped (wellShaped_ofTy _ _) _ ht

private theorem empty_ty (a : Ty) : ({} : CompareSubstitution).ty a = .ofTy a := by
  change (CompareSubstitution.ofSubstitution {}).ty a = _
  rw [CompareSubstitution.ofSubstitution_ty]
  congr 1
  exact (a.subst_congr (fun v _ => by cases v <;> rfl)
    (fun v _ => by cases v <;> rfl)).trans a.subst_id

private theorem empty_bounds (cs : Bounds) :
    ({} : CompareSubstitution).bounds cs = cs.map CompareConstraint.ofConstraint := by
  change (CompareSubstitution.ofSubstitution {}).bounds cs = _
  simp

private theorem pairs_wellFormedBounds (a : Ty) :
    ComparisonShape.pairs a.wellFormedBounds = [] := by
  induction a <;> simp_all [ComparisonShape.pairs, TypeExpr.wellFormedBounds]

private theorem comparisons_wellFormedBounds (a : Ty) :
    (a.wellFormedBounds.map CompareConstraint.ofConstraint).flatMap comparisons = [] := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, comparisons, CompareConstraint.ofConstraint]

private theorem guards_wellFormedBounds (a : Ty) :
    (a.wellFormedBounds.map CompareConstraint.ofConstraint).flatMap guards = a.wellFormedBounds := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, guards, CompareConstraint.ofConstraint]

theorem shapePrepare_declared_edge {p : SchemePreparation.Prepared}
    (hb : p.sourceBounds = p.sourceType.wellFormedBounds)
    (hedge : Constraint.sub p.sourceType p.targetType ∈ p.assumptions) :
    ∃n shapes, ∀fuel ≥ n, ComparisonShapeSolver.prepare fuel p = .success shapes := by
  open ComparisonShapeSolver in
  obtain ⟨n, result, hn, he⟩ := ComparisonShapeSolver.unify_eventually
    (fun _ => true) (ComparisonShape.pairs p.assumptions)
  cases result with
  | exhausted => exact False.elim (hn rfl)
  | rejected reason =>
      exact ⟨n, .infeasibleAssumptions, fun fuel hf => by
        simp [ComparisonShapeSolver.prepare, he fuel hf]⟩
  | success fixed =>
      have hp : (ComparisonShape.ofTy p.sourceType).subst (ComparisonShapeSolver.action fixed) =
          (ComparisonShape.ofTy p.targetType).subst (ComparisonShapeSolver.action fixed) := by
        exact ComparisonShapeSolver.unify_sound (he n le_rfl)
          (ComparisonShape.ofTy p.sourceType, ComparisonShape.ofTy p.targetType)
          (List.mem_flatMap.mpr ⟨.sub p.sourceType p.targetType, hedge, by simp⟩)
      refine ⟨max n 2, .solved ⟨fixed, []⟩, fun fuel hf => ?_⟩
      have hf' : 2 ≤ fuel := (Nat.le_max_right _ _).trans hf
      obtain ⟨fuel, rfl⟩ := Nat.exists_eq_add_of_le hf'
      simp only [ComparisonShapeSolver.prepare, he _ ((Nat.le_max_left _ _).trans hf)]
      simp only [ComparisonShapeSolver.sourcePairs, hb, pairs_wellFormedBounds,
        List.nil_append, ComparisonShapeSolver.mapPairs, List.map_cons, List.map_nil, hp]
      simp [ComparisonShapeSolver.unify, Nat.add_comm, bind, pure, RunResult.bind]

private theorem action_empty {p : SchemePreparation.Prepared}
    (ht : p.firstType = p.nextType) : action p = {} := by
  simp [action, ← ht]

private theorem obligations_comparisons {p : SchemePreparation.Prepared}
    (hb : p.sourceBounds = p.sourceType.wellFormedBounds) :
    (obligations p {}).flatMap comparisons = [(.ofTy p.sourceType, .ofTy p.targetType)] := by
  simp [obligations, empty_ty, empty_bounds, hb, comparisons_wellFormedBounds, comparisons]

private theorem obligations_guards {p : SchemePreparation.Prepared}
    (hb : p.sourceBounds = p.sourceType.wellFormedBounds) :
    (obligations p {}).flatMap guards = p.sourceType.wellFormedBounds ++
      p.sourceType.wellFormedBounds ++ p.targetType.wellFormedBounds := by
  simp [obligations, empty_ty, empty_bounds, hb, guards_wellFormedBounds, guards, List.append_assoc]

private theorem vertices_shapes {p : SchemePreparation.Prepared}
    (hb : p.sourceBounds = p.sourceType.wellFormedBounds)
    (shapes : ComparisonShapeSolver.Result) {t : CompareTy}
    (ht : t ∈ vertices p {}) : shapeCheck shapes t = true := by
  simp only [vertices, obligations_comparisons hb, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_dedup, List.mem_append] at ht
  rcases ht with (ht | ht) | ht
  · exact shapeCheck_expose_ofTy shapes _ _ ht
  · exact shapeCheck_expose_ofTy shapes _ _ ht
  · obtain ⟨a, _, ht⟩ := List.mem_flatMap.mp ht
    exact shapeCheck_expose_ofTy shapes _ _ ht

private theorem vertices_endpoints {p : SchemePreparation.Prepared}
    (hb : p.sourceBounds = p.sourceType.wellFormedBounds) :
    CompareTy.ofTy p.sourceType ∈ vertices p {} ∧ CompareTy.ofTy p.targetType ∈ vertices p {} := by
  simp only [vertices, obligations_comparisons hb, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_dedup, List.mem_append]
  exact ⟨.inl (.inl (expose_self _ _)), .inl (.inr (expose_self _ _))⟩

theorem checkPairs_declared_edge {p : SchemePreparation.Prepared}
    (hb : p.sourceBounds = p.sourceType.wellFormedBounds)
    (hedge : Constraint.sub p.sourceType p.targetType ∈ p.assumptions)
    (shapes : ComparisonShapeSolver.Result) (edges : List (ModExpr × ModExpr))
    {fuel : Nat} (hf : 0 < fuel) :
    checkPairs fuel p shapes edges (initialGraph p.assumptions (vertices p {}))
      ((obligations p {}).flatMap comparisons) = .success true := by
  have hv := vertices_endpoints hb
  obtain ⟨c, hc⟩ := initialGraph_bound hedge hv.1 hv.2
  have hchecked : (initialGraph p.assumptions (vertices p {})).Checked
      (shapeCheck shapes) (fun a b => edges.contains (a,b)) p.assumptions := by
    apply initialGraph_checked
    intro a ha c hc
    exact axioms_checked (shapeCheck_modal shapes) (vertices_shapes hb shapes ha) hc
  obtain ⟨hl, hr, hcert⟩ := hchecked _ _ _ hc
  cases fuel with
  | zero => omega
  | succ fuel =>
      simpa [obligations_comparisons hb, checkPairs, checkPair, saturate, hc,
        hl, hr, bind, pure, RunResult.bind] using hcert

/-- Whole declared edges have an eventually successful checked certificate,
without requiring a finite model of the declared shape equations. -/
theorem attempt_declared_edge {p : SchemePreparation.Prepared}
    (ht : p.firstType = p.nextType) (hm : p.firstMode = p.nextMode)
    (hb : p.sourceBounds = p.sourceType.wellFormedBounds)
    (hedge : Constraint.sub p.sourceType p.targetType ∈ p.assumptions)
    (hguards : ∀η, ModeModels p.assumptions η →
      ModeModels (p.sourceType.wellFormedBounds ++ p.targetType.wellFormedBounds) η) :
    ∃n result, ∀fuel ≥ n, attempt fuel p = .success (some result) := by
  obtain ⟨n, shapes, hn⟩ := shapePrepare_declared_edge hb hedge
  obtain ⟨k, edges, hedges, hk⟩ := modeEdges_eventual_sound p.assumptions
    (modeLabels (vertices p {}))
  obtain ⟨j, report, hj⟩ := ConcreteBackend.decideFormula_complete
    (.imp (boundsModeFormula p.assumptions)
      (boundsModeFormula (edges.map (fun (a,b) => Constraint.mode a b) ++
        (obligations p {}).flatMap guards)))
  have hj' : ∀fuel ≥ j, ConcreteBackend.entails fuel p.assumptions
      (edges.map (fun (a,b) => Constraint.mode a b) ++
        (obligations p {}).flatMap guards) = .success report := hj
  have hvalid : report.valid = true := by
    apply (ConcreteBackend.entails_correct (hj' j le_rfl)).mpr
    intro η hη c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨⟨a,b⟩, hab, rfl⟩ := List.mem_map.mp hc
      exact (hedges a b hab).denote hη
    · rw [obligations_guards hb] at hc
      rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_append.mp hc with hc | hc
        all_goals exact hguards η hη c (List.mem_append_left _ hc)
      · exact hguards η hη c (List.mem_append_right _ hc)
  refine ⟨max (max n k) (max j 1), ⟨shapes, {}, edges, report⟩, fun fuel hf => ?_⟩
  have hn' : n ≤ fuel := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans hf)
  have hk' : k ≤ fuel := (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hf)
  have hj'' : j ≤ fuel := (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans hf)
  have hf' : 0 < fuel := Nat.lt_of_lt_of_le (by decide : 0 < 1)
    ((Nat.le_max_right _ _).trans ((Nat.le_max_right _ _).trans hf))
  simp [attempt, hm, action_empty ht, hn fuel hn', hk fuel hk', hj' fuel hj'',
    hvalid, checkPairs_declared_edge hb hedge shapes edges hf', bind, pure, RunResult.bind]

private theorem ordinary_empty_ty (a : Ty) : ({} : Substitution).ty a = a :=
  (a.subst_congr (fun v _ => by cases v <;> rfl)
    (fun v _ => by cases v <;> rfl)).trans a.subst_id

private theorem mono_prepared (Δ : Bounds) (a b : Ty) :
    let p := SchemePreparation.prepare [] (Scheme.mono a).requireDefinedInstances
      { bounds := Δ, body := b }
    p.firstType = p.nextType ∧ p.firstMode = p.nextMode ∧
      p.sourceBounds = a.wellFormedBounds ∧ p.sourceType = a ∧ p.targetType = b ∧
      p.assumptions = Δ.assumptions ∧ p.sourceRenaming = {} := by
  simp [SchemePreparation.prepare, Scheme.mono, Scheme.requireDefinedInstances,
    Scheme.instanceGuards, Scheme.freshSubstitution, ordinary_empty_ty]

/-- The whole declared bound is accepted with every written endpoint guard and
without a residual-bounds or finite-shape-model condition. -/
theorem run_declared_edge {Δ : Bounds} {a b : Ty} (h : Constraint.sub a b ∈ Δ) :
    ∃n, ∀fuel ≥ n, run fuel (Scheme.mono a) { bounds := Δ, body := b } = .success {} := by
  let p := SchemePreparation.prepare [] (Scheme.mono a).requireDefinedInstances
    { bounds := Δ, body := b }
  obtain ⟨ht, hm, hb, ha, htgt, hΔ, hr⟩ := mono_prepared Δ a b
  have hedge : Constraint.sub p.sourceType p.targetType ∈ p.assumptions := by
    rw [ha, htgt, hΔ]
    exact List.mem_flatMap.mpr ⟨.sub a b, h, by simp [Constraint.assumptions]⟩
  have hg : ∀η, ModeModels p.assumptions η →
      ModeModels (p.sourceType.wellFormedBounds ++ p.targetType.wellFormedBounds) η := by
    intro η hη c hc
    rw [ha, htgt] at hc
    rw [hΔ] at hη
    apply hη c
    refine List.mem_flatMap.mpr ⟨.sub a b, h, ?_⟩
    rcases List.mem_append.mp hc with hc | hc
    · simp [Constraint.assumptions, hc]
    · simp [Constraint.assumptions, hc]
  have hsource : p.sourceType = a := ha
  have hbound : p.sourceBounds = p.sourceType.wellFormedBounds :=
    hb.trans (congrArg TypeExpr.wellFormedBounds hsource).symm
  obtain ⟨n, result, hn⟩ := attempt_declared_edge (p := p) ht hm hbound hedge hg
  refine ⟨n, fun fuel hf => ?_⟩
  change (attempt fuel p).bind _ = _
  simp only [hn fuel hf, RunResult.bind]
  simp [ComparisonPreparation.reconstruct, hr, pure]

end ComparisonDeclaredAnchors


/-- Every literal monomorphic declared subtype edge is eventually accepted by
the public checker, with its original endpoint-definedness guards. -/
theorem checkSubsumption_declared_edge_complete {Δ : Bounds} {a b : Ty}
    (h : Constraint.sub a b ∈ Δ) :
    ∃n, ∀fuel ≥ n, ∃e,
      checkSubsumption fuel (Scheme.mono a) { bounds := Δ, body := b } = .success e := by
  let source := Scheme.mono a
  let target : Scheme := { bounds := Δ, body := b }
  obtain ⟨n, result, hr, hn⟩ := ComparisonChecker.run_terminates source.requireDefinedInstances target
  obtain ⟨m, joint, hj, hm⟩ := (ComparisonJointChecker.run_settles source target).2
  obtain ⟨k, hk⟩ := ComparisonDeclaredAnchors.run_declared_edge h
  refine ⟨max (max n m) k, fun fuel hf => ?_⟩
  have hn' : n ≤ fuel := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans hf)
  have hm' : m ≤ fuel := (Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans hf)
  have hk' : k ≤ fuel := (Nat.le_max_right _ _).trans hf
  change ∃e, checkSubsumption fuel source target = .success e
  rw [checkSubsumption, hn fuel hn']
  cases result with
  | success e => exact ⟨e, rfl⟩
  | exhausted => exact False.elim (hr rfl)
  | rejected reason =>
      simp only [comparisonFallback, hm fuel hm']
      cases joint with
      | exhausted => exact False.elim (hj rfl)
      | success action => exact ⟨jointSubsumptionEvidence source target action, rfl⟩
      | rejected reason =>
          refine ⟨jointSubsumptionEvidence source target {}, ?_⟩
          have ha : ComparisonDeclaredAnchors.run fuel source target = .success {} := hk fuel hk'
          simp [ha, bind, pure, RunResult.bind]

end ModalityInference
