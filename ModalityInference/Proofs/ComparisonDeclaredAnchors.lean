import ModalityInference.ComparisonDeclaredAnchors
import ModalityInference.Proofs.ComparisonPartialPropagation
import ModalityInference.Proofs.ComparisonDefinedInstances
import ModalityInference.Proofs.ComparisonCheckerSolution
import ModalityInference.Proofs.ComparisonInfeasibleShapes

/-! Checked whole-type anchor propagation preserves the original declared
assumptions and all source instance guards. -/
namespace ModalityInference.ComparisonDeclaredAnchors

open ComparisonPartialPropagation

theorem shapeCheck_sound {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Result} {a : CompareTy}
    (hs : ComparisonShapeSolver.prepare fuel p = .success shapes)
    (ha : shapeCheck shapes a = true) : a.WellShaped p.assumptions := by
  cases shapes with
  | infeasibleAssumptions => exact ComparisonShapeSolver.prepare_infeasible_wellShaped hs a
  | solved shapes => exact wellShaped_prepared hs ha

theorem checkPair_sound {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Result} {edges : List (ModExpr × ModExpr)}
    {graph : Graph} {pair : CompareTy × CompareTy}
    (hs : ComparisonShapeSolver.prepare fuel p = .success shapes)
    (hm : ∀ a b, (a, b) ∈ edges → Submode p.assumptions a b)
    (h : checkPair fuel p shapes edges graph pair = .success true) :
    AlgebraSubtype p.assumptions pair.1 pair.2 := by
  simp only [checkPair, bind, pure, RunResult.bind] at h
  cases hc : saturate (fun a b => edges.contains (a, b)) pair.1 pair.2 fuel graph with
  | rejected reason | exhausted => rw [hc] at h; cases h
  | success candidate =>
      cases candidate with
      | none => rw [hc] at h; cases h
      | some c =>
          simp only [hc, RunResult.success.injEq, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
          have hh := Certificate.check_sound (fun t ht => shapeCheck_sound hs ht)
            (fun a b hab => hm a b (by simpa only [List.contains_iff] using hab)) h.2.2
          simpa only [h.1, h.2.1] using hh

theorem checkPairs_sound {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Result} {edges : List (ModExpr × ModExpr)}
    {graph : Graph} {pairs : List (CompareTy × CompareTy)}
    (hs : ComparisonShapeSolver.prepare fuel p = .success shapes)
    (hm : ∀ a b, (a, b) ∈ edges → Submode p.assumptions a b)
    (h : checkPairs fuel p shapes edges graph pairs = .success true) :
    ∀ pair ∈ pairs, AlgebraSubtype p.assumptions pair.1 pair.2 := by
  induction pairs with
  | nil => simp
  | cons pair rest ih =>
      simp only [checkPairs, bind, pure, RunResult.bind] at h
      cases hp : checkPair fuel p shapes edges graph pair with
      | rejected reason | exhausted => rw [hp] at h; cases h
      | success ok =>
          cases ok
          · rw [hp] at h; cases h
          · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
            exact List.forall_mem_cons.mpr ⟨checkPair_sound hs hm hp, ih h⟩

theorem constraint_sound {Δ : Bounds} {c : CompareConstraint}
    (hp : ∀ pair ∈ comparisons c, AlgebraSubtype Δ pair.1 pair.2)
    (hm : ∀ η, ModeModels Δ η → ModeModels (guards c) η) :
    AlgebraEntails Δ c := by
  cases c <;> simp_all only [comparisons, guards, AlgebraEntails, List.forall_mem_cons,
    true_and, CompareTy.DefinedUnder, ModeModels, List.mem_append,
    or_imp, forall_and, List.mem_singleton, forall_eq, ModeSatisfies]
  all_goals first | exact hm | exact .valid hm

structure AttemptSpec (fuel : Nat) (p : SchemePreparation.Prepared) (r : Result) : Prop where
  modeRange : p.firstMode = p.nextMode
  shapes : ComparisonShapeSolver.prepare fuel p = .success r.shapes
  action_eq : r.action = action p
  imageShapes : ∀ entry ∈ r.action.types, shapeCheck r.shapes entry.2 = true
  backend : ConcreteBackend.entails fuel p.assumptions
    (r.scalarEdges.map (fun (a, b) => Constraint.mode a b) ++
      (obligations p r.action).flatMap guards) = .success r.backend
  valid : r.backend.valid = true
  checked : checkPairs fuel p r.shapes r.scalarEdges
    (initialGraph p.assumptions (vertices p r.action))
    ((obligations p r.action).flatMap comparisons) = .success true

theorem attempt_spec {fuel : Nat} {p : SchemePreparation.Prepared} {r : Result}
    (h : attempt fuel p = .success (some r)) : AttemptSpec fuel p r := by
  simp only [attempt, bind, pure, RunResult.bind] at h
  split at h
  · cases h
  next hmode =>
    cases hs : ComparisonShapeSolver.prepare fuel p with
    | rejected reason | exhausted => rw [hs] at h; cases h
    | success shapes =>
        simp only [hs] at h
        split at h
        · cases h
        next himages =>
          cases he : modeEdges fuel p.assumptions (modeLabels (vertices p (action p))) with
          | rejected reason | exhausted => rw [he] at h; cases h
          | success edges =>
              simp only [he] at h
              cases hb : ConcreteBackend.entails fuel p.assumptions
                  (edges.map (fun (a, b) => Constraint.mode a b) ++
                    (obligations p (action p)).flatMap guards) with
              | rejected reason | exhausted => rw [hb] at h; cases h
              | success report =>
                  simp only [hb] at h
                  split at h
                  · cases h
                  next hvalid =>
                    cases hp : checkPairs fuel p shapes edges
                        (initialGraph p.assumptions (vertices p (action p)))
                        ((obligations p (action p)).flatMap comparisons) with
                    | rejected reason | exhausted => rw [hp] at h; cases h
                    | success ok =>
                        cases ok
                        · rw [hp] at h; cases h
                        · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                            RunResult.success.injEq, Option.some.injEq] at h
                          subst r
                          exact
                            { modeRange := by simpa using hmode
                              shapes := hs
                              action_eq := rfl
                              imageShapes := by simpa using himages
                              backend := hb
                              valid := by simpa using hvalid
                              checked := hp }

theorem attempt_sound {fuel : Nat} {p : SchemePreparation.Prepared} {r : Result}
    (h : attempt fuel p = .success (some r)) :
    r.action.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (r.action.bounds p.sourceBounds) ∧
      AlgebraSubtype p.assumptions (r.action.ty p.sourceType) (.ofTy p.targetType) := by
  have hs := attempt_spec h
  have hmodels := (ConcreteBackend.entails_correct hs.backend).mp hs.valid
  have hmode : ∀ a b, (a, b) ∈ r.scalarEdges → Submode p.assumptions a b := by
    intro a b hab
    exact .valid fun η hη => hmodels η hη (.mode a b)
      (List.mem_append_left _ (List.mem_map.mpr ⟨(a, b), hab, rfl⟩))
  have hp := checkPairs_sound hs.shapes hmode hs.checked
  have hc : AlgebraEntailsAll p.assumptions (obligations p r.action) := by
    intro c hc
    apply constraint_sound
    · intro pair hpair
      exact hp pair (List.mem_flatMap.mpr ⟨c, hc, hpair⟩)
    · intro η hη g hg
      exact hmodels η hη g (List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, hc, hg⟩))
  exact ⟨fun entry he => shapeCheck_sound hs.shapes (hs.imageShapes entry he),
    fun c hc' => hc c (List.mem_append_left _ hc'),
    (hc (.sub (r.action.ty p.sourceType) (.ofTy p.targetType))
      (List.mem_append_right _ (List.mem_singleton_self _))).1⟩

theorem action_domainsAbove (p : SchemePreparation.Prepared) :
    (action p).DomainsAbove p.firstType p.firstMode := by
  constructor
  · rintro entry he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hn
    exact Nat.le_add_right _ _
  · simp [action]

theorem attempt_reconstruct {fuel : Nat} {ambient : Bounds} {source target : Scheme} {r : Result}
    (h : attempt fuel (SchemePreparation.prepare ambient source target) = .success (some r)) :
    let p := SchemePreparation.prepare ambient source target
    let result := ComparisonPreparation.reconstruct p r.action
    result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  let p := SchemePreparation.prepare ambient source target
  obtain ⟨hs, hb, ht⟩ := attempt_sound h
  have hd : r.action.DomainsAbove p.firstType p.firstMode :=
    (attempt_spec h).action_eq.symm ▸ action_domainsAbove p
  have htypes : ∀ v ∈ source.body.typeVars ∪ source.bounds.typeVars,
      r.action.type v = .var v := by
    intro v hv
    apply hd.type_fixed
    apply SchemePreparation.original_type_lt_first
    have hv' := Finset.mem_union.mp hv
    simp only [SchemePreparation.originalTypeIds, List.mem_append,
      TypeExpr.mem_typeVariables, Bounds.mem_typeVariables]
    tauto
  have hmodes : ∀ v ∈ source.body.modVars ∪ source.bounds.modVars,
      r.action.mode v = .var v := by
    intro v hv
    apply hd.mode_fixed
    apply SchemePreparation.original_mode_lt_first
    have hv' := Finset.mem_union.mp hv
    simp only [SchemePreparation.originalModeIds, List.mem_append,
      TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
    tauto
  refine ⟨ComparisonPreparation.reconstruct_wellShaped hs, ?_, ?_⟩
  · exact (ComparisonPreparation.reconstruct_algebra_bounds p r.action source.bounds p.assumptions
      (fun v hv => htypes v (Finset.mem_union_right _ hv))
      (fun v hv => hmodes v (Finset.mem_union_right _ hv))).mpr hb
  · change AlgebraSubtype p.assumptions
      ((ComparisonPreparation.reconstruct p r.action).ty source.body) (.ofTy p.targetType)
    rw [ComparisonPreparation.reconstruct_ty p r.action source.body
      (fun v hv => htypes v (Finset.mem_union_left _ hv))
      (fun v hv => hmodes v (Finset.mem_union_left _ hv))]
    exact ht

theorem run_success {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel source target = .success result) :
    ∃ r, attempt fuel (SchemePreparation.prepare [] source.requireDefinedInstances target) =
      .success (some r) ∧ result = ComparisonPreparation.reconstruct
        (SchemePreparation.prepare [] source.requireDefinedInstances target) r.action := by
  simp only [run, bind, pure, RunResult.bind] at h
  cases ha : attempt fuel (SchemePreparation.prepare [] source.requireDefinedInstances target) with
  | rejected reason | exhausted => rw [ha] at h; cases h
  | success candidate =>
      cases candidate with
      | none => rw [ha] at h; cases h
      | some r =>
          simp only [ha, RunResult.success.injEq] at h
          exact ⟨r, rfl, h.symm⟩

/-- Every returned anchor instance satisfies the original source bounds and
body, including every quantified-image guard under the original target. -/
theorem run_result {fuel : Nat} {source target : Scheme} {result : CompareSubstitution}
    (h : run fuel source target = .success result) :
    let p := SchemePreparation.prepare [] source target
    CompareInstantiatesUnder p.assumptions source result ∧
      result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  obtain ⟨r, hr, rfl⟩ := run_success h
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let result := ComparisonPreparation.reconstruct p r.action
  have hs := attempt_reconstruct hr
  have hi : CompareInstantiates source result :=
    ComparisonPreparation.reconstruct_instantiates [] source.requireDefinedInstances target r.action
  have hb : AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.instanceGuards) := by
    simpa only [Scheme.requireDefinedInstances, CompareSubstitution.bounds,
      List.map_append, AlgebraEntailsAll, List.mem_append, or_imp, forall_and] using hs.2.1
  obtain ⟨hw, hd⟩ := (CompareSubstitution.instance_guards_iff hi hs.1).mp hb.2
  have ha : p.assumptions = (SchemePreparation.prepare [] source target).assumptions := by
    simp only [p, SchemePreparation.prepare_assumptions, Scheme.requireDefinedInstances_subsumptionIndices]
  have ht : p.targetType = (SchemePreparation.prepare [] source target).targetType := by
    simp only [p, SchemePreparation.prepare, Scheme.requireDefinedInstances_subsumptionIndices]
  have hbody : AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := hs.2.2
  exact ⟨⟨hi, ha ▸ hw, ha ▸ hd⟩, ha ▸ hs.1, ha ▸ hb.1, by simpa only [ha, ht] using hbody⟩

theorem run_algebra_subsumesUnder {fuel : Nat} {source target : Scheme}
    {result : CompareSubstitution} (h : run fuel source target = .success result) :
    AlgebraSubsumesUnder [] source target := by
  obtain ⟨hi, hs, hb, ht⟩ := run_result h
  exact ⟨result, hi.domain, hs, hi.images, hi.body, hb, ht⟩

end ModalityInference.ComparisonDeclaredAnchors
