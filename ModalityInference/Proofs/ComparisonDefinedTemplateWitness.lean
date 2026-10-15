import ModalityInference.Proofs.ComparisonDefinedPreparation
import ModalityInference.Proofs.ComparisonShapeWitness
import ModalityInference.Proofs.ComparisonSkeletonFactor
import ModalityInference.Proofs.ComparisonPartialBoundary
import ModalityInference.Proofs.SchemeBounds

/-! Residual declared bounds and admissible prepared instances yield one shared,
defined assignment for the actual structural template coordinates. -/

namespace ModalityInference

theorem CompareSubstitution.ty_defined_of_mode_agreement {Δ : Bounds}
    {σ τ : CompareSubstitution} (ht : ∀ v, (τ.type v).DefinedUnder Δ)
    (hm : ∀ v, τ.mode v = σ.mode v) {t : Ty} (hd : (σ.ty t).DefinedUnder Δ) :
    (τ.ty t).DefinedUnder Δ := by
  induction t with
  | var v => exact ht v
  | unit | credit => exact hd
  | prod a b iha ihb =>
    exact CompareTy.definedUnder_prod_iff.mpr
      ⟨iha (CompareTy.definedUnder_prod_iff.mp hd).1,
        ihb (CompareTy.definedUnder_prod_iff.mp hd).2⟩
  | sum a b iha ihb =>
    exact CompareTy.definedUnder_sum_iff.mpr
      ⟨iha (CompareTy.definedUnder_sum_iff.mp hd).1,
        ihb (CompareTy.definedUnder_sum_iff.mp hd).2⟩
  | fn a b iha ihb =>
    exact CompareTy.definedUnder_fn_iff.mpr
      ⟨iha (CompareTy.definedUnder_fn_iff.mp hd).1,
        ihb (CompareTy.definedUnder_fn_iff.mp hd).2⟩
  | modal a m ih =>
    refine CompareTy.definedUnder_modal_iff.mpr
      ⟨ih (CompareTy.definedUnder_modal_iff.mp hd).1, ?_⟩
    change Entails Δ (.defined (m.subst τ.mode))
    rw [show τ.mode = σ.mode from funext hm]
    exact (CompareTy.definedUnder_modal_iff.mp hd).2

theorem Substitution.outer_variable_renaming (σ : Substitution)
    (ht : ∀ v, ∃ w, σ.type v = .var w) {a : Ty} {v : TypeVar}
    (ha : a.outer.1 = .var v) : ∃ w, (σ.ty a).outer.1 = .var w := by
  induction a with
  | var v =>
    obtain ⟨w, hw⟩ := ht v
    exact ⟨w, by simp only [Substitution.ty, TypeExpr.subst, hw, TypeExpr.outer]⟩
  | modal a m ih => exact ih ha
  | unit | credit | prod | sum | fn => cases ha

theorem Residual.renaming {cs : Bounds} (h : Residual cs) (σ : Substitution)
    (ht : ∀ v, ∃ w, σ.type v = .var w) : Residual (σ.bounds cs) := by
  apply List.forall_iff_forall_mem.mpr
  intro c hc
  change c ∈ cs.map σ.constraint at hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have hh := List.forall_iff_forall_mem.mp h d hd
  cases d with
  | sub a b =>
    obtain ⟨x,y,m,n,ha,hb⟩ := hh
    obtain ⟨x', hx⟩ := σ.outer_variable_renaming ht (congrArg Prod.fst ha)
    obtain ⟨y', hy⟩ := σ.outer_variable_renaming ht (congrArg Prod.fst hb)
    exact ⟨x', y', (σ.ty a).outer.2, (σ.ty b).outer.2,
      Prod.ext hx rfl, Prod.ext hy rfl⟩
  | mode | defined => trivial
  | equal | equiv => contradiction

theorem TypeExpr.wellFormedBounds_residual (a : Ty) : Residual a.wellFormedBounds := by
  induction a <;> simp_all [Residual, TypeExpr.wellFormedBounds, List.Forall]

theorem Residual.assumptions {cs : Bounds} (h : Residual cs) : Residual cs.assumptions := by
  apply List.forall_iff_forall_mem.mpr
  intro c hc
  obtain ⟨d,hd,hc⟩ := List.mem_flatMap.mp hc
  have hh := List.forall_iff_forall_mem.mp h d hd
  cases d with
  | sub a b =>
    simp only [Constraint.assumptions, List.mem_append, List.mem_singleton] at hc
    rcases hc with (rfl | hc) | hc
    · exact hh
    · exact List.forall_iff_forall_mem.mp a.wellFormedBounds_residual c hc
    · exact List.forall_iff_forall_mem.mp b.wellFormedBounds_residual c hc
  | mode | defined => cases List.mem_singleton.mp hc; trivial
  | equal | equiv => contradiction

theorem SchemePreparation.prepare_assumptions_residual {source target : Scheme}
    (hR : Residual target.bounds) : Residual (prepare [] source target).assumptions := by
  change Residual ([] ++ _)
  simpa only [List.nil_append] using
    (hR.renaming _ (target.freshSubstitution_type_variable _ _ true)).assumptions

namespace ComparisonSkeleton

open ComparisonSkeletonCoordinates

theorem forestExtension_wellFormedUnder {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    (names : List Nat) (nt nm : Nat) {σ : CompareSubstitution}
    (hσ : σ.WellFormedUnder Δ) :
    (forestExtension p solved trees names nt nm σ).WellFormedUnder Δ := by
  constructor
  · exact (CompareSubstitution.wellFormedUnder_of_images
      (σ := {types := forestTypes p solved trees names nt, modes := forestModes p solved trees names nm})
      (fun entry he => (forestTypes_guarded p solved trees names nt entry he).2)
      (forestModes_defined p solved trees names nm)).types
  · intro v
    cases v with
    | rigid n => exact hσ.modes (.rigid n)
    | flex n =>
      cases he : (forestModes p solved trees names nm).lookup n with
      | none =>
        simpa only [forestExtension, CompareSubstitution.mode, List.lookup_append, he,
          Option.none_or] using hσ.modes (.flex n)
      | some m =>
        obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
        have hm := forestModes_defined p solved trees names nm (n,m) (by simp [hh])
        simpa only [forestExtension, CompareSubstitution.mode, List.lookup_append, he,
          Option.some_or, Option.getD_some] using hm

theorem normalizedAction_wellFormedUnder {Δ : Bounds} (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (trees : CoordinateTrees Δ p solved)
    {σ : CompareSubstitution} (hσ : σ.WellFormedUnder Δ) :
    (normalizedAction p solved trees σ).WellFormedUnder Δ := by
  constructor
  · apply (CompareSubstitution.wellFormedUnder_of_images
      (σ := {types := (normalizedAction p solved trees σ).types}) ?_ (by simp)).types
    intro entry he
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
    exact ComparisonSkeletonCoordinates.Tree.reify_defined _
  · intro v
    simpa only [normalizedAction_mode] using hσ.modes v

/-- An admissible prepared comparison factors through the actual allocated
coordinates. All coordinates are defined under the original assumptions, and
the original shared modality assignment is retained. -/
theorem prepared_template_under {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (hshape : ComparisonShapeSolver.prepare fuel (SchemePreparation.prepare [] source target) =
      .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hR : Residual target.bounds) :
    let p := SchemePreparation.prepare [] source target
    ∃ trees : CoordinateTrees p.assumptions p solved,
      let core := preparedForest p solved trees σ
      core.WellShaped p.assumptions ∧ core.WellFormedUnder p.assumptions ∧
      AlgebraEntailsAll p.assumptions (core.bounds ((prepare p solved).substitution.bounds p.sourceBounds)) ∧
      (core.ty ((prepare p solved).substitution.ty p.sourceType)).DefinedUnder p.assumptions ∧
      AlgebraSubtype p.assumptions (core.ty ((prepare p solved).substitution.ty p.sourceType)) (.ofTy p.targetType) ∧
      (∀ v, v.index < p.nextMode → core.mode v = σ.mode v) ∧
      (∀ v, v.index < p.nextType → core.type v = .var v) := by
  let p := SchemePreparation.prepare [] source target
  have hr := SchemePreparation.prepare_assumptions_residual (source := source) hR
  have hd : (CompareTy.ofTy p.targetType).DefinedUnder p.assumptions :=
    by simpa only [CompareTy.definedUnder_ofTy] using
      ComparisonPartialBoundary.prepared_public_defined_of_above source target hw.2.2 hw.1.2.2.2
  obtain ⟨trees, hs, _, hb, ht⟩ := prepared_template_factor hshape hw.1 hr hw.2.2 hd
  have hcore := forestExtension_wellFormedUnder p solved trees
    (List.range' p.firstType (p.nextType - p.firstType)) p.nextType p.nextMode hw.2.1
  refine ⟨trees, hs, hcore, hb, ?_, ht, ?_, ?_⟩
  · rw [preparedForest_ty p solved trees σ p.sourceType
      (SchemePreparation.prepare_sourceType_bounded [] source target)]
    exact CompareSubstitution.ty_defined_of_mode_agreement
      (normalizedAction_wellFormedUnder p solved trees hw.2.1).types
      (normalizedAction_mode p solved trees σ) hw.2.2
  · exact fun v hv => forestExtension_mode p solved trees _ _ _ σ v hv
  · exact fun v hv => forestExtension_type_fixed p solved trees _ _ _ σ v hv

/-- Admissible source instances over residual target bounds eventually reach
an actual solved shape and one shared, defined assignment for its template
coordinates. No model of the assumptions is required. -/
theorem algebra_defined_template_complete {source target : Scheme}
    (hR : Residual target.bounds) (h : AlgebraSubsumesUnder [] source target) :
    let p := SchemePreparation.prepare [] source target
    ∃ n, ∀ fuel ≥ n, ∃ solved σ,
      ComparisonShapeSolver.prepare fuel p = .success (.solved solved) ∧
      ComparisonPreparation.PreparedWitnessUnder p σ ∧
      ∃ trees : CoordinateTrees p.assumptions p solved,
        let core := preparedForest p solved trees σ
        core.WellShaped p.assumptions ∧ core.WellFormedUnder p.assumptions ∧
        AlgebraEntailsAll p.assumptions (core.bounds ((prepare p solved).substitution.bounds p.sourceBounds)) ∧
        (core.ty ((prepare p solved).substitution.ty p.sourceType)).DefinedUnder p.assumptions ∧
        AlgebraSubtype p.assumptions (core.ty ((prepare p solved).substitution.ty p.sourceType)) (.ofTy p.targetType) ∧
        (∀ v, v.index < p.nextMode → core.mode v = σ.mode v) ∧
        (∀ v, v.index < p.nextType → core.type v = .var v) := by
  obtain ⟨σ, hw⟩ := ComparisonPreparation.prepare_algebra_under_complete h
  obtain ⟨n, solved, hs⟩ := prepared_witness_shape_complete_residual hw.1
    (SchemePreparation.prepare_assumptions_residual (source := source) hR)
  refine ⟨n, fun fuel hf => ⟨solved, σ, hs fuel hf, hw, ?_⟩⟩
  exact prepared_template_under (hs fuel hf) hw hR

end ComparisonSkeleton
end ModalityInference
