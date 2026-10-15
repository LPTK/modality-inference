import ModalityInference.Proofs.ComparisonDefinedPrepasses
import ModalityInference.Proofs.ComparisonDefinedTemplateWitness

/-! Explicit binder guards identify the ordinary propagation preparations with
the complete structural template allocation of the original prepared input. -/

namespace ModalityInference.ComparisonChecker

open SchemePreparation

private theorem empty_ty (a : Ty) : ({} : Substitution).ty a = a :=
  (a.subst_congr (fun v _ => by cases v <;> rfl)
    (fun v _ => by cases v <;> rfl)).trans a.subst_id

theorem Setup.input_empty (s : Setup) (hb : s.before = {}) :
    s.input = s.original := by
  simp only [Setup.input, hb, ComparisonExactContext.rewrite,
    empty_ty, Substitution.empty_bounds]

theorem Setup.absorbed_of_binderGuards (s : Setup) (hb : s.before = {})
    (hg : BinderGuards s.original) : s.absorbed = s.original := by
  simp only [Setup.absorbed, Setup.absorption, s.input_empty hb, absorption_body_eq hg]

theorem Setup.annotations_substitution_of_binderGuards (s : Setup) (hb : s.before = {})
    (hg : BinderGuards s.original) : s.annotations.substitution = {} := by
  simp only [Setup.annotations, ComparisonPartialModes.Result.substitution,
    s.absorbed_of_binderGuards hb hg, (annotations_trivial hg s.total).1]

theorem Setup.work_of_binderGuards (s : Setup) (hb : s.before = {})
    (hg : BinderGuards s.original) : s.work = s.original := by
  simp only [Setup.work, s.annotations_substitution_of_binderGuards hb hg,
    s.absorbed_of_binderGuards hb hg, empty_ty]

theorem Setup.bare_of_binderGuards (s : Setup) (hb : s.before = {})
    (hg : BinderGuards s.original) (hshared : s.shared = false) : s.bare = [] := by
  simp only [Setup.bare, hshared, Bool.false_eq_true, ↓reduceIte,
    s.work_of_binderGuards hb hg, bareEligible_nil hg, List.filter_nil]

theorem Setup.names_of_binderGuards (s : Setup) (hb : s.before = {})
    (hg : BinderGuards s.original) (hshared : s.shared = false) :
    s.names = List.range' s.original.firstType (s.original.nextType - s.original.firstType) := by
  simp only [Setup.names, hb, s.bare_of_binderGuards hb hg hshared, List.map_nil,
    List.contains_nil, Bool.not_false, Bool.true_and, List.filter_true]

theorem Setup.annotations_nextMode_of_binderGuards (s : Setup) (hb : s.before = {})
    (hg : BinderGuards s.original) : s.annotations.nextMode = s.original.nextMode := by
  simpa only [Setup.annotations, s.absorbed_of_binderGuards hb hg] using
    (annotations_trivial hg s.total).2.2

theorem Setup.templates_of_binderGuards (s : Setup) (hb : s.before = {})
    (hg : BinderGuards s.original) (hshared : s.shared = false) :
    s.templates = ComparisonSkeleton.prepare s.original s.shapes := by
  simp only [Setup.templates, s.work_of_binderGuards hb hg,
    s.names_of_binderGuards hb hg hshared, s.annotations_nextMode_of_binderGuards hb hg,
    ComparisonSkeleton.prepare]

theorem Setup.modeIds_of_binderGuards (s : Setup) (hb : s.before = {})
    (hg : BinderGuards s.original) :
    s.modeIds = List.range' s.original.firstMode (s.templates.nextMode - s.original.firstMode) := by
  simp only [Setup.modeIds, hb, Setup.absorption, s.input_empty hb,
    ComparisonAbsorption.Result.modes, absorption_owners_nil hg,
    ComparisonAbsorption.modes, Setup.annotations, s.absorbed_of_binderGuards hb hg,
    (annotations_trivial hg s.total).1, List.map_nil, List.dedup_nil,
    List.nil_append, List.contains_nil, Bool.not_false, List.filter_true]

/-- The actual ordinary propagation input has one defined coordinate witness,
retaining the original shared modality assignment. -/
theorem prepared_ordinary_template_under {source target : Scheme}
    {fuel : Nat} {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (hshape : ComparisonShapeSolver.prepare fuel
      (prepare [] source.requireDefinedInstances target) = .success (.solved solved))
    (hw : ComparisonPreparation.PreparedWitnessUnder
      (prepare [] source.requireDefinedInstances target) σ)
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds) (known : List ModExpr) :
    let p := prepare [] source.requireDefinedInstances target
    let s : Setup := ⟨p, {}, solved, known, false⟩
    ∃ trees : ComparisonSkeleton.CoordinateTrees p.assumptions p solved,
      let core := ComparisonSkeleton.preparedForest p solved trees σ
      core.WellShaped s.work.assumptions ∧ core.WellFormedUnder s.work.assumptions ∧
      AlgebraEntailsAll s.work.assumptions
        (core.bounds (s.templates.substitution.bounds s.work.sourceBounds)) ∧
      (core.ty (s.templates.substitution.ty s.work.sourceType)).DefinedUnder s.work.assumptions ∧
      AlgebraSubtype s.work.assumptions
        (core.ty (s.templates.substitution.ty s.work.sourceType)) (.ofTy s.work.targetType) ∧
      (∀ v, v.index < p.nextMode → core.mode v = σ.mode v) ∧
      (∀ v, v.index < p.nextType → core.type v = .var v) := by
  let p := prepare [] source.requireDefinedInstances target
  let s : Setup := ⟨p, {}, solved, known, false⟩
  have hg : BinderGuards s.original := prepare_binderGuards [] source target ht hm
  have hwork := s.work_of_binderGuards rfl hg
  have htemplates := s.templates_of_binderGuards rfl hg rfl
  dsimp only [s, p] at hwork htemplates
  simpa only [hwork, htemplates] using
    ComparisonSkeleton.prepared_template_under hshape hw hR

end ModalityInference.ComparisonChecker
