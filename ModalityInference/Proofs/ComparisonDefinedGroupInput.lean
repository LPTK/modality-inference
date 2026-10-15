import ModalityInference.Proofs.ComparisonDefinedGroupWitness
import ModalityInference.Proofs.ComparisonJointGroupWitness

/-! Actual opaque groups compile together while retaining the observations of
one admissible type and modality witness. -/

namespace ModalityInference.ComparisonChecker

open SchemePreparation ComparisonJointGroup

theorem OrdinaryGroupWitness.opaqueGuards {s : Setup} (w : OrdinaryGroupWitness s) :
    ComparisonReduction.OpaqueGuards (s.reduced w.reduced) :=
  (ComparisonReduction.prepare_opaqueGuards (w.reduction w.budget le_rfl)).prepend_modes _

theorem OrdinaryGroupWitness.mode_fixed {s : Setup} (w : OrdinaryGroupWitness s)
    (v : ModVar) (hv : ∀n∈s.modeIds, v ≠ .flex n) : w.core.mode v = .var v := by
  cases v with
  | rigid => rfl
  | flex n =>
    apply Substitution.mode_fresh ({modes := w.core.modes} : Substitution)
    intro hn
    obtain ⟨entry, he, hn⟩ := List.mem_map.mp hn
    exact hv entry.1 (w.modeDomain entry he) (congrArg ModVar.flex hn.symm)

theorem OrdinaryGroupWitness.strategy_uniform {s : Setup} (w : OrdinaryGroupWitness s) :
    ModalSynthesis.Uniform ModalSynthesis.locality (SchemeModeSynthesis.atoms s.modeIds)
      (SchemeModeSynthesis.strategy w.core.mode) :=
  SchemeModeSynthesis.strategy_uniform w.mode_fixed

theorem prepared_scalar_witness {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    (w : OrdinaryGroupWitness ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩) (inputs : Nat → Bool) :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    (BoolExpr.imp (boundsModeFormula s.work.assumptions)
      (boundsModeFormula (s.reduced w.reduced).modes)).eval
      (SchemeModeSynthesis.strategy w.core.mode inputs) = true := by
  rw [BoolExpr.eval_imp_true]
  apply ComparisonJointGroup.scalar_witness _ w.defined w.holds.modes inputs
  intro v hv
  apply w.domains.mode_fixed
  exact ((Bounds.bounded_iff _ _ _).mp
    (prepare_assumptions_bounded_first [] source.requireDefinedInstances target)).2 v hv

private theorem supports_combine {P : TypeVar → Prop} {Q : ModVar → Prop} {a : CompareTy}
    (ht : ComparisonInterpolation.Supports P (fun _ => True) a)
    (hm : ComparisonInterpolation.Supports (fun _ => True) Q a) :
    ComparisonInterpolation.Supports P Q a := by
  induction a <;> simp_all [ComparisonInterpolation.Supports]

theorem prepared_group_leaf_support {source target : Scheme}
    {shapeFuel : Nat} {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    (hshape : ComparisonShapeSolver.prepare shapeFuel
      (SchemePreparation.prepare [] source.requireDefinedInstances target) = .success (.solved shapes))
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (w : OrdinaryGroupWitness ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩)
    {g : ComparisonGroups.Group} (hg : g ∈ w.groups) :
    ∀i : Fin g.leaves.length, ComparisonInterpolation.Supports (· ∈ g.heads)
      (fun v => v.index < (SchemePreparation.prepare [] source.requireDefinedInstances target).firstMode)
      (w.core.type (.flex g.leaves[i])) := by
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let s : Setup := ⟨p, {}, shapes, known, false⟩
  have hb : BinderGuards s.original := prepare_binderGuards [] source target ht hm
  have hwork := s.work_of_binderGuards rfl hb
  have htemplates := s.templates_of_binderGuards rfl hb rfl
  have hs : ComparisonShapeSolver.prepare shapeFuel s.work = .success (.solved shapes) := by
    simpa only [hwork] using hshape
  have hfresh : ∀leaf∈s.templates.leaves, ∀v∈ComparisonGroups.inputHeads s.work,
      v ≠ .flex leaf.name := by
    rw [hwork, htemplates]
    exact ComparisonGroups.prepared_leaves_fresh [] source.requireDefinedInstances target shapes
  have hscope : ∀v∈s.work.assumptions.typeVars,
      ComparisonShapeSolver.sourceAllowed s.work v = false := by
    rw [hwork]
    intro v hv
    apply ComparisonShapeSolver.prepared_assumptions_fixed [] source.requireDefinedInstances target
    rwa [ComparisonShapeSolver.vars_pairs]
  have hfixed : ∀v∈g.heads, w.core.type v = .var v := by
    intro v hv
    apply w.domains.type_fixed
    have ho := (ComparisonGroups.collect_head_origin w.collection g hg v hv).1
    change v ∈ ComparisonGroups.inputHeads s.work at ho
    rw [hwork] at ho
    exact ComparisonGroups.prepared_inputHeads_bounded [] source.requireDefinedInstances target v ho
  have hφ := ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hs).1
  cases he : g.heads with
  | nil => exact False.elim (w.nonempty g hg he)
  | cons head rest =>
    have hh : head ∈ g.heads := by simp only [he, List.mem_cons_self]
    have hclass := collected_class_fixed hs w.collection hfresh hg hh
    intro i
    apply supports_combine (hm := w.fixedImages.1 _)
    apply opaque_head_support hφ (w.shaped.type _)
      (collected_image_shape hφ w.collection hfresh w.leafShape hg hclass hfixed
        (.inr ⟨g.leaves[i], List.getElem_mem _, rfl⟩))
    simpa only [he] using ComparisonGroups.collect_class_heads hs w.collection hscope hfresh hg hh

theorem prepared_scalar_complete {source target : Scheme}
    {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    (w : OrdinaryGroupWitness ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩) :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    ∃n scalar, (∀fuel≥n, CompactCNF.toCNF fuel true
      (.imp (boundsModeFormula s.work.assumptions) (boundsModeFormula (s.reduced w.reduced).modes)) =
        .success scalar) ∧
      ∀inputs, CNFHolds (SchemeModeSynthesis.strategy w.core.mode inputs) scalar := by
  obtain ⟨n, scalar, hc⟩ := CompactCNF.toCNF_complete _ true
  exact ⟨n, scalar, hc, fun inputs =>
    (CompactCNF.toCNF_correct (hc n le_rfl) _).mpr (prepared_scalar_witness w inputs)⟩

/-- The nominal polynomial and all four guarded observations use the same
substitution for every group. -/
def OrdinaryGroupWitness.GroupInput {s : Setup} (w : OrdinaryGroupWitness s)
    (g : ComparisonGroups.Group) (input : ComparisonJointGroup.Input) : Prop :=
  (nominalStore g w.core).Polynomial g.heads.length ∧
    ∀headWorld inputs,
      input.Holds g.heads.length
        (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy w.core.mode inputs))
        (witnessValues g w.core headWorld inputs)

theorem prepared_group_input {source target : Scheme}
    {shapeFuel fuel : Nat} {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    (hshape : ComparisonShapeSolver.prepare shapeFuel
      (SchemePreparation.prepare [] source.requireDefinedInstances target) = .success (.solved shapes))
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (w : OrdinaryGroupWitness ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩)
    {g : ComparisonGroups.Group} (hg : g ∈ w.groups) {input : ComparisonJointGroup.Input}
    (hinput : ComparisonJointGroup.prepare fuel
      (Setup.work ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
        {}, shapes, known, false⟩).assumptions
      ((Setup.reduced ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
        {}, shapes, known, false⟩) w.reduced).modes g = .success input) :
    w.GroupInput g input := by
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let s : Setup := ⟨p, {}, shapes, known, false⟩
  have hb : BinderGuards s.original := prepare_binderGuards [] source target ht hm
  have hwork := s.work_of_binderGuards rfl hb
  have htemplates := s.templates_of_binderGuards rfl hb rfl
  have hs : ComparisonShapeSolver.prepare shapeFuel s.work = .success (.solved shapes) := by
    simpa only [hwork] using hshape
  have hd : s.work.assumptions.TypeBoundsDefined := by
    rw [hwork]
    exact prepared_typeBoundsDefined source.requireDefinedInstances target
  have hfresh : ∀leaf∈s.templates.leaves, ∀v∈ComparisonGroups.inputHeads s.work,
      v ≠ .flex leaf.name := by
    rw [hwork, htemplates]
    exact ComparisonGroups.prepared_leaves_fresh [] source.requireDefinedInstances target shapes
  have hscope : ∀v∈s.work.assumptions.typeVars,
      ComparisonShapeSolver.sourceAllowed s.work v = false := by
    rw [hwork]
    intro v hv
    apply ComparisonShapeSolver.prepared_assumptions_fixed [] source.requireDefinedInstances target
    rwa [ComparisonShapeSolver.vars_pairs]
  have hmode : ∀v∈s.work.assumptions.modVars, w.core.mode v = .var v := by
    intro v hv
    apply w.domains.mode_fixed
    rw [hwork] at hv
    exact ((Bounds.bounded_iff _ _ _).mp
      (prepare_assumptions_bounded_first [] source.requireDefinedInstances target)).2 v hv
  have hfixed : ∀v∈g.heads, w.core.type v = .var v := by
    intro v hv
    apply w.domains.type_fixed
    have ho := (ComparisonGroups.collect_head_origin w.collection g hg v hv).1
    change v ∈ ComparisonGroups.inputHeads s.work at ho
    rw [hwork] at ho
    exact ComparisonGroups.prepared_inputHeads_bounded [] source.requireDefinedInstances target v ho
  cases he : g.heads with
  | nil => exact False.elim (w.nonempty g hg he)
  | cons head rest =>
    have hh : head ∈ g.heads := by simp only [he, List.mem_cons_self]
    exact ⟨nominalStore_polynomial hs w.collection hscope hfresh w.shaped w.leafShape hg hh hfixed,
      prepare_witness hs w.collection hfresh hd w.shaped w.defined hmode w.leafShape
        w.opaqueGuards w.holds.modes w.holds.inequalities hg hh hfixed hinput⟩

private theorem mapM_complete_with {α β : Type} (xs : List α)
    (f : Nat → α → RunResult β) (P : α → β → Prop)
    (h : ∀x∈xs, ∃n y, (∀fuel≥n, f fuel x = .success y) ∧ P x y) :
    ∃n ys, (∀fuel≥n, xs.mapM (f fuel) = .success ys) ∧ List.Forall₂ P xs ys := by
  induction xs with
  | nil => exact ⟨0, [], fun _ _ => rfl, .nil⟩
  | cons x xs ih =>
    obtain ⟨nx, y, hy, hp⟩ := h x List.mem_cons_self
    obtain ⟨ns, ys, hys, hps⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨max nx ns, y :: ys, ?_, .cons hp hps⟩
    intro fuel hf
    simp [List.mapM_cons, hy fuel (by omega), hys fuel (by omega), bind, pure, RunResult.bind]

/-- One budget compiles every actual collected group, including each group's
original assumptions and the retained source and reduction scalar guards. -/
theorem prepared_groups_complete {source target : Scheme}
    {shapeFuel : Nat} {shapes : ComparisonShapeSolver.Solved} {known : List ModExpr}
    (hshape : ComparisonShapeSolver.prepare shapeFuel
      (SchemePreparation.prepare [] source.requireDefinedInstances target) = .success (.solved shapes))
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (w : OrdinaryGroupWitness ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩) :
    let s : Setup := ⟨SchemePreparation.prepare [] source.requireDefinedInstances target,
      {}, shapes, known, false⟩
    ∃n inputs, (∀fuel≥n, w.groups.mapM
      (ComparisonJointGroup.prepare fuel s.work.assumptions (s.reduced w.reduced).modes) = .success inputs) ∧
      List.Forall₂ w.GroupInput w.groups inputs := by
  apply mapM_complete_with
  intro g hg
  obtain ⟨n, input, hi⟩ := ComparisonJointGroup.prepare_complete (w.covered g hg) _ _
  exact ⟨n, input, hi, prepared_group_input hshape ht hm w hg (hi n le_rfl)⟩

/-- An admissible scheme comparison supplies all compiled group observations
at the same eventual fuel as its shape, annotation, and structural preparation. -/
theorem algebra_joint_group_input {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds) (h : AlgebraSubsumesUnder [] source target) :
    let p := SchemePreparation.prepare [] source.requireDefinedInstances target
    ∃shapes known, ∃w : OrdinaryGroupWitness ⟨p, {}, shapes, known, false⟩,
      ∃inputs, List.Forall₂ w.GroupInput w.groups inputs ∧ ∃n, ∀fuel≥n,
        ComparisonShapeSolver.prepare fuel p = .success (.solved shapes) ∧
        ComparisonBody.knownTotal fuel (p.assumptions ++ p.sourceBounds.assumptions)
          (ComparisonAnnotations.obligationExpressions p) = .success known ∧
        ComparisonReduction.prepare fuel
          (Setup.work ⟨p, {}, shapes, known, false⟩)
          (Setup.templates ⟨p, {}, shapes, known, false⟩)
          (Setup.bare ⟨p, {}, shapes, known, false⟩) known false = .success w.reduced ∧
        w.groups.mapM (ComparisonJointGroup.prepare fuel
          (Setup.work ⟨p, {}, shapes, known, false⟩).assumptions
          ((Setup.reduced ⟨p, {}, shapes, known, false⟩) w.reduced).modes) = .success inputs := by
  obtain ⟨shapes, known, w, n, hp⟩ := algebra_ordinary_group_witness ht hm hR h
  obtain ⟨ng, inputs, hi, hw⟩ := prepared_groups_complete (hp n le_rfl).1 ht hm w
  refine ⟨shapes, known, w, inputs, hw, max n ng, ?_⟩
  intro fuel hf
  obtain ⟨hs, hk, hr⟩ := hp fuel (by omega)
  exact ⟨hs, hk, hr, hi fuel (by omega)⟩

end ModalityInference.ComparisonChecker
