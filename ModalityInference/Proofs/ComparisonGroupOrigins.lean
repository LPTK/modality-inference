import ModalityInference.Proofs.ComparisonOpaqueGrammar
import ModalityInference.Proofs.ComparisonDefinedReductionWitness

/-! Input provenance of the opaque classes retained by comparison templates. -/

namespace ModalityInference.ComparisonShapeSolver

theorem subst_eq_self_vars {s : ComparisonShape} {ρ : TypeVar → ComparisonShape}
    (h : s.subst ρ = s) : ∀v∈s.vars, ρ v = .var v := by
  induction s with
  | var v => simpa only [ComparisonShape.subst, ComparisonShape.vars,
      List.mem_singleton, forall_eq] using h
  | unit | credit => simp [ComparisonShape.vars]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [ComparisonShape.subst, ComparisonShape.prod.injEq,
      ComparisonShape.sum.injEq, ComparisonShape.fn.injEq] at h
    intro v hv
    exact (List.mem_append.mp hv).elim (iha h.1 v) (ihb h.2 v)

end ModalityInference.ComparisonShapeSolver

namespace ModalityInference.ComparisonGroups

def inputHeads (p : SchemePreparation.Prepared) : List TypeVar :=
  p.assumptions.typeVariables ++ p.targetType.typeVariables ++
    p.sourceType.typeVariables ++ p.sourceBounds.typeVariables

open ComparisonShapeSolver

theorem fixed_image_origin {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    {v w : TypeVar} (hv : v ∈ inputHeads p) (hw : w ∈ (shapes.fixedShapes v).vars) :
    w ∈ inputHeads p ∧ shapes.fixedShapes w = .var w := by
  have hf := (prepare_solved_iff.mp h).1
  have hid := unify_factor hf (unify_sound hf) v
  refine ⟨?_, subst_eq_self_vars hid w hw⟩
  obtain ⟨hfix, hsupport⟩ := unify_support hf p.assumptions.typeVars (by rw [vars_pairs])
  by_cases hm : v ∈ p.assumptions.typeVars
  · have hw := hsupport v hm (List.mem_toFinset.mpr hw)
    simp only [inputHeads, List.mem_append, Bounds.mem_typeVariables]
    exact Or.inl (Or.inl (Or.inl hw))
  · change w ∈ (action shapes.fixed v).vars at hw
    rw [hfix v hm] at hw
    have he : w = v := by simpa only [ComparisonShape.vars, List.mem_singleton] using hw
    exact he ▸ hv

theorem sourcePairs_origin {p : SchemePreparation.Prepared} {v : TypeVar}
    (hv : v ∈ Measure.vars (sourcePairs p)) : v ∈ inputHeads p := by
  obtain ⟨a, b, hp, hv⟩ := (Measure.mem_vars _ _).mp hv
  rcases List.mem_append.mp hp with hp | hp
  · have hm := (Measure.mem_vars _ _).mpr ⟨a, b, hp, hv⟩
    rw [vars_pairs] at hm
    simp only [inputHeads, List.mem_append, Bounds.mem_typeVariables]
    exact Or.inr hm
  · simp only [List.mem_singleton, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp only [inputHeads, List.mem_append, TypeExpr.mem_typeVariables]
    exact hv.elim (fun hv => .inl (.inr ((mem_vars_ofTy _ _).mp hv)))
      (fun hv => .inl (.inl (.inr ((mem_vars_ofTy _ _).mp hv))))

theorem source_normal_vars_origin {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    {w : TypeVar}
    (hw : w ∈ Measure.vars (mapPairs shapes.fixedShapes (sourcePairs p))) :
    w ∈ inputHeads p ∧ shapes.fixedShapes w = .var w := by
  obtain ⟨a, b, hp, hw⟩ := (Measure.mem_vars _ _).mp hw
  obtain ⟨⟨x, y⟩, hxy, he⟩ := List.mem_map.mp hp
  cases he
  rcases hw with hw | hw
  all_goals
    obtain ⟨v, hv, hw⟩ := (mem_vars_subst _ _ _).mp hw
    apply fixed_image_origin h ?_ hw
    apply sourcePairs_origin
    apply (Measure.mem_vars _ _).mpr
  · exact ⟨x, y, hxy, .inl hv⟩
  · exact ⟨x, y, hxy, .inr hv⟩

theorem resolved_fixed_origin {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (hscope : ∀w∈Measure.vars (ComparisonShape.pairs p.assumptions),
      sourceAllowed p w = false) {v w : TypeVar}
    (hv : sourceAllowed p v = true) (hw : w ∈ (shapes.resolveAll v).vars)
    (hfixed : sourceAllowed p w = false) :
    w ∈ inputHeads p ∧ shapes.fixedShapes w = .var w := by
  rw [prepare_resolve_source h hscope hv] at hw
  let names := Measure.vars (mapPairs shapes.fixedShapes (sourcePairs p))
  obtain ⟨hfix, hsupport⟩ := unify_support (prepare_solved_iff.mp h).2 names Finset.Subset.rfl
  by_cases hm : v ∈ names
  · exact source_normal_vars_origin h (hsupport v hm (List.mem_toFinset.mpr hw))
  · rw [hfix v hm] at hw
    have he : w = v := by simpa only [ComparisonShape.vars, List.mem_singleton] using hw
    exact False.elim (Bool.noConfusion (hv.symm.trans (he ▸ hfixed)))

end ModalityInference.ComparisonGroups

namespace ModalityInference.ComparisonSkeleton

theorem leaves_class_origin (p : SchemePreparation.Prepared) (shape : ComparisonShape)
    (nt : Nat) {leaf : Leaf} (h : leaf ∈ leaves p shape nt) :
    leaf.shapeClass ∈ shape.vars ∧ ComparisonShapeSolver.sourceAllowed p leaf.shapeClass = false := by
  induction shape generalizing nt with
  | var v =>
    simp only [leaves] at h
    split at h
    · simp at h
    · simp only [List.mem_singleton] at h
      subst leaf
      exact ⟨List.mem_singleton_self _, Bool.eq_false_iff.mpr (by assumption)⟩
  | unit | credit => simp [leaves] at h
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    rcases List.mem_append.mp h with h | h
    · exact ⟨List.mem_append_left _ (iha _ h).1, (iha _ h).2⟩
    · exact ⟨List.mem_append_right _ (ihb _ h).1, (ihb _ h).2⟩

theorem allocate_class_origin {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (hscope : ∀w∈ComparisonShapeSolver.Measure.vars (ComparisonShape.pairs p.assumptions),
      ComparisonShapeSolver.sourceAllowed p w = false)
    (names : List Nat) (hnames : ∀n∈names, ComparisonShapeSolver.sourceAllowed p (.flex n) = true)
    (nt nm : Nat) {leaf : Leaf} (hl : leaf ∈ (allocate p shapes names nt nm).leaves) :
    leaf.shapeClass ∈ ComparisonGroups.inputHeads p ∧
      ComparisonShapeSolver.sourceAllowed p leaf.shapeClass = false ∧
      shapes.fixedShapes leaf.shapeClass = .var leaf.shapeClass := by
  induction names generalizing nt nm with
  | nil => simp [allocate] at hl
  | cons n ns ih =>
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨hm, hf⟩ := leaves_class_origin p _ _ hl
      obtain ⟨hi, he⟩ := ComparisonGroups.resolved_fixed_origin h hscope
        (hnames n List.mem_cons_self) hm hf
      exact ⟨hi, hf, he⟩
    · exact ih (fun n hn => hnames n (List.mem_cons_of_mem _ hn)) _ _ hl

theorem prepare_class_origin {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved}
    (h : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (hscope : ∀w∈ComparisonShapeSolver.Measure.vars (ComparisonShape.pairs p.assumptions),
      ComparisonShapeSolver.sourceAllowed p w = false)
    {leaf : Leaf} (hl : leaf ∈ (prepare p shapes).leaves) :
    leaf.shapeClass ∈ ComparisonGroups.inputHeads p ∧
      ComparisonShapeSolver.sourceAllowed p leaf.shapeClass = false ∧
      shapes.fixedShapes leaf.shapeClass = .var leaf.shapeClass := by
  apply allocate_class_origin h hscope _ ?_ _ _ hl
  intro n hn
  have hn := List.mem_range'_1.mp hn
  simp only [ComparisonShapeSolver.sourceAllowed, Bool.and_eq_true, decide_eq_true_eq]
  omega

end ModalityInference.ComparisonSkeleton
