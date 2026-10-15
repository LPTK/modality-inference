import ModalityInference.Proofs.ComparisonGroupOrigins
import ModalityInference.Proofs.ComparisonJointGroup

/-! Successful collection and complete opaque-head coverage of reduced goals. -/

namespace ModalityInference.ComparisonGroups

private instance : LawfulMonad RunResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

private theorem mapM_complete {α β : Type} {f : α → RunResult β}
    {xs : List α} {P : β → Prop} (h : ∀x∈xs, ∃y, f x = .success y ∧ P y) :
    ∃ys, xs.mapM f = .success ys ∧ ∀y∈ys, P y := by
  induction xs with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons x xs ih =>
    obtain ⟨y, hy, hp⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys, hps⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨y :: ys, ?_, by simpa only [List.forall_mem_cons] using And.intro hp hps⟩
    simp only [List.mapM_cons, hy, hys, bind, pure, RunResult.bind]

private theorem forIn_yields {α β : Type} {xs : List α}
    {f : α → β → RunResult (ForInStep β)} (state : β)
    (h : ∀x∈xs, f x state = .success (.yield state)) :
    forIn xs state f = .success state := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.forIn_cons, h x List.mem_cons_self, bind, pure, RunResult.bind] using
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

private theorem mapM_result {α β : Type} {f : α → RunResult β}
    {xs : List α} {result : RunResult (List β)} {P : β → Prop}
    (hr : xs.mapM f = result) (h : ∀x∈xs, ∃y, f x = .success y ∧ P y) :
    ∃ys, result = .success ys ∧ ∀y∈ys, P y := by
  obtain ⟨ys, he, hp⟩ := mapM_complete h
  exact ⟨ys, hr.symm.trans he, hp⟩

private theorem forIn_result {α β : Type} {xs : List α}
    {f : α → β → RunResult (ForInStep β)} {state : β} {result : RunResult β}
    (hr : forIn xs state f = result)
    (h : ∀x∈xs, f x state = .success (.yield state)) : result = .success state :=
  hr.symm.trans (forIn_yields state h)

theorem collect_complete {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State}
    (h : ∀goal∈reduced.inequalities, ∃pair : Inequality,
      inequality goal.1 goal.2 = some pair ∧ ∃c,
      shapeClass shapes templates pair.1.head = some c ∧
      shapeClass shapes templates pair.2.head = some c) :
    ∃groups, collect p shapes templates reduced = .success groups := by
  unfold collect
  simp only [bind, pure, RunResult.bind]
  split
  all_goals
    obtain ⟨goals, he, hc⟩ := mapM_result
      (P := fun pair : Inequality => ∃c,
        shapeClass shapes templates pair.1.head = some c ∧
        shapeClass shapes templates pair.2.head = some c)
      (by assumption) (by
        intro goal hm
        obtain ⟨pair, hp, hc⟩ := h goal hm
        exact ⟨pair, by simp only [hp], hc⟩)
    try contradiction
  cases he
  split
  all_goals
    have he := forIn_result (by assumption) (by
      intro pair hp
      obtain ⟨c, hl, hr⟩ := hc pair hp
      simp only [hl, hr, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte])
    try contradiction
  cases he
  exact ⟨_, rfl⟩

theorem collect_leaf_mem {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups) {g : Group} (hg : g ∈ groups)
    {leaf : ComparisonSkeleton.Leaf} (hl : leaf ∈ templates.leaves)
    (hc : leaf.shapeClass = g.shapeClass) : leaf.name ∈ g.leaves := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact List.mem_filterMap.mpr ⟨leaf, hl, by simp only [hc, beq_self_eq_true, ↓reduceIte]⟩
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List Group)) PUnit => r.fst = none) (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

theorem collect_group_nonempty {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups) {g : Group} (hg : g ∈ groups) :
    g.heads ≠ [] ∨ g.leaves ≠ [] ∨ g.goals ≠ [] := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    simp only [List.mem_dedup, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · obtain ⟨leaf, hl, rfl⟩ := List.mem_map.mp hc
      right; left
      apply List.ne_nil_of_mem (a := leaf.name)
      exact List.mem_filterMap.mpr ⟨leaf, hl, by simp⟩
    · obtain ⟨v, hv, hc⟩ := List.mem_filterMap.mp hc
      left
      apply List.ne_nil_of_mem (a := v)
      exact List.mem_filter.mpr ⟨hv, by simp only [hc, beq_self_eq_true]⟩
    · obtain ⟨pair, hp, hc⟩ := List.mem_filterMap.mp hc
      right; right
      apply List.ne_nil_of_mem (a := pair)
      exact List.mem_filter.mpr ⟨hp, by simp only [hc, beq_self_eq_true]⟩
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List Group)) PUnit => r.fst = none) (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

theorem collect_assumption_class {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups) {g : Group} (hg : g ∈ groups)
    {pair : Inequality} (hp : pair ∈ g.assumptions) :
    shapeClass shapes templates pair.1.head = some g.shapeClass := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact beq_iff_eq.mp (List.mem_filter.mp hp).2
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List Group)) PUnit => r.fst = none) (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

end ModalityInference.ComparisonGroups
