import ModalityInference.Proofs.ComparisonWitnessProperties

/-! The executable group partition preserves the opaque obligations and the
definedness guards needed to reconstruct their original endpoints. -/
namespace ModalityInference.ComparisonGroups

private instance : LawfulMonad RunResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

private theorem mapM_forall₂ {α β : Type} {f : α → RunResult β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .success ys) :
    List.Forall₂ (fun x y => f x = .success y) xs ys := by
  induction xs generalizing ys with
  | nil => cases h; exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hx : f x <;> simp only [hx] at h <;> try contradiction
    next y =>
      cases hxs : xs.mapM f <;> simp only [hxs] at h <;> try contradiction
      next rest => cases h; exact .cons hx (ih hxs)

private theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | cons hr h ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨y, hy, hr⟩ := ih hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hr⟩

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => simp at hy
  | cons hr h ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hr⟩ := ih hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

private theorem forIn_all {α β : Type} {xs : List α} {initial final : β}
    {f : α → β → RunResult (ForInStep β)} (P : α → Prop)
    (h : forIn xs initial f = .success final)
    (hstep : ∀ a ∈ xs, ∀ before after, f a before = .success after →
      (∃ result, after = .yield result) ∧ P a) : ∀ a ∈ xs, P a := by
  induction xs generalizing initial with
  | nil => simp
  | cons a xs ih =>
    simp only [List.forIn_cons, pure] at h
    cases hf : f a initial <;> simp only [hf] at h <;> try contradiction
    next result =>
      obtain ⟨⟨next, rfl⟩, ha⟩ := hstep a List.mem_cons_self initial result hf
      simpa only [List.forall_mem_cons] using
        And.intro ha (ih h (fun a ha => hstep a (List.mem_cons_of_mem _ ha)))

theorem atom_spec {t : Ty} {a : Atom} (h : atom t = some a) :
    t.outer = (.var a.head, a.mode) := by
  unfold atom at h
  split at h <;> try contradiction
  next v m he => cases Option.some.inj h; exact he

theorem atom_mode_defined {Δ : Bounds} {t : Ty} {a : Atom}
    (h : atom t = some a) (ht : t.DefinedUnder Δ) : Entails Δ (.defined a.mode) := by
  have hm := (TypeExpr.definedUnder_modal.mp ((t.outer_definedUnder Δ).mpr ht)).2
  simpa only [atom_spec h] using hm

theorem inequality_spec {left right : Ty} {pair : Inequality}
    (h : inequality left right = some pair) :
    atom left = some pair.1 ∧ atom right = some pair.2 := by
  unfold inequality at h
  cases hl : atom left <;> simp only [hl, bind, pure, Option.bind] at h <;> try contradiction
  cases hr : atom right <;> simp only [hr] at h <;> try contradiction
  cases Option.some.inj h
  exact ⟨rfl, rfl⟩

def Atom.interpret (σ : CompareSubstitution) (a : Atom) : CompareTy :=
  .modal (σ.type a.head) (a.mode.subst σ.mode)

theorem atom_algebra {Δ : Bounds} {σ : CompareSubstitution} {t : Ty} {a : Atom}
    (hσ : σ.WellShaped Δ) (h : atom t = some a)
    (hm : Entails Δ (.defined (a.mode.subst σ.mode))) :
    AlgebraSubtype Δ (σ.ty t) (a.interpret σ) ∧
      AlgebraSubtype Δ (a.interpret σ) (σ.ty t) := by
  have he := atom_spec h
  have hh := ComparisonReduction.outer_algebra hσ t
    (by simpa only [he] using Submode.refl hm)
  simpa only [he, Atom.interpret, CompareSubstitution.ty, CompareTy.ofTy,
    CompareTy.subst] using hh

theorem inequality_algebra_iff {Δ : Bounds} {σ : CompareSubstitution}
    {left right : Ty} {pair : Inequality}
    (hσ : σ.WellShaped Δ) (h : inequality left right = some pair)
    (hl : Entails Δ (.defined (pair.1.mode.subst σ.mode)))
    (hr : Entails Δ (.defined (pair.2.mode.subst σ.mode))) :
    AlgebraSubtype Δ (σ.ty left) (σ.ty right) ↔
      AlgebraSubtype Δ (pair.1.interpret σ) (pair.2.interpret σ) := by
  obtain ⟨ha, hb⟩ := inequality_spec h
  have ha := atom_algebra hσ ha hl
  have hb := atom_algebra hσ hb hr
  exact ⟨fun hs => ha.2.trans (hs.trans hb.1), fun hs => ha.1.trans (hs.trans hb.2)⟩

theorem collect_assumption_origin {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups) :
    ∀ g ∈ groups, ∀ pair ∈ g.assumptions, ∃ left right,
      Constraint.sub left right ∈ p.assumptions ∧ inequality left right = some pair := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    intro g hg pair hp
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    obtain ⟨hp, _⟩ := List.mem_filter.mp hp
    obtain ⟨constraint, hc, he⟩ := List.mem_filterMap.mp hp
    cases constraint <;> try contradiction
    next left right => exact ⟨left, right, hc, he⟩
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List Group)) PUnit => r.fst = none) (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

theorem collect_goal_coverage {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups) :
    ∀ goal ∈ reduced.inequalities, ∃ g ∈ groups, ∃ pair ∈ g.goals,
      inequality goal.1 goal.2 = some pair := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  split at h
  · next goals hgoals =>
    split at h
    · next final hloop =>
      have hnone := RunResult.forIn_preserves
        (fun r : MProd (Option (List Group)) PUnit => r.fst = none) hloop rfl (by
          intro pair hp before after hb hs
          repeat' first
            | contradiction
            | (cases hs; rfl)
            | (split at hs <;> try simp only at hs))
      have hclasses := forIn_all
        (fun pair : Inequality => ∃ c, shapeClass shapes templates pair.1.head = some c)
        hloop (by
          intro pair hp before after hs
          repeat' first
            | contradiction
            | (split at hs <;> try simp only at hs)
          cases hs
          exact ⟨⟨_, rfl⟩, _, by assumption⟩)
      rw [hnone] at h
      cases h
      intro goal hg
      obtain ⟨pair, hp, he⟩ := forall₂_mem_left (mapM_forall₂ hgoals) hg
      have hi : inequality goal.1 goal.2 = some pair := by
        split at he <;> try contradiction
        next pair' hpair => cases he; exact hpair
      obtain ⟨c, hc⟩ := hclasses pair hp
      refine ⟨_, List.mem_map.mpr ⟨c, ?_, rfl⟩, pair, ?_, hi⟩
      · exact List.mem_dedup.mpr (List.mem_append_right _
          (List.mem_filterMap.mpr ⟨pair, hp, hc⟩))
      · exact List.mem_filter.mpr ⟨hp, by simp only [hc, beq_self_eq_true]⟩
    · contradiction
    · contradiction
  · contradiction
  · contradiction

theorem collect_goal_origin {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups) :
    ∀ g ∈ groups, ∀ pair ∈ g.goals, ∃ goal ∈ reduced.inequalities,
      inequality goal.1 goal.2 = some pair ∧
      shapeClass shapes templates pair.1.head = some g.shapeClass ∧
      shapeClass shapes templates pair.2.head = some g.shapeClass := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  split at h
  · next goals hgoals =>
    split at h
    · next final hloop =>
      have hnone := RunResult.forIn_preserves
        (fun r : MProd (Option (List Group)) PUnit => r.fst = none) hloop rfl (by
          intro pair hp before after hb hs
          repeat' first
            | contradiction
            | (cases hs; rfl)
            | (split at hs <;> try simp only at hs))
      have hclasses := forIn_all
        (fun pair : Inequality => ∃ c, shapeClass shapes templates pair.1.head = some c ∧
          shapeClass shapes templates pair.2.head = some c) hloop (by
          intro pair hp before after hs
          split at hs
          · next x y hl hr =>
            split at hs
            · contradiction
            · next hxy =>
              cases hs
              have he : x = y := by simpa using hxy
              exact ⟨⟨_, rfl⟩, x, hl, he ▸ hr⟩
          · contradiction)
      rw [hnone] at h
      cases h
      intro g hg pair hp
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hp, hclass⟩ := List.mem_filter.mp hp
      have hclass := beq_iff_eq.mp hclass
      obtain ⟨goal, hgoal, he⟩ := forall₂_mem_right (mapM_forall₂ hgoals) hp
      have hi : inequality goal.1 goal.2 = some pair := by
        split at he <;> try contradiction
        next pair' hpair => cases he; exact hpair
      obtain ⟨other, hl, hr⟩ := hclasses pair hp
      have he := Option.some.inj (hl.symm.trans hclass)
      exact ⟨goal, hgoal, hi, hclass, he ▸ hr⟩
    · contradiction
    · contradiction
  · contradiction
  · contradiction

theorem collect_assumption_modes {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (hd : p.assumptions.TypeBoundsDefined)
    (h : collect p shapes templates reduced = .success groups) :
    ∀ g ∈ groups, ∀ pair ∈ g.assumptions,
      Entails p.assumptions (.defined pair.1.mode) ∧
      Entails p.assumptions (.defined pair.2.mode) := by
  intro g hg pair hp
  obtain ⟨left, right, hc, hi⟩ := collect_assumption_origin h g hg pair hp
  obtain ⟨hl, hr⟩ := inequality_spec hi
  exact ⟨atom_mode_defined hl (hd left right hc).1,
    atom_mode_defined hr (hd left right hc).2⟩

theorem collect_group_eq_of_shape {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups)
    {a b : Group} (ha : a ∈ groups) (hb : b ∈ groups) (he : a.shapeClass = b.shapeClass) : a = b := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hb
    change c = d at he
    subst d
    rfl
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List Group)) PUnit => r.fst = none) (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

private theorem nodup_filterMap_of_map {α β : Type} (xs : List α) (f : α → β) (p : α → Bool)
    (h : (xs.map f).Nodup) : (xs.filterMap (fun x => if p x then some (f x) else none)).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases hx : p x = true
    · simp only [List.filterMap_cons, hx, if_true, List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hm
      obtain ⟨y, hy, he⟩ := List.mem_filterMap.mp hm
      split at he <;> try contradiction
      exact h.1 (List.mem_map.mpr ⟨y, hy, Option.some.inj he⟩)
    · simpa only [List.filterMap_cons, hx, if_false] using ih h.2

theorem collect_leaves_nodup {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups)
    (hn : (templates.leaves.map (·.name)).Nodup) : ∀ g ∈ groups, g.leaves.Nodup := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    intro g hg
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hg
    exact nodup_filterMap_of_map templates.leaves (·.name) (fun leaf => leaf.shapeClass == c) hn
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List Group)) PUnit => r.fst = none) (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

theorem collect_leaf_shared {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups)
    (hn : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b)
    {a b : Group} (ha : a ∈ groups) (hb : b ∈ groups) {n : Nat}
    (hna : n ∈ a.leaves) (hnb : n ∈ b.leaves) : a = b := by
  obtain ⟨x, hx, hxn, hxc⟩ := collect_leaf_origin h a ha n hna
  obtain ⟨y, hy, hyn, hyc⟩ := collect_leaf_origin h b hb n hnb
  have he := hn x hx y hy (hxn.trans hyn.symm)
  apply collect_group_eq_of_shape h ha hb
  exact hxc.symm.trans ((congrArg ComparisonSkeleton.Leaf.shapeClass he).trans hyc)

end ModalityInference.ComparisonGroups

namespace ModalityInference.ComparisonReduction

def OpaqueGuards (s : State) : Prop :=
  ∀ pair ∈ s.inequalities,
    Constraint.defined pair.1.outer.2 ∈ s.modes ∧
      Constraint.defined pair.2.outer.2 ∈ s.modes

theorem OpaqueGuards.prepend_modes {s : State} (h : OpaqueGuards s) (extra : Bounds) :
    OpaqueGuards { s with modes := extra ++ s.modes } :=
  fun pair hp => ⟨List.mem_append_right _ (h pair hp).1,
    List.mem_append_right _ (h pair hp).2⟩

theorem step_modes_mono {s next : State} (h : step s = .success next) :
    ∀ c ∈ s.modes, c ∈ next.modes := by
  unfold step at h
  repeat' first
    | contradiction
    | (cases h; intro c hc; first | exact hc | (simp only [List.mem_cons]; tauto))
    | (split at h <;> try simp only at h)

theorem step_opaqueGuards {s next : State} (h : step s = .success next)
    (hs : OpaqueGuards s) : OpaqueGuards next := by
  have hm := step_modes_mono h
  unfold step at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  all_goals cases h
  all_goals intro pair hp
  all_goals first
    | exact ⟨hm _ (hs pair hp).1, hm _ (hs pair hp).2⟩
    | (rcases List.mem_cons.mp hp with rfl | hp
       · exact ⟨by simp, by simp⟩
       · exact ⟨hm _ (hs pair hp).1, hm _ (hs pair hp).2⟩)

theorem run_opaqueGuards {fuel : Nat} {s next : State}
    (h : run fuel s = .success next) (hs : OpaqueGuards s) : OpaqueGuards next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases he : step s <;> simp only [he] at h <;> try contradiction
      next middle => exact ih h (step_opaqueGuards he hs)

theorem prepare_opaqueGuards {fuel : Nat} {p : SchemePreparation.Prepared}
    {templates : ComparisonSkeleton.Templates} {bare : List Nat} {known : List ModExpr}
    {shared : Bool} {result : State}
    (h : prepare fuel p templates bare known shared = .success result) : OpaqueGuards result := by
  unfold prepare at h
  simp only [bind, RunResult.bind] at h
  split at h
  · next reduced hr =>
    apply run_opaqueGuards h
    change OpaqueGuards reduced
    exact run_opaqueGuards hr (by simp [OpaqueGuards, initial])
  · contradiction
  · contradiction

end ModalityInference.ComparisonReduction

namespace ModalityInference.ComparisonGroups

theorem collect_goal_guards {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups)
    (hguards : ComparisonReduction.OpaqueGuards reduced) :
    ∀ g ∈ groups, ∀ pair ∈ g.goals,
      Constraint.defined pair.1.mode ∈ reduced.modes ∧
      Constraint.defined pair.2.mode ∈ reduced.modes := by
  intro g hg pair hp
  obtain ⟨goal, hgoal, hi, _⟩ := collect_goal_origin h g hg pair hp
  obtain ⟨hl, hr⟩ := inequality_spec hi
  simpa only [atom_spec hl, atom_spec hr] using hguards goal hgoal

theorem collect_reconstruct {Δ : Bounds} {σ : CompareSubstitution}
    {p : SchemePreparation.Prepared} {shapes : ComparisonShapeSolver.Solved}
    {templates : ComparisonSkeleton.Templates} {reduced : ComparisonReduction.State}
    {groups : List Group} (hσ : σ.WellShaped Δ)
    (h : collect p shapes templates reduced = .success groups)
    (hguards : ComparisonReduction.OpaqueGuards reduced)
    (hmodes : AlgebraEntailsAll Δ (σ.bounds reduced.modes))
    (hgoals : ∀ g ∈ groups, ∀ pair ∈ g.goals,
      AlgebraSubtype Δ (pair.1.interpret σ) (pair.2.interpret σ)) :
    ∀ goal ∈ reduced.inequalities, ComparisonReduction.PairHolds Δ σ goal := by
  intro goal hgoal
  obtain ⟨g, hg, pair, hp, hi⟩ := collect_goal_coverage h goal hgoal
  obtain ⟨hl, hr⟩ := collect_goal_guards h hguards g hg pair hp
  apply (inequality_algebra_iff hσ hi ?_ ?_).mpr (hgoals g hg pair hp)
  · exact hmodes _ (List.mem_map.mpr ⟨.defined pair.1.mode, hl, rfl⟩)
  · exact hmodes _ (List.mem_map.mpr ⟨.defined pair.2.mode, hr, rfl⟩)

end ModalityInference.ComparisonGroups
