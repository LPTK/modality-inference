import ModalityInference.Proofs.ComparisonGroupCoverage

/-! Reduction retains the provenance of every opaque endpoint it emits. -/

namespace ModalityInference.ComparisonReduction

theorem atom_of_outer_var {t : Ty} {v : TypeVar} (h : t.outer.1 = .var v) :
    ComparisonGroups.atom t = some ⟨v, t.outer.2⟩ := by
  unfold ComparisonGroups.atom
  cases he : t.outer with
  | mk a m => simp only [he] at h; simp only [h]

def Collectable (P : TypeVar → Prop) (s : State) : Prop :=
  (∀pair∈s.pending, Supported P pair.1 ∧ Supported P pair.2) ∧
  ∀goal∈s.inequalities, ∃pair : ComparisonGroups.Inequality,
    ComparisonGroups.inequality goal.1 goal.2 = some pair ∧ P pair.1.head ∧ P pair.2.head

theorem step_collectable {s next : State} {P : TypeVar → Prop}
    (h : step s = .success next) (hs : Collectable P s) : Collectable P next := by
  unfold step at h
  split at h
  · cases h; exact hs
  · next left right rest hpending =>
    simp only [Collectable, hpending, List.forall_mem_cons] at hs
    simp only at h
    split at h
    · cases h; exact ⟨hs.1.2, hs.2⟩
    · split at h
      · cases h; exact ⟨hs.1.2, hs.2⟩
      · cases h; exact ⟨hs.1.2, hs.2⟩
      · split at h
        · next result hshared =>
          cases h
          refine ⟨?_, hs.2⟩
          simp only [List.forall_mem_cons]
          refine ⟨?_, hs.1.2⟩
          split at hshared
          · obtain ⟨hl, hr⟩ := ComparisonBody.stripTotal_typeVars hshared
            simpa only [Supported, hl, hr] using hs.1.1
          · contradiction
        · split at h
          · cases h; exact ⟨hs.1.2, hs.2⟩
          · split at h
            · cases h; exact ⟨hs.1.2, hs.2⟩
            · split at h
              all_goals try contradiction
              all_goals cases h
              all_goals try exact ⟨hs.1.2, hs.2⟩
              · rename_i x y hl hr
                refine ⟨hs.1.2, ?_⟩
                simp only [List.forall_mem_cons]
                refine ⟨⟨(⟨x, left.outer.2⟩, ⟨y, right.outer.2⟩), ?_, ?_, ?_⟩, hs.2⟩
                · simp only [ComparisonGroups.inequality, atom_of_outer_var hl,
                    atom_of_outer_var hr, bind, pure, Option.bind]
                · apply hs.1.1.1
                  rw [← TypeExpr.outer_typeVars left, hl]
                  exact Finset.mem_singleton_self _
                · apply hs.1.1.2
                  rw [← TypeExpr.outer_typeVars right, hr]
                  exact Finset.mem_singleton_self _
              all_goals
                refine ⟨?_, hs.2⟩
                have hl : Supported P left.outer.1 := by
                  simpa only [Supported, TypeExpr.outer_typeVars] using hs.1.1.1
                have hr : Supported P right.outer.1 := by
                  simpa only [Supported, TypeExpr.outer_typeVars] using hs.1.1.2
                simp only [*, Supported, TypeExpr.typeVars, Finset.mem_union,
                  or_imp, forall_and] at hl hr
                simp only [List.forall_mem_cons, Supported, TypeExpr.typeVars]
              · exact ⟨⟨hl.1, hr.1⟩, ⟨hl.2, hr.2⟩, hs.1.2⟩
              · exact ⟨⟨hl.1, hr.1⟩, ⟨hl.2, hr.2⟩, hs.1.2⟩
              · exact ⟨⟨hr.1, hl.1⟩, ⟨hl.2, hr.2⟩, hs.1.2⟩

theorem run_collectable {fuel : Nat} {s next : State} {P : TypeVar → Prop}
    (h : run fuel s = .success next) (hs : Collectable P s) : Collectable P next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases hstep : step s <;> simp only [hstep] at h <;> try contradiction
      exact ih h (step_collectable hstep hs)

theorem initial_collectable {bounds : Bounds} {source target : Ty} {P : TypeVar → Prop}
    (hb : ∀c∈bounds, ∀v∈c.typeVars, P v)
    (hs : Supported P source) (ht : Supported P target) :
    Collectable P (initial bounds source target) := by
  refine ⟨?_, by simp [initial]⟩
  intro pair hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨c, hc, he⟩ := List.mem_filterMap.mp hp
    cases c <;> try contradiction
    next left right =>
      cases Option.some.inj he
      obtain ⟨c, hc, hs⟩ := List.mem_flatMap.mp hc
      have hv := Constraint.sub_assumptions_typeVars hs
      exact ⟨fun v hm => hb c hc v (hv (Finset.mem_union_left _ hm)),
        fun v hm => hb c hc v (hv (Finset.mem_union_right _ hm))⟩
  · have he : pair = (source, target) := by simpa only [List.mem_singleton] using hp
    exact he ▸ ⟨hs, ht⟩

theorem prepare_collectable {fuel : Nat} {p : SchemePreparation.Prepared}
    {templates : ComparisonSkeleton.Templates} {known : List ModExpr} {shared : Bool}
    {result : State} {P : TypeVar → Prop}
    (h : prepare fuel p templates [] known shared = .success result)
    (hb : ∀c∈templates.substitution.bounds p.sourceBounds, ∀v∈c.typeVars, P v)
    (hs : Supported P (templates.substitution.ty p.sourceType))
    (ht : Supported P p.targetType) : Collectable P result := by
  simp only [prepare, bind, RunResult.bind] at h
  split at h
  · next reduced hfirst =>
    have hi := run_collectable hfirst (initial_collectable hb hs ht)
    apply run_collectable h
    exact ⟨by simp [ComparisonPartial.reduceBare], hi.2⟩
  · contradiction
  · contradiction

end ModalityInference.ComparisonReduction
