import ModalityInference.Proofs.ComparisonReduction
import ModalityInference.Proofs.ComparisonAnnotations

/-! Mode-variable support of structural reduction and partial interval images. -/
namespace ModalityInference

namespace ComparisonInterpolation

theorem supports_ofTy_modes (Q : ModVar → Prop) (t : Ty) :
    Supports (fun _ => True) Q (.ofTy t) ↔ ∀ v ∈ t.modVars, Q v := by
  induction t <;> simp_all [Supports, CompareTy.ofTy, TypeExpr.modVars, or_imp, forall_and]

end ComparisonInterpolation

namespace TypeExpr

theorem outer_modVars (t : Ty) :
    t.outer.1.modVars ∪ t.outer.2.vars ⊆ t.modVars := by
  induction t <;> simp only [outer, modVars, ModExpr.epsilon, ModExpr.vars,
    Finset.union_empty]
  all_goals try exact Finset.Subset.refl _
  next a m ih =>
    simpa only [Finset.union_assoc] using Finset.union_subset_union ih (Finset.Subset.refl m.vars)

theorem wellFormedBounds_modeSupport {Q : ModVar → Prop} (t : Ty)
    (ht : ∀ v ∈ t.modVars, Q v) : ∀ c ∈ t.wellFormedBounds, ∀ v ∈ c.modVars, Q v := by
  induction t <;> simp_all [wellFormedBounds, modVars, Constraint.modVars,
    or_imp, forall_and]
  all_goals first | assumption | exact ⟨by assumption, by assumption⟩

end TypeExpr

theorem Constraint.assumptions_modeSupport {Q : ModVar → Prop} (c : Constraint)
    (hc : ∀ v ∈ c.modVars, Q v) : ∀ d ∈ c.assumptions, ∀ v ∈ d.modVars, Q v := by
  cases c <;> simp [Constraint.assumptions, Constraint.modVars, TypeExpr.modVars,
    or_imp, forall_and, and_assoc] at hc ⊢
  case sub a b =>
    exact ⟨hc.1, hc.2, TypeExpr.wellFormedBounds_modeSupport a hc.1,
      TypeExpr.wellFormedBounds_modeSupport b hc.2⟩
  case mode => exact hc
  case defined => exact hc
  case equal v a => exact ⟨hc, TypeExpr.wellFormedBounds_modeSupport a hc⟩
  case equiv a b =>
    exact ⟨hc.1, hc.2, hc.1, TypeExpr.wellFormedBounds_modeSupport a hc.1,
      TypeExpr.wellFormedBounds_modeSupport b hc.2⟩

namespace ComparisonBody

theorem peelFuel_modeSupport {Q : ModVar → Prop} (total : ModExpr → Bool) (fuel : Nat)
    (t : Ty) (ht : ∀ v ∈ t.modVars, Q v) :
    (∀ v ∈ (peelFuel total fuel t).base.modVars, Q v) ∧
      ∀ m ∈ (peelFuel total fuel t).labels, ∀ v ∈ m.vars, Q v := by
  induction fuel generalizing t with
  | zero => exact ⟨ht, by simp [peelFuel]⟩
  | succ fuel ih =>
    have hn : ∀ v ∈ (ComparisonPartialModes.normalizeOuter t).modVars, Q v :=
      fun v hv => ht v (ComparisonAnnotations.normalizeOuterFuel_modeVars _ _ hv)
    cases he : ComparisonPartialModes.normalizeOuter t <;> simp only [peelFuel, he]
    all_goals try exact ⟨by simpa only [he] using hn, by simp⟩
    split
    · rename_i a m hm
      have ha : ∀ v ∈ a.modVars, Q v :=
        fun v hv => hn v (by simp only [he, TypeExpr.modVars]; exact Finset.mem_union_left _ hv)
      have hm' : ∀ v ∈ m.vars, Q v :=
        fun v hv => hn v (by simp only [he, TypeExpr.modVars]; exact Finset.mem_union_right _ hv)
      exact ⟨(ih a ha).1, by simpa only [List.forall_mem_cons] using And.intro hm' (ih a ha).2⟩
    · exact ⟨by simpa only [he] using hn, by simp⟩

theorem stripTotal_modeSupport {Q : ModVar → Prop} {total : ModExpr → Bool}
    {left right : Ty} {result : TotalStep} (h : stripTotal total left right = some result)
    (hl : ∀ v ∈ left.modVars, Q v) (hr : ∀ v ∈ right.modVars, Q v) :
    (∀ v ∈ result.bases.1.modVars, Q v) ∧ (∀ v ∈ result.bases.2.modVars, Q v) ∧
      (∀ v ∈ result.labels.1.vars, Q v) ∧ ∀ v ∈ result.labels.2.vars, Q v := by
  obtain ⟨hb, hm⟩ := stripTotal_spec h
  rw [hb, hm]
  exact ⟨(peelFuel_modeSupport total 1 left hl).1,
    (peelFuel_modeSupport total 1 right hr).1,
    ComparisonPartialModes.recompose_support _ (peelFuel_modeSupport total 1 left hl).2,
    ComparisonPartialModes.recompose_support _ (peelFuel_modeSupport total 1 right hr).2⟩

theorem suffixGoal_modeSupport {Q : ModVar → Prop} {total : ModExpr → Bool}
    {left right : Ty} {m n : ModExpr} (h : suffixGoal total left right = some (m, n))
    (hl : ∀ v ∈ left.modVars, Q v) (hr : ∀ v ∈ right.modVars, Q v) :
    (∀ v ∈ m.vars, Q v) ∧ ∀ v ∈ n.vars, Q v := by
  simp only [suffixGoal] at h
  split at h
  · cases h
    exact ⟨ComparisonPartialModes.recompose_support _ (peelFuel_modeSupport total _ left hl).2,
      ComparisonPartialModes.recompose_support _ (peelFuel_modeSupport total _ right hr).2⟩
  · contradiction

end ComparisonBody

namespace ComparisonReduction

structure ModeSupport (Q : ModVar → Prop) (s : State) : Prop where
  pending : ∀ pair ∈ s.pending,
    (∀ v ∈ pair.1.modVars, Q v) ∧ ∀ v ∈ pair.2.modVars, Q v
  inequalities : ∀ pair ∈ s.inequalities,
    (∀ v ∈ pair.1.modVars, Q v) ∧ ∀ v ∈ pair.2.modVars, Q v
  modes : ∀ c ∈ s.modes, ∀ v ∈ c.modVars, Q v
  bareBounds : ∀ b ∈ s.bareBounds, ∀ v ∈ b.endpoint.modVars, Q v
  partialTypes : ∀ entry ∈ s.partialTypes,
    ComparisonInterpolation.Supports (fun _ => True) Q entry.2

theorem modeSupport_iff {Q s} : ModeSupport Q s ↔
    (∀ pair ∈ s.pending, (∀ v ∈ pair.1.modVars, Q v) ∧ ∀ v ∈ pair.2.modVars, Q v) ∧
    (∀ pair ∈ s.inequalities, (∀ v ∈ pair.1.modVars, Q v) ∧ ∀ v ∈ pair.2.modVars, Q v) ∧
    (∀ c ∈ s.modes, ∀ v ∈ c.modVars, Q v) ∧
    (∀ b ∈ s.bareBounds, ∀ v ∈ b.endpoint.modVars, Q v) ∧
    ∀ entry ∈ s.partialTypes, ComparisonInterpolation.Supports (fun _ => True) Q entry.2 :=
  ⟨fun h => ⟨h.pending, h.inequalities, h.modes, h.bareBounds, h.partialTypes⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

theorem step_modeSupport {Q : ModVar → Prop} {s next : State}
    (h : step s = .success next) (hs : ModeSupport Q s) : ModeSupport Q next := by
  unfold step at h
  split at h
  · cases h; exact hs
  · next left right rest hpending =>
    simp only [modeSupport_iff, hpending, List.forall_mem_cons] at hs
    have hlb : ∀ v ∈ left.outer.1.modVars, Q v :=
      fun v hv => hs.1.1.1 v (left.outer_modVars (Finset.mem_union_left _ hv))
    have hrb : ∀ v ∈ right.outer.1.modVars, Q v :=
      fun v hv => hs.1.1.2 v (right.outer_modVars (Finset.mem_union_left _ hv))
    have hlm : ∀ v ∈ left.outer.2.vars, Q v :=
      fun v hv => hs.1.1.1 v (left.outer_modVars (Finset.mem_union_right _ hv))
    have hrm : ∀ v ∈ right.outer.2.vars, Q v :=
      fun v hv => hs.1.1.2 v (right.outer_modVars (Finset.mem_union_right _ hv))
    simp only at h
    split at h
    · cases h
      exact modeSupport_iff.mpr ⟨hs.1.2, hs.2⟩
    · split at h
      · cases h
        exact modeSupport_iff.mpr ⟨hs.1.2, hs.2.1, hs.2.2.1,
          by simpa only [List.forall_mem_cons] using And.intro hs.1.1.2 hs.2.2.2.1,
          hs.2.2.2.2⟩
      · cases h
        exact modeSupport_iff.mpr ⟨hs.1.2, hs.2.1, hs.2.2.1,
          by simpa only [List.forall_mem_cons] using And.intro hs.1.1.1 hs.2.2.2.1,
          hs.2.2.2.2⟩
      · split at h
        · next result hshared =>
          cases h
          split at hshared
          · have hp := ComparisonBody.stripTotal_modeSupport hshared hs.1.1.1 hs.1.1.2
            apply modeSupport_iff.mpr
            refine ⟨?_, hs.2.1, ?_, hs.2.2.2⟩
            · simpa only [List.forall_mem_cons] using And.intro ⟨hp.1, hp.2.1⟩ hs.1.2
            · simp only [List.forall_mem_cons]
              exact ⟨fun v hv => (Finset.mem_union.mp hv).elim (hp.2.2.1 v) (hp.2.2.2 v), hs.2.2.1⟩
          · contradiction
        · split at h
          · cases h
            exact modeSupport_iff.mpr ⟨hs.1.2, hs.2⟩
          · split at h
            · next m n hsuffix =>
              cases h
              split at hsuffix
              · have hm := ComparisonBody.suffixGoal_modeSupport hsuffix hs.1.1.1 hs.1.1.2
                apply modeSupport_iff.mpr
                refine ⟨hs.1.2, hs.2.1, ?_, hs.2.2.2⟩
                simp only [List.forall_mem_cons]
                exact ⟨fun v hv => (Finset.mem_union.mp hv).elim (hm.1 v) (hm.2 v), hs.2.2.1⟩
              · contradiction
            · split at h
              all_goals try contradiction
              all_goals cases h
              all_goals simp only [*, TypeExpr.modVars, Finset.mem_union, or_imp, forall_and]
                at hlb hrb
              · apply modeSupport_iff.mpr
                refine ⟨hs.1.2, ?_, ?_, hs.2.2.2⟩
                · simpa only [List.forall_mem_cons] using And.intro hs.1.1 hs.2.1
                · simpa only [List.forall_mem_cons, Constraint.modVars] using
                    And.intro hlm (And.intro hrm hs.2.2.1)
              · apply modeSupport_iff.mpr
                refine ⟨hs.1.2, hs.2.1, ?_, hs.2.2.2⟩
                simp only [List.forall_mem_cons]
                exact ⟨fun v hv => (Finset.mem_union.mp hv).elim (hlm v) (hrm v), hs.2.2.1⟩
              · apply modeSupport_iff.mpr
                refine ⟨hs.1.2, hs.2.1, ?_, hs.2.2.2⟩
                simp only [List.forall_mem_cons, Constraint.modVars, ModExpr.vars, Finset.union_empty]
                exact ⟨fun v hv => (Finset.mem_union.mp hv).elim (hlm v) (hrm v), hs.2.2.1⟩
              · apply modeSupport_iff.mpr
                refine ⟨?_, hs.2.1, ?_, hs.2.2.2⟩
                · simp only [List.forall_mem_cons]
                  exact ⟨⟨fun v hv => (Finset.mem_union.mp hv).elim (hlb.1 v) (hlm v),
                    fun v hv => (Finset.mem_union.mp hv).elim (hrb.1 v) (hrm v)⟩,
                    ⟨fun v hv => (Finset.mem_union.mp hv).elim (hlb.2 v) (hlm v),
                    fun v hv => (Finset.mem_union.mp hv).elim (hrb.2 v) (hrm v)⟩, hs.1.2⟩
                · simp only [List.forall_mem_cons]
                  exact ⟨fun v hv => (Finset.mem_union.mp hv).elim (hlm v) (hrm v), hs.2.2.1⟩
              · apply modeSupport_iff.mpr
                refine ⟨?_, hs.2.1, ?_, hs.2.2.2⟩
                · simp only [List.forall_mem_cons]
                  exact ⟨⟨fun v hv => (Finset.mem_union.mp hv).elim (hlb.1 v) (hlm v),
                    fun v hv => (Finset.mem_union.mp hv).elim (hrb.1 v) (hrm v)⟩,
                    ⟨fun v hv => (Finset.mem_union.mp hv).elim (hlb.2 v) (hlm v),
                    fun v hv => (Finset.mem_union.mp hv).elim (hrb.2 v) (hrm v)⟩, hs.1.2⟩
                · simp only [List.forall_mem_cons]
                  exact ⟨fun v hv => (Finset.mem_union.mp hv).elim (hlm v) (hrm v), hs.2.2.1⟩
              · apply modeSupport_iff.mpr
                refine ⟨?_, hs.2.1, ?_, hs.2.2.2⟩
                · simpa only [List.forall_mem_cons] using
                    And.intro ⟨hrb.1, hlb.1⟩ (And.intro ⟨hlb.2, hrb.2⟩ hs.1.2)
                · simp only [List.forall_mem_cons, Constraint.modVars, ModExpr.top,
                    ModExpr.vars, Finset.union_empty]
                  exact ⟨fun v hv => (Finset.mem_union.mp hv).elim (hlm v) (hrm v), hs.2.2.1⟩

theorem run_modeSupport {Q : ModVar → Prop} {fuel : Nat} {s next : State}
    (h : run fuel s = .success next) (hs : ModeSupport Q s) : ModeSupport Q next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases he : step s <;> simp only [he] at h <;> try contradiction
      exact ih h (step_modeSupport he hs)

theorem initial_modeSupport {Q : ModVar → Prop} {bounds : Bounds} {source target : Ty}
    (hb : ∀ c ∈ bounds, ∀ v ∈ c.modVars, Q v)
    (hs : ∀ v ∈ source.modVars, Q v) (ht : ∀ v ∈ target.modVars, Q v) :
    ModeSupport Q (initial bounds source target) := by
  have ha : ∀ c ∈ bounds.assumptions, ∀ v ∈ c.modVars, Q v := by
    intro c hc
    obtain ⟨b, hmem, hc⟩ := List.mem_flatMap.mp hc
    exact b.assumptions_modeSupport (hb b hmem) c hc
  refine ⟨?_, by simp [initial], ?_, by simp [initial], by simp [initial]⟩
  · intro pair hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨c, hc, he⟩ := List.mem_filterMap.mp hp
      cases c <;> simp only at he <;> try contradiction
      next a b =>
        cases he
        exact ⟨fun v hv => ha _ hc v (Finset.mem_union_left _ hv),
          fun v hv => ha _ hc v (Finset.mem_union_right _ hv)⟩
    · obtain rfl := List.mem_singleton.mp hp
      exact ⟨hs, ht⟩
  · intro c hc
    exact ha c (List.mem_filter.mp hc).1

theorem prepare_modeSupport {Q : ModVar → Prop} {fuel : Nat}
    {p : SchemePreparation.Prepared} {templates : ComparisonSkeleton.Templates}
    {bare : List Nat} {known : List ModExpr} {shared : Bool} {result : State}
    (h : prepare fuel p templates bare known shared = .success result)
    (hb : ∀ c ∈ templates.substitution.bounds p.sourceBounds, ∀ v ∈ c.modVars, Q v)
    (hs : ∀ v ∈ (templates.substitution.ty p.sourceType).modVars, Q v)
    (ht : ∀ v ∈ p.targetType.modVars, Q v) : ModeSupport Q result := by
  unfold prepare at h
  simp only [bind, RunResult.bind] at h
  split at h
  · next middle hr =>
    have hi := initial_modeSupport hb hs ht
    have hm := run_modeSupport hr ⟨hi.pending, hi.inequalities, hi.modes,
      hi.bareBounds, hi.partialTypes⟩
    apply run_modeSupport h
    refine ⟨?_, hm.inequalities, hm.modes, by simp, ?_⟩
    · simp only [ComparisonPartial.reduceBare, ComparisonPartial.crossed,
        List.forall_mem_flatMap, List.forall_mem_map]
      intro name _ a ha b hb
      obtain ⟨lower, hl, _, _, rfl⟩ := ComparisonPartial.mem_lower.mp ha
      obtain ⟨upper, hu, _, _, rfl⟩ := ComparisonPartial.mem_upper.mp hb
      exact ⟨hm.bareBounds lower hl, hm.bareBounds upper hu⟩
    · simp only [ComparisonPartial.reduceBare, List.forall_mem_map]
      intro name _
      apply ComparisonPartial.image_support
      intro b hb
      exact (ComparisonInterpolation.supports_ofTy_modes Q b.endpoint).mpr (hm.bareBounds b hb)

  · contradiction
  · contradiction

end ComparisonReduction

end ModalityInference
