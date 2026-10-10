import ModalityInference.Core.Mode

/-! Concrete algebra used by semantic subtyping. -/
namespace ModalityInference.Mode

@[simp] theorem compose_identity (m : Mode) : m.compose identity = m := by
  cases m; simp [compose, identity]

@[simp] theorem identity_compose (m : Mode) : identity.compose m = m := by
  cases m; simp [compose, identity]

theorem compose_assoc (a b c : Mode) : (a.compose b).compose c = a.compose (b.compose c) := by
  cases a; cases b; cases c; simp [compose, Bool.and_assoc]

theorem le_iff (a b : Mode) : a.le b = true ↔
    (a.isLocal = true → b.isLocal = true) ∧
    (a.once = true → b.once = true) ∧ (b.unique = true → a.unique = true) := by
  simp [le, Bool.or_eq_true, Bool.and_eq_true]
  simp only [Bool.eq_false_iff, or_iff_not_imp_left, not_not, and_assoc]

theorem le_trans {a b c : Mode} (hab : a.le b = true) (hbc : b.le c = true) :
    a.le c = true := by
  simp only [le_iff] at *
  exact ⟨hbc.1 ∘ hab.1, hbc.2.1 ∘ hab.2.1, hab.2.2 ∘ hbc.2.2⟩

theorem compose_le_left (a : Mode) {b c : Mode} (h : b.le c = true) :
    (a.compose b).le (a.compose c) = true := by
  simp only [le_iff, compose, Bool.and_eq_true] at *
  exact ⟨fun ⟨ha, hb⟩ => ⟨ha, h.1 hb⟩, fun ⟨ha, hb⟩ => ⟨ha, h.2.1 hb⟩,
    fun ⟨ha, hc⟩ => ⟨ha, h.2.2 hc⟩⟩

theorem compose_le_right (c : Mode) {a b : Mode} (h : a.le b = true) :
    (a.compose c).le (b.compose c) = true := by
  simp only [le_iff, compose, Bool.and_eq_true] at *
  exact ⟨fun ⟨ha, hc⟩ => ⟨h.1 ha, hc⟩, fun ⟨ha, hc⟩ => ⟨h.2.1 ha, hc⟩,
    fun ⟨hb, hc⟩ => ⟨h.2.2 hb, hc⟩⟩

end ModalityInference.Mode
