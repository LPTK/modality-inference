import ModalityInference.Declarative

/-! Established structural properties of the declarative judgments. -/
namespace ModalityInference

theorem Typing.weakening {Δ Γ Γ' t a} (h : Typing Δ Γ t a)
    (hc : ContextLe Δ Γ' Γ) : Typing Δ Γ' t a := h.subs hc .refl

theorem RawTyping.weakening {Δ Γ Γ' t a} (h : RawTyping Δ Γ t a)
    (hc : ContextLe Δ Γ' Γ) : RawTyping Δ Γ' t a := by
  obtain ⟨u, hu, ht⟩ := h
  exact ⟨u, hu, ht.weakening hc⟩

end ModalityInference
