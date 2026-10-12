import ModalityInference.Proofs.Resources

/-! Ownership evidence is stable across worlds whenever every reference of the
value remains live. Closure contracts already quantify over calling worlds. -/
namespace ModalityInference

theorem ResourceInterpretation.reworld {w w' t ambient v owned}
    (h : ResourceInterpretation w t ambient v owned) (hv : w'.ValidValue v) :
    ResourceInterpretation w' t ambient v owned := by
  induction t generalizing ambient v owned
  all_goals cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at h ⊢
  case prod.pair a b m iha ihb l x y =>
    exact let ⟨first, second, hx, hy, hd⟩ := h.2.2.2
      ⟨hv, h.2.1, h.2.2.1, first, second,
        iha hx (fun k hk => hv k (.pairLeft hk)),
        ihb hy (fun k hk => hv k (.pairRight hk)), hd⟩
  case sum.inl a b m iha _ x =>
    exact ⟨hv, h.2.1, iha h.2.2 (fun k hk => hv k (.inl hk))⟩
  case sum.inr a b m _ ihb x =>
    exact ⟨hv, h.2.1, ihb h.2.2 (fun k hk => hv k (.inr hk))⟩
  all_goals exact ⟨hv, h.2⟩

theorem ResourceSchemeInterpretation.reworld {ρ w w' s v reserved}
    (h : ResourceSchemeInterpretation ρ w s v reserved) (hv : w'.ValidValue v) :
    ResourceSchemeInterpretation ρ w' s v reserved :=
  ⟨h.1, fun η t hη ht => let ⟨owned, hs, hr⟩ := h.2 η t hη ht
    ⟨owned, hs, hr.reworld hv⟩⟩

theorem ResourceEnvironmentInterpretation.reworld {ρ w w' Γ γ reserved}
    (h : ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (hv : ∀ v ∈ γ, w'.ValidValue v) :
    ResourceEnvironmentInterpretation ρ w' Γ γ reserved :=
  ⟨fun i s hi => let ⟨v, hvalue, hr⟩ := h.1 i s hi
    ⟨v, hvalue, hr.reworld (hv v (List.mem_of_getElem? hvalue))⟩, h.2⟩

end ModalityInference
