import ModalityInference.Proofs.ComparisonPartialCarrierInterpretation
import ModalityInference.Proofs.ComparisonDefinedCovers

/-! Carrier interpretation bounds are derivable in the comparison algebra, and
every well-shaped carrier is contained in both of its interpretations. -/

namespace ModalityInference.ComparisonPartialCarrier

noncomputable section

attribute [local instance] Classical.propDecidable

theorem denote_sound {Δ : Bounds} {a : CompareTy} (hs : a.WellShaped Δ) :
    (∀ c, (denote Δ a).lower.mem c → AlgebraSubtype Δ c a) ∧
      (∀ c, (denote Δ a).upper.mem c → AlgebraSubtype Δ a c) := by
  induction a with
  | fn a b iha ihb =>
    constructor
    · intro c hc
      exact LowerClosure.bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact ComparisonDefinedCovers.fn_congr ((iha hs.1).2 x hx) ((ihb hs.2).1 y hy)
    · intro c hc
      exact UpperClosure.bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact ComparisonDefinedCovers.fn_congr ((iha hs.1).1 x hx) ((ihb hs.2).2 y hy)
  | modal a m ih =>
    by_cases hm : Entails Δ (.defined m)
    · simp only [denote, if_pos hm]
      constructor
      · intro c hc
        exact LowerClosure.bound hc fun _ h => by
          obtain ⟨x, hx, rfl⟩ := h
          exact .congr ((ih hs).1 x hx) (.refl hm)
      · intro c hc
        exact UpperClosure.bound hc fun _ h => by
          obtain ⟨x, hx, rfl⟩ := h
          exact .congr ((ih hs).2 x hx) (.refl hm)
    · simp only [denote, if_neg hm]
      constructor
      · intro c hc
        exact LowerClosure.bound hc fun _ h => by
          obtain ⟨_, rfl⟩ := h
          exact .refl hs
      · intro c hc
        exact UpperClosure.bound hc fun _ h => by
          obtain ⟨_, rfl⟩ := h
          exact .refl hs
  | var | unit | credit =>
    exact ⟨fun _ h => LowerIdeal.principal_sound hs h, fun _ h => UpperIdeal.principal_sound hs h⟩
  | prod a b iha ihb =>
    constructor
    · intro c hc
      exact LowerClosure.bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact ComparisonDefinedCovers.prod_congr ((iha hs.1).1 x hx) ((ihb hs.2).1 y hy)
    · intro c hc
      exact UpperClosure.bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact ComparisonDefinedCovers.prod_congr ((iha hs.1).2 x hx) ((ihb hs.2).2 y hy)
  | sum a b iha ihb =>
    constructor
    · intro c hc
      exact LowerClosure.bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact ComparisonDefinedCovers.sum_congr ((iha hs.1).1 x hx) ((ihb hs.2).1 y hy)
    · intro c hc
      exact UpperClosure.bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact ComparisonDefinedCovers.sum_congr ((iha hs.1).2 x hx) ((ihb hs.2).2 y hy)
  | join a b iha ihb =>
    constructor
    · intro c hc
      exact LowerClosure.bound hc fun t h =>
        h.elim (fun h => ((iha hs.1).1 t h).trans (.shaped (.joinLeft hs)))
          (fun h => ((ihb hs.2.1).1 t h).trans (.shaped (.joinRight hs)))
    · intro c hc
      exact .joinLeast ((iha hs.1).2 c hc.1) ((ihb hs.2.1).2 c hc.2)
  | meet a b iha ihb =>
    constructor
    · intro c hc
      exact .meetGreatest ((iha hs.1).1 c hc.1) ((ihb hs.2.1).1 c hc.2)
    · intro c hc
      exact UpperClosure.bound hc fun t h =>
        h.elim (fun h => (AlgebraSubtype.shaped (.meetLeft hs)).trans ((iha hs.1).2 t h))
          (fun h => (AlgebraSubtype.shaped (.meetRight hs)).trans ((ihb hs.2.1).2 t h))

theorem denote_self {Δ : Bounds} {a : CompareTy} (hc : Carrier Δ a) (hs : a.WellShaped Δ) :
    (denote Δ a).lower.mem a ∧ (denote Δ a).upper.mem a := by
  induction a with
  | var | unit | credit => exact ⟨.base hc hs rfl, .base hc hs rfl⟩
  | prod a b iha ihb | sum a b iha ihb =>
    have ha := iha hc.1 hs.1
    have hb := ihb hc.2 hs.2
    exact ⟨.base hc hs ⟨a, b, ha.1, hb.1, rfl⟩, .base hc hs ⟨a, b, ha.2, hb.2, rfl⟩⟩
  | fn a b iha ihb =>
    have ha := iha hc.1 hs.1
    have hb := ihb hc.2 hs.2
    exact ⟨.base hc hs ⟨a, b, ha.2, hb.1, rfl⟩, .base hc hs ⟨a, b, ha.1, hb.2, rfl⟩⟩
  | modal a m ih =>
    by_cases hm : Entails Δ (.defined m)
    · simp only [denote, if_pos hm]
      have ha := ih hc hs
      exact ⟨.base hc hs ⟨a, ha.1, rfl⟩, .base hc hs ⟨a, ha.2, rfl⟩⟩
    · simp only [denote, if_neg hm]
      exact ⟨.base hc hs ⟨hc, rfl⟩, .base hc hs ⟨hc, rfl⟩⟩
  | join a b iha ihb =>
    have hca := Carrier.of_defined hc.1
    have hcb := Carrier.of_defined hc.2
    have ha := iha hca hs.1
    have hb := ihb hcb hs.2.1
    constructor
    · exact .join ⟨hs, hc⟩ (.base hca hs.1 (.inl ha.1)) (.base hcb hs.2.1 (.inr hb.1))
    · exact ⟨(denote Δ a).upper.upper _ _ hc (.shaped (.joinLeft hs)) ha.2,
        (denote Δ b).upper.upper _ _ hc (.shaped (.joinRight hs)) hb.2⟩
  | meet a b iha ihb =>
    have hca := Carrier.of_defined hc.1
    have hcb := Carrier.of_defined hc.2
    have ha := iha hca hs.1
    have hb := ihb hcb hs.2.1
    constructor
    · exact ⟨(denote Δ a).lower.lower _ _ hc (.shaped (.meetLeft hs)) ha.1,
        (denote Δ b).lower.lower _ _ hc (.shaped (.meetRight hs)) hb.1⟩
    · exact .meet ⟨hs, hc⟩ (.base hca hs.1 (.inl ha.2)) (.base hcb hs.2.1 (.inr hb.2))

theorem denote_lower_carrier_iff {Δ : Bounds} {a c : CompareTy}
    (ha : Carrier Δ a) (hs : a.WellShaped Δ) :
    (denote Δ a).lower.mem c ↔ Carrier Δ c ∧ AlgebraSubtype Δ c a :=
  ⟨fun h => ⟨(denote Δ a).lower.carrier c h, (denote_sound hs).1 c h⟩,
    fun h => (denote Δ a).lower.lower c a h.1 h.2 (denote_self ha hs).1⟩

theorem denote_upper_carrier_iff {Δ : Bounds} {a c : CompareTy}
    (ha : Carrier Δ a) (hs : a.WellShaped Δ) :
    (denote Δ a).upper.mem c ↔ Carrier Δ c ∧ AlgebraSubtype Δ a c :=
  ⟨fun h => ⟨(denote Δ a).upper.carrier c h, (denote_sound hs).2 c h⟩,
    fun h => (denote Δ a).upper.upper c a h.1 h.2 (denote_self ha hs).2⟩

end
end ModalityInference.ComparisonPartialCarrier
