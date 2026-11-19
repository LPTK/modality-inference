import ModalityInference.Proofs.ComparisonRawCarrierRestriction

/-! Lower and upper ideal semantics for capsule-supported derivations.
A partial modal barrier is interpreted literally as a whole supported term.
Principal reflection is asserted only for supported endpoints. -/
namespace ModalityInference.ComparisonRawCarrierRestriction

open ComparisonRawCarrierIdeals

noncomputable section
attribute [local instance] Classical.propDecidable

structure Interpretation (Δ : Bounds) (K : Set Token) where
  lower : LowerIdeal (core Δ K)
  upper : UpperIdeal (core Δ K)

def lowerInter {Δ} {C : Core Δ} (S T : LowerIdeal C) : LowerIdeal C where
  mem a := S.mem a ∧ T.mem a
  carrier h := S.carrier h.1
  shaped h := S.shaped h.1
  lower h hab := ⟨S.lower h hab.1, T.lower h hab.2⟩
  join hs ha hb := ⟨S.join hs ha.1 hb.1, T.join hs ha.2 hb.2⟩

def upperInter {Δ} {C : Core Δ} (S T : UpperIdeal C) : UpperIdeal C where
  mem a := S.mem a ∧ T.mem a
  carrier h := S.carrier h.1
  shaped h := S.shaped h.1
  upper h hab := ⟨S.upper h hab.1, T.upper h hab.2⟩
  meet hs ha hb := ⟨S.meet hs ha.1 hb.1, T.meet hs ha.2 hb.2⟩

def BinaryImage (op : CompareTy → CompareTy → CompareTy)
    (S T : CompareTy → Prop) : CompareTy → Prop :=
  fun a => ∃ b c, S b ∧ T c ∧ a = op b c

def denote (Δ : Bounds) (K : Set Token) : CompareTy → Interpretation Δ K
  | .var v => ⟨.principal (core Δ K) (.var v), .principal (core Δ K) (.var v)⟩
  | .unit => ⟨.principal (core Δ K) .unit, .principal (core Δ K) .unit⟩
  | .credit => ⟨.principal (core Δ K) .credit, .principal (core Δ K) .credit⟩
  | .prod a b =>
      ⟨.closure (core Δ K) (BinaryImage .prod (denote Δ K a).lower.mem (denote Δ K b).lower.mem),
       .closure (core Δ K) (BinaryImage .prod (denote Δ K a).upper.mem (denote Δ K b).upper.mem)⟩
  | .sum a b =>
      ⟨.closure (core Δ K) (BinaryImage .sum (denote Δ K a).lower.mem (denote Δ K b).lower.mem),
       .closure (core Δ K) (BinaryImage .sum (denote Δ K a).upper.mem (denote Δ K b).upper.mem)⟩
  | .fn a b =>
      ⟨.closure (core Δ K) (BinaryImage .fn (denote Δ K a).upper.mem (denote Δ K b).lower.mem),
       .closure (core Δ K) (BinaryImage .fn (denote Δ K a).lower.mem (denote Δ K b).upper.mem)⟩
  | .modal a m =>
      if Entails Δ (.defined m) then
        ⟨.closure (core Δ K) (image (fun t => .modal t m) (denote Δ K a).lower.mem),
         .closure (core Δ K) (image (fun t => .modal t m) (denote Δ K a).upper.mem)⟩
      else
        ⟨.closure (core Δ K) (fun t => Carrier Δ K (.modal a m) ∧ t = .modal a m),
         .closure (core Δ K) (fun t => Carrier Δ K (.modal a m) ∧ t = .modal a m)⟩
  | .join a b =>
      ⟨.closure (core Δ K) (fun t => (denote Δ K a).lower.mem t ∨ (denote Δ K b).lower.mem t),
       upperInter (denote Δ K a).upper (denote Δ K b).upper⟩
  | .meet a b =>
      ⟨lowerInter (denote Δ K a).lower (denote Δ K b).lower,
       .closure (core Δ K) (fun t => (denote Δ K a).upper.mem t ∨ (denote Δ K b).upper.mem t)⟩

theorem lower_bound {Δ K S a t} (h : LowerClosure (core Δ K) S a)
    (hb : ∀ s, S s → Derivation Δ K s t) : Derivation Δ K a t :=
  h.lift _ (.principal _ t) (fun {s} hs _ _ => hb s hs)

theorem upper_bound {Δ K S a t} (h : UpperClosure (core Δ K) S a)
    (hb : ∀ s, S s → Derivation Δ K t s) : Derivation Δ K t a :=
  h.lift _ (.principal _ t) (fun {s} hs _ _ => hb s hs)

theorem denote_sound {Δ : Bounds} {K : Set Token} {a : CompareTy}
    (hcarr : Carrier Δ K a) (hs : a.WellShaped Δ) :
    (∀ c, (denote Δ K a).lower.mem c → Derivation Δ K c a) ∧
      (∀ c, (denote Δ K a).upper.mem c → Derivation Δ K a c) := by
  induction a with
  | fn a b iha ihb =>
    have hca := (carrier_fn.mp hcarr).1
    have hcb := (carrier_fn.mp hcarr).2
    constructor
    · intro c hc
      exact lower_bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact Derivation.fn_congr ((iha hca hs.1).2 x hx) ((ihb hcb hs.2).1 y hy)
    · intro c hc
      exact upper_bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact Derivation.fn_congr ((iha hca hs.1).1 x hx) ((ihb hcb hs.2).2 y hy)
  | modal a m ih =>
    by_cases hm : Entails Δ (.defined m)
    · simp only [denote, if_pos hm]
      constructor
      · intro c hc
        exact lower_bound hc fun _ h => by
          obtain ⟨x, hx, rfl⟩ := h
          exact .congr ((ih ((carrier_modal_total hm).mp hcarr) hs).1 x hx) (.refl hm)
      · intro c hc
        exact upper_bound hc fun _ h => by
          obtain ⟨x, hx, rfl⟩ := h
          exact .congr ((ih ((carrier_modal_total hm).mp hcarr) hs).2 x hx) (.refl hm)
    · simp only [denote, if_neg hm]
      constructor
      · intro c hc
        exact lower_bound hc fun _ h => by
          obtain ⟨_, rfl⟩ := h
          exact .refl hcarr hs
      · intro c hc
        exact upper_bound hc fun _ h => by
          obtain ⟨_, rfl⟩ := h
          exact .refl hcarr hs
  | var | unit | credit =>
    exact ⟨fun _ h => h, fun _ h => h⟩
  | prod a b iha ihb =>
    have hca := (carrier_prod.mp hcarr).1
    have hcb := (carrier_prod.mp hcarr).2
    constructor
    · intro c hc
      exact lower_bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact Derivation.prod_congr ((iha hca hs.1).1 x hx) ((ihb hcb hs.2).1 y hy)
    · intro c hc
      exact upper_bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact Derivation.prod_congr ((iha hca hs.1).2 x hx) ((ihb hcb hs.2).2 y hy)
  | sum a b iha ihb =>
    have hca := (carrier_sum.mp hcarr).1
    have hcb := (carrier_sum.mp hcarr).2
    constructor
    · intro c hc
      exact lower_bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact Derivation.sum_congr ((iha hca hs.1).1 x hx) ((ihb hcb hs.2).1 y hy)
    · intro c hc
      exact upper_bound hc fun _ h => by
        obtain ⟨x, y, hx, hy, rfl⟩ := h
        exact Derivation.sum_congr ((iha hca hs.1).2 x hx) ((ihb hcb hs.2).2 y hy)
  | join a b iha ihb =>
    have hca := (carrier_join.mp hcarr).1
    have hcb := (carrier_join.mp hcarr).2
    constructor
    · intro c hc
      exact lower_bound hc fun t h =>
        h.elim (fun h => ((iha hca hs.1).1 t h).trans (.atom hca hcarr (.joinLeft hs)))
          (fun h => ((ihb hcb hs.2.1).1 t h).trans (.atom hcb hcarr (.joinRight hs)))
    · intro c hc
      exact .joinLeast ((iha hca hs.1).2 c hc.1) ((ihb hcb hs.2.1).2 c hc.2)
  | meet a b iha ihb =>
    have hca := (carrier_meet.mp hcarr).1
    have hcb := (carrier_meet.mp hcarr).2
    constructor
    · intro c hc
      exact .meetGreatest ((iha hca hs.1).1 c hc.1) ((ihb hcb hs.2.1).1 c hc.2)
    · intro c hc
      exact upper_bound hc fun t h =>
        h.elim (fun h => (Derivation.atom hcarr hca (.meetLeft hs)).trans ((iha hca hs.1).2 t h))
          (fun h => (Derivation.atom hcarr hcb (.meetRight hs)).trans ((ihb hcb hs.2.1).2 t h))

theorem denote_self {Δ : Bounds} {K : Set Token} {a : CompareTy}
    (hc : Carrier Δ K a) (hs : a.WellShaped Δ) :
    (denote Δ K a).lower.mem a ∧ (denote Δ K a).upper.mem a := by
  induction a with
  | var | unit | credit => exact ⟨.refl hc hs, .refl hc hs⟩
  | prod a b iha ihb | sum a b iha ihb =>
    have ha := iha (carrier_prod.mp hc).1 hs.1
    have hb := ihb (carrier_prod.mp hc).2 hs.2
    exact ⟨.base hc hs ⟨a, b, ha.1, hb.1, rfl⟩, .base hc hs ⟨a, b, ha.2, hb.2, rfl⟩⟩
  | fn a b iha ihb =>
    have ha := iha (carrier_fn.mp hc).1 hs.1
    have hb := ihb (carrier_fn.mp hc).2 hs.2
    exact ⟨.base hc hs ⟨a, b, ha.2, hb.1, rfl⟩, .base hc hs ⟨a, b, ha.1, hb.2, rfl⟩⟩
  | modal a m ih =>
    by_cases hm : Entails Δ (.defined m)
    · simp only [denote, if_pos hm]
      have ha := ih ((carrier_modal_total hm).mp hc) hs
      exact ⟨.base hc hs ⟨a, ha.1, rfl⟩, .base hc hs ⟨a, ha.2, rfl⟩⟩
    · simp only [denote, if_neg hm]
      exact ⟨.base hc hs ⟨hc, rfl⟩, .base hc hs ⟨hc, rfl⟩⟩
  | join a b iha ihb =>
    have hca := (carrier_join.mp hc).1
    have hcb := (carrier_join.mp hc).2
    have ha := iha hca hs.1
    have hb := ihb hcb hs.2.1
    exact ⟨.join hs (.base hca hs.1 (.inl ha.1)) (.base hcb hs.2.1 (.inr hb.1)),
      ⟨(denote Δ K a).upper.upper (.atom hca hc (.joinLeft hs)) ha.2,
        (denote Δ K b).upper.upper (.atom hcb hc (.joinRight hs)) hb.2⟩⟩
  | meet a b iha ihb =>
    have hca := (carrier_meet.mp hc).1
    have hcb := (carrier_meet.mp hc).2
    have ha := iha hca hs.1
    have hb := ihb hcb hs.2.1
    exact ⟨⟨(denote Δ K a).lower.lower (.atom hc hca (.meetLeft hs)) ha.1,
        (denote Δ K b).lower.lower (.atom hc hcb (.meetRight hs)) hb.1⟩,
      .meet hs (.base hca hs.1 (.inl ha.2)) (.base hcb hs.2.1 (.inr hb.2))⟩

theorem denote_lower_carrier_iff {Δ : Bounds} {K : Set Token} {a c : CompareTy}
    (ha : Carrier Δ K a) (hs : a.WellShaped Δ) :
    (denote Δ K a).lower.mem c ↔ Derivation Δ K c a :=
  ⟨(denote_sound ha hs).1 c,
    fun h => (denote Δ K a).lower.lower h (denote_self ha hs).1⟩

theorem denote_upper_carrier_iff {Δ : Bounds} {K : Set Token} {a c : CompareTy}
    (ha : Carrier Δ K a) (hs : a.WellShaped Δ) :
    (denote Δ K a).upper.mem c ↔ Derivation Δ K a c :=
  ⟨(denote_sound ha hs).2 c,
    fun h => (denote Δ K a).upper.upper h (denote_self ha hs).2⟩

def Related (Δ : Bounds) (K : Set Token) (a b : CompareTy) : Prop :=
  (∀ c, (denote Δ K a).lower.mem c → (denote Δ K b).lower.mem c) ∧
  (∀ c, (denote Δ K b).upper.mem c → (denote Δ K a).upper.mem c)

theorem Related.refl {Δ K a} : Related Δ K a a := ⟨fun _ h => h, fun _ h => h⟩

theorem Related.trans {Δ K a b c} (h : Related Δ K a b) (g : Related Δ K b c) :
    Related Δ K a c := ⟨fun _ hc => g.1 _ (h.1 _ hc), fun _ hc => h.2 _ (g.2 _ hc)⟩

theorem Related.of_derivation {Δ K a b} (h : Derivation Δ K a b) : Related Δ K a b :=
  ⟨fun c hc => (denote_lower_carrier_iff h.carriers.2 h.shaped.2).mpr
      (((denote_sound h.carriers.1 h.shaped.1).1 c hc).trans h),
    fun c hc => (denote_upper_carrier_iff h.carriers.1 h.shaped.1).mpr
      (h.trans ((denote_sound h.carriers.2 h.shaped.2).2 c hc))⟩

theorem Related.derivation {Δ K a b} (ha : Carrier Δ K a) (hb : Carrier Δ K b)
    (hs : a.WellShaped Δ) (ht : b.WellShaped Δ) (h : Related Δ K a b) :
    Derivation Δ K a b :=
  (denote_lower_carrier_iff hb ht).mp (h.1 a (denote_self ha hs).1)

end
end ModalityInference.ComparisonRawCarrierRestriction
