import ModalityInference.Proofs.ComparisonPartialCarrier

/-! Upper carrier ideals preserve partial boundaries while closing their
defined members under compatible meets. -/

namespace ModalityInference.ComparisonPartialCarrier

inductive UpperClosure (Δ : Bounds) (S : CompareTy → Prop) : CompareTy → Prop where
  | base {a} : Carrier Δ a → a.WellShaped Δ → S a → UpperClosure Δ S a
  | upper {a b} : Carrier Δ a → AlgebraSubtype Δ b a →
      UpperClosure Δ S b → UpperClosure Δ S a
  | meet {a b} : ComparisonAlgebra.Compatible Δ a b →
      UpperClosure Δ S a → UpperClosure Δ S b → UpperClosure Δ S (.meet a b)

theorem UpperClosure.carrier {Δ S a} (h : UpperClosure Δ S a) : Carrier Δ a := by
  induction h with
  | base hc _ _ | upper hc _ _ _ => exact hc
  | meet hc _ _ _ _ => exact hc.2

theorem UpperClosure.shaped {Δ S a} (h : UpperClosure Δ S a) : a.WellShaped Δ := by
  induction h with
  | base _ hs _ => exact hs
  | upper _ hab _ _ => exact hab.wellShaped_right
  | meet hc _ _ _ _ => exact hc.1

theorem UpperClosure.bound {Δ S a t} (h : UpperClosure Δ S a)
    (hS : ∀ s, S s → AlgebraSubtype Δ t s) : AlgebraSubtype Δ t a := by
  induction h with
  | base _ _ hs => exact hS _ hs
  | upper _ hab _ ih => exact ih.trans hab
  | meet _ _ _ iha ihb => exact .meetGreatest iha ihb

theorem UpperClosure.partial {Δ S a} (hΔ : Δ.TypeBoundsDefined)
    (h : UpperClosure Δ S a) (ha : ¬a.DefinedUnder Δ) :
    ∃ b, S b ∧ AlgebraSubtype Δ b a := by
  induction h with
  | base _ hs hS => exact ⟨_, hS, .refl hs⟩
  | @upper a b hc hba hb ih =>
    have hn : ¬ b.DefinedUnder Δ := fun h => ha ((hb.carrier.defined_iff hΔ hc hba).mp h)
    obtain ⟨c, hc, hcb⟩ := ih hn
    exact ⟨c, hc, hcb.trans hba⟩
  | meet hc _ _ _ _ => exact False.elim (ha (CompareTy.definedUnder_meet_iff.mpr hc.2))

theorem UpperClosure.factor {Δ S a} (hΔ : Δ.TypeBoundsDefined)
    (hS : ∀ a, S a → Carrier Δ a)
    (hmeet : ∀ a b, S a → S b → ComparisonAlgebra.Compatible Δ a b →
      ∃ c, S c ∧ AlgebraSubtype Δ c a ∧ AlgebraSubtype Δ c b)
    (h : UpperClosure Δ S a) : ∃ b, S b ∧ AlgebraSubtype Δ b a := by
  induction h with
  | base _ hs hS => exact ⟨_, hS, .refl hs⟩
  | upper _ hab _ ih =>
    obtain ⟨c, hc, hbc⟩ := ih
    exact ⟨c, hc, hbc.trans hab⟩
  | @meet a b hc ha hb iha ihb =>
    obtain ⟨x, hx, hxa⟩ := iha
    obtain ⟨y, hy, hyb⟩ := ihb
    have hxy : ComparisonAlgebra.Compatible Δ x y :=
      ⟨⟨hxa.wellShaped_left, hyb.wellShaped_left,
        hxa.shape_equivalent.trans (hc.1.2.2.trans hyb.shape_equivalent.symm)⟩,
        (hS x hx).defined_of_below hΔ hc.2.1 hxa,
        (hS y hy).defined_of_below hΔ hc.2.2 hyb⟩
    obtain ⟨c, hc, hcx, hcy⟩ := hmeet x y hx hy hxy
    exact ⟨c, hc, .meetGreatest (hcx.trans hxa) (hcy.trans hyb)⟩

structure UpperIdeal (Δ : Bounds) where
  mem : CompareTy → Prop
  carrier : ∀ a, mem a → Carrier Δ a
  shaped : ∀ a, mem a → a.WellShaped Δ
  upper : ∀ a b, Carrier Δ a → AlgebraSubtype Δ b a → mem b → mem a
  meet : ∀ a b, ComparisonAlgebra.Compatible Δ a b → mem a → mem b → mem (.meet a b)

def UpperIdeal.closure (Δ : Bounds) (S : CompareTy → Prop) : UpperIdeal Δ where
  mem := UpperClosure Δ S
  carrier := fun _ => UpperClosure.carrier
  shaped := fun _ => UpperClosure.shaped
  upper := fun _ _ => UpperClosure.upper
  meet := fun _ _ => UpperClosure.meet

def UpperIdeal.modalImage {Δ : Bounds} (S : UpperIdeal Δ) (m : ModExpr) : CompareTy → Prop :=
  fun a => ∃ b, S.mem b ∧ a = .modal b m

theorem UpperIdeal.modal_factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (S : UpperIdeal Δ) {m : ModExpr} (hm : Submode Δ m m) {a : CompareTy}
    (h : UpperClosure Δ (S.modalImage m) a) :
    ∃ b, S.mem b ∧ AlgebraSubtype Δ (.modal b m) a := by
  induction h with
  | base _ hs hS =>
    obtain ⟨b, hb, rfl⟩ := hS
    exact ⟨b, hb, .refl hs⟩
  | upper _ hab _ ih =>
    obtain ⟨c, hc, hbc⟩ := ih
    exact ⟨c, hc, hbc.trans hab⟩
  | @meet a b hc ha hb iha ihb =>
    obtain ⟨x, hx, hxa⟩ := iha
    obtain ⟨y, hy, hyb⟩ := ihb
    have hxdef : x.DefinedUnder Δ :=
      (CompareTy.definedUnder_modal_iff.mp
        ((S.carrier x hx).defined_of_below (a := .modal x m) hΔ hc.2.1 hxa)).1
    have hydef : y.DefinedUnder Δ :=
      (CompareTy.definedUnder_modal_iff.mp
        ((S.carrier y hy).defined_of_below (a := .modal y m) hΔ hc.2.2 hyb)).1
    have hxy : ComparisonAlgebra.Compatible Δ x y :=
      ⟨⟨S.shaped x hx, S.shaped y hy,
        hxa.shape_equivalent.trans (hc.1.2.2.trans hyb.shape_equivalent.symm)⟩, hxdef, hydef⟩
    refine ⟨.meet x y, S.meet x y hxy hx hy, .meetGreatest ?_ ?_⟩
    · exact (AlgebraSubtype.congr (.shaped (.meetLeft hxy.1)) hm).trans hxa
    · exact (AlgebraSubtype.congr (.shaped (.meetRight hxy.1)) hm).trans hyb

end ModalityInference.ComparisonPartialCarrier
