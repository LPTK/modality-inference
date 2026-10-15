import ModalityInference.Proofs.ComparisonPartialCarrier

namespace ModalityInference.ComparisonPartialCarrier

theorem LowerClosure.factor {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {S : CompareTy → Prop} (hS : ∀ a, S a → Carrier Δ a)
    (hjoin : ∀ a b, S a → S b → ComparisonAlgebra.Compatible Δ a b →
      ∃ c, S c ∧ AlgebraSubtype Δ a c ∧ AlgebraSubtype Δ b c)
    {a : CompareTy} (h : LowerClosure Δ S a) :
    ∃ b, S b ∧ AlgebraSubtype Δ a b := by
  induction h with
  | base _ hs hS => exact ⟨_, hS, .refl hs⟩
  | lower _ hab _ ih =>
    obtain ⟨c, hc, hbc⟩ := ih
    exact ⟨c, hc, hab.trans hbc⟩
  | @join a b hc ha hb iha ihb =>
    obtain ⟨x, hx, hax⟩ := iha
    obtain ⟨y, hy, hby⟩ := ihb
    have hxy : ComparisonAlgebra.Compatible Δ x y :=
      ⟨⟨hax.wellShaped_right, hby.wellShaped_right,
        hax.shape_equivalent.symm.trans (hc.1.2.2.trans hby.shape_equivalent)⟩,
        (hS x hx).defined_of_above hΔ hc.2.1 hax,
        (hS y hy).defined_of_above hΔ hc.2.2 hby⟩
    obtain ⟨c, hc, hxc, hyc⟩ := hjoin x y hx hy hxy
    exact ⟨c, hc, .joinLeast (hax.trans hxc) (hby.trans hyc)⟩

theorem LowerClosure.lift {Δ : Bounds} {S : CompareTy → Prop} (T : LowerIdeal Δ)
    (hST : ∀ a, S a → T.mem a) {a : CompareTy} (h : LowerClosure Δ S a) : T.mem a := by
  induction h with
  | base _ _ hS => exact hST _ hS
  | lower hc hab _ ih => exact T.lower _ _ hc hab ih
  | join hc _ _ iha ihb => exact T.join _ _ hc iha ihb

def LowerIdeal.inter {Δ : Bounds} (S T : LowerIdeal Δ) : LowerIdeal Δ where
  mem a := S.mem a ∧ T.mem a
  carrier a h := S.carrier a h.1
  shaped a h := S.shaped a h.1
  lower a b hc hab hb := ⟨S.lower a b hc hab hb.1, T.lower a b hc hab hb.2⟩
  join a b hc ha hb := ⟨S.join a b hc ha.1 hb.1, T.join a b hc ha.2 hb.2⟩

def LowerIdeal.principal (Δ : Bounds) (a : CompareTy) : LowerIdeal Δ :=
  .closure Δ (fun b => b = a)

theorem LowerIdeal.principal_mem {Δ : Bounds} {a b : CompareTy}
    (ha : Carrier Δ a) (hb : Carrier Δ b) (hab : AlgebraSubtype Δ a b) :
    (LowerIdeal.principal Δ b).mem a :=
  .lower ha hab (.base hb hab.wellShaped_right rfl)

theorem LowerIdeal.principal_sound {Δ : Bounds} {a b : CompareTy}
    (hb : b.WellShaped Δ) (h : (LowerIdeal.principal Δ b).mem a) :
    AlgebraSubtype Δ a b :=
  h.bound fun _ he => by subst he; exact .refl hb

end ModalityInference.ComparisonPartialCarrier
