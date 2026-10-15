import ModalityInference.Proofs.ComparisonPartialCarrierUpper

/-! Closure and principal-filter operations for upper carrier approximations. -/

namespace ModalityInference.ComparisonPartialCarrier

theorem UpperClosure.lift {Δ : Bounds} {S : CompareTy → Prop} (T : UpperIdeal Δ)
    (hST : ∀ a, S a → T.mem a) {a : CompareTy} (h : UpperClosure Δ S a) : T.mem a := by
  induction h with
  | base _ _ hS => exact hST _ hS
  | upper hc hab _ ih => exact T.upper _ _ hc hab ih
  | meet hc _ _ iha ihb => exact T.meet _ _ hc iha ihb

def UpperIdeal.inter {Δ : Bounds} (S T : UpperIdeal Δ) : UpperIdeal Δ where
  mem a := S.mem a ∧ T.mem a
  carrier a h := S.carrier a h.1
  shaped a h := S.shaped a h.1
  upper a b hc hab hb := ⟨S.upper a b hc hab hb.1, T.upper a b hc hab hb.2⟩
  meet a b hc ha hb := ⟨S.meet a b hc ha.1 hb.1, T.meet a b hc ha.2 hb.2⟩

def UpperIdeal.principal (Δ : Bounds) (a : CompareTy) : UpperIdeal Δ :=
  .closure Δ (fun b => b = a)

theorem UpperIdeal.principal_mem {Δ : Bounds} {a b : CompareTy}
    (ha : Carrier Δ a) (hb : Carrier Δ b) (hab : AlgebraSubtype Δ a b) :
    (UpperIdeal.principal Δ a).mem b :=
  .upper hb hab (.base ha hab.wellShaped_left rfl)

theorem UpperIdeal.principal_sound {Δ : Bounds} {a b : CompareTy}
    (ha : a.WellShaped Δ) (h : (UpperIdeal.principal Δ a).mem b) :
    AlgebraSubtype Δ a b :=
  h.bound fun _ he => by subst he; exact .refl ha

end ModalityInference.ComparisonPartialCarrier
