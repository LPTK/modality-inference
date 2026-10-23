import ModalityInference.Proofs.ComparisonRawCarrierRestriction

/-! Monotone operations on the capsule-supported comparison subcalculus. -/
namespace ModalityInference.ComparisonRawCarrierRestriction

open ComparisonRawCarrierIdeals

def modalMap (Δ : Bounds) (K : Set Token) (m : ModExpr) (hm : Entails Δ (.defined m)) :
    Map (core Δ K) where
  toFun a := .modal a m
  carrier := (carrier_modal_total hm).mpr
  shaped h := h
  shape _ _ _ := rfl
  mono h := .congr h (.refl hm)

def prodMap (Δ : Bounds) (K : Set Token) : BinaryMap (core Δ K) false false where
  toFun := .prod
  carrier ha hb := carrier_prod.mpr ⟨ha,hb⟩
  shaped ha hb := ⟨ha,hb⟩
  separate h := ⟨fun ρ hρ => (ComparisonShape.prod.inj (h ρ hρ)).1,
    fun ρ hρ => (ComparisonShape.prod.inj (h ρ hρ)).2⟩
  mono := Derivation.prod_congr

def sumMap (Δ : Bounds) (K : Set Token) : BinaryMap (core Δ K) false false where
  toFun := .sum
  carrier ha hb := carrier_sum.mpr ⟨ha,hb⟩
  shaped ha hb := ⟨ha,hb⟩
  separate h := ⟨fun ρ hρ => (ComparisonShape.sum.inj (h ρ hρ)).1,
    fun ρ hρ => (ComparisonShape.sum.inj (h ρ hρ)).2⟩
  mono := Derivation.sum_congr

def fnMap (Δ : Bounds) (K : Set Token) : BinaryMap (core Δ K) true false where
  toFun := .fn
  carrier ha hb := carrier_fn.mpr ⟨ha,hb⟩
  shaped ha hb := ⟨ha,hb⟩
  separate h := ⟨fun ρ hρ => (ComparisonShape.fn.inj (h ρ hρ)).1,
    fun ρ hρ => (ComparisonShape.fn.inj (h ρ hρ)).2⟩
  mono := Derivation.fn_congr

end ModalityInference.ComparisonRawCarrierRestriction
