import ModalityInference.Proofs.ComparisonModeRestriction
import ModalityInference.Proofs.ComparisonAlgebraReification

/-! A total modality action fixing the ambient bounds induces a lattice
endomorphism on each defined comparison shape. Precomposition transports one
actual observer, preserving all correlations between the observed type images. -/
namespace ModalityInference.ComparisonObserverModePullback

open ComparisonAlgebra ComparisonModeRestriction

def carrier {Δ : Bounds} {ms : ModVar → ModExpr} {shape : ComparisonShape}
    (h : Fixed Δ ms) (a : Carrier Δ shape) : Carrier Δ shape where
  type := a.type.subst CompareTy.var ms
  shaped := (a.type.wellShaped_subst_modes_iff ms).mpr a.shaped
  defined := h.type_defined a.defined
  shape_eq := by simpa only [CompareTy.shape_subst_modes] using a.shape_eq

theorem representable {Δ : Bounds} {ms : ModVar → ModExpr} {shape : ComparisonShape}
    (h : Fixed Δ ms) {a : CompareTy} (ha : Representable Δ shape a) :
    Representable Δ shape (a.subst CompareTy.var ms) :=
  ⟨(a.wellShaped_subst_modes_iff ms).mpr ha.1,h.type_defined ha.2.1,
    by simpa only [CompareTy.shape_subst_modes] using ha.2.2⟩

noncomputable def order {Δ : Bounds} {ms : ModVar → ModExpr} {shape : ComparisonShape}
    (h : Fixed Δ ms) : LatticeHom (Order Δ shape) (Order Δ shape) where
  toFun := Quotient.lift (fun a : Carrier Δ shape => Order.of (carrier h a)) (by
    intro a b hab
    exact Quotient.sound ⟨h.algebra hab.1,h.algebra hab.2⟩)
  map_sup' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rfl
  map_inf' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rfl

@[simp] theorem order_of {Δ : Bounds} {ms : ModVar → ModExpr} {shape : ComparisonShape}
    (h : Fixed Δ ms) (a : Carrier Δ shape) :
    order h (Order.of a) = Order.of (carrier h a) := rfl

noncomputable def observer {Δ : Bounds} {ms : ModVar → ModExpr} {shape : ComparisonShape}
    (h : Fixed Δ ms) (f : LatticeHom (Order Δ shape) Bool) : LatticeHom (Order Δ shape) Bool :=
  f.comp (order h)

@[simp] theorem observer_of {Δ : Bounds} {ms : ModVar → ModExpr} {shape : ComparisonShape}
    (h : Fixed Δ ms) (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape) :
    observer h f (Order.of a) = f (Order.of (carrier h a)) := rfl

theorem observer_value {Δ : Bounds} {ms : ModVar → ModExpr} {shape : ComparisonShape}
    (h : Fixed Δ ms) (f : LatticeHom (Order Δ shape) Bool)
    {a : CompareTy} (ha : Representable Δ shape a) :
    booleanValue (observer h f) a = booleanValue f (a.subst CompareTy.var ms) := by
  rw [booleanValue_represented _ a ha,
    booleanValue_represented _ _ (representable h ha)]
  rfl

end ModalityInference.ComparisonObserverModePullback
