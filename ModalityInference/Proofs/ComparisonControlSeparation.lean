import ModalityInference.Proofs.ComparisonAlgebraOrder
import ModalityInference.Proofs.ComparisonControls

/-! Boolean observers of the guarded modal lattice. The endpoint bands select
the four coordinate actions used by the comparison compiler. -/
namespace ModalityInference.ComparisonAlgebra

namespace Carrier

variable {Δ : Bounds} {shape : ComparisonShape}

def modal (a : Carrier Δ shape) (m : ModExpr) (hm : DefinedMode Δ m) : Carrier Δ shape where
  type := .modal a.type m
  shaped := a.shaped
  defined := by
    intro η hη c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact a.defined η hη c hc
    · obtain rfl := List.mem_singleton.mp hc
      exact hm η hη
  shape_eq := a.shape_eq

def atMode (a : Carrier Δ shape) (m : Mode) : Carrier Δ shape :=
  a.modal (.const m) (fun _ _ => rfl)

theorem modal_le {a b : Carrier Δ shape} {m n : ModExpr}
    {hm : DefinedMode Δ m} {hn : DefinedMode Δ n} (hab : a ≤ b) (hmn : Submode Δ m n) :
    a.modal m hm ≤ b.modal n hn := .congr hab hmn

theorem atMode_le {a b : Carrier Δ shape} {m n : Mode}
    (hab : a ≤ b) (hmn : m.le n = true) : a.atMode m ≤ b.atMode n :=
  modal_le hab (.valid fun _ _ => ⟨m, n, rfl, rfl, hmn⟩)

theorem atMode_identity (a : Carrier Δ shape) :
    Order.of (a.atMode Mode.identity) = Order.of a :=
  Quotient.sound ⟨.shaped (.identity a.shaped), .shaped (.identityRev a.shaped)⟩

theorem atMode_join (a : Carrier Δ shape) (m n : Mode) :
    Order.of (a.atMode (m.join n)) =
      Order.of (a.atMode m) ⊔ Order.of (a.atMode n) := by
  apply Quotient.sound
  have he : Equation Δ (.modal a.type (.join (.const m) (.const n)))
      (.join (.modal a.type (.const m)) (.modal a.type (.const n))) :=
    .scalar true a.shaped a.defined (fun _ _ => rfl) (fun _ _ => rfl)
  refine ⟨?_, ?_⟩
  · exact (AlgebraSubtype.congr (.refl a.shaped) (.valid fun _ _ =>
      ⟨m.join n, m.join n, rfl, rfl, Mode.le_refl _⟩)).trans (.equation he)
  · exact (AlgebraSubtype.equationRev he).trans
      (.congr (.refl a.shaped) (.valid fun _ _ =>
        ⟨m.join n, m.join n, rfl, rfl, Mode.le_refl _⟩))

theorem raised_le_floor {a b : Carrier Δ shape} (hab : a ≤ b)
    (k : Mode) (hk : (Mode.bottom.compose Mode.top).le (Mode.top.compose k) = true) :
    (a.atMode Mode.bottom).atMode Mode.top ≤ (b.atMode Mode.top).atMode k :=
  (AlgebraSubtype.shaped (.compose a.shaped)).trans
    ((AlgebraSubtype.congr hab (.valid fun _ _ => ⟨_, _, rfl, rfl, hk⟩)).trans
      (.shaped (.composeRev b.shaped)))

end Carrier

def observer (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape) : Bool :=
  f (Order.of a)

theorem observer_join (f : LatticeHom (Order Δ shape) Bool) (a b : Carrier Δ shape) :
    observer f (a.join b) = (observer f a || observer f b) :=
  f.map_sup' (Order.of a) (Order.of b)

theorem observer_meet (f : LatticeHom (Order Δ shape) Bool) (a b : Carrier Δ shape) :
    observer f (a.meet b) = (observer f a && observer f b) :=
  f.map_inf' (Order.of a) (Order.of b)

theorem observer_mono (f : LatticeHom (Order Δ shape) Bool)
    {a b : Carrier Δ shape} (hab : a ≤ b) : observer f a = true → observer f b = true :=
  Bool.le_iff_imp.mp (OrderHomClass.monotone f hab)

/-- A nonconstant observer selects one coordinate band. These four cases are
exactly the compiler's unaffected, locality, affinity, and uniqueness actions. -/
theorem observer_coordinate_cases (f : LatticeHom (Order Δ shape) Bool)
    {a b : Carrier Δ shape} (hab : a ≤ b)
    (ht : observer f (b.atMode Mode.top) = true) :
    let raised := observer f ((a.atMode Mode.bottom).atMode Mode.top)
    let locality := observer f ((b.atMode Mode.top).atMode Mode.global)
    let affine := observer f ((b.atMode Mode.top).atMode Mode.many)
    (raised = false ∧ locality = true ∧ affine = true) ∨
    (raised = false ∧ locality = false ∧ affine = true) ∨
    (raised = false ∧ locality = true ∧ affine = false) ∨
    (raised = true ∧ locality = true ∧ affine = true) := by
  have hrl := observer_mono f (Carrier.raised_le_floor hab Mode.global (by decide))
  have hra := observer_mono f (Carrier.raised_le_floor hab Mode.many (by decide))
  have hla : (observer f ((b.atMode Mode.top).atMode Mode.global) ||
      observer f ((b.atMode Mode.top).atMode Mode.many)) = true := by
    have he := congrArg f ((Carrier.atMode_join (b.atMode Mode.top)
      Mode.global Mode.many).symm.trans (Carrier.atMode_identity (b.atMode Mode.top)))
    exact (f.map_sup' _ _).symm.trans (he.trans ht)
  cases hr : observer f ((a.atMode Mode.bottom).atMode Mode.top) <;>
    cases hl : observer f ((b.atMode Mode.top).atMode Mode.global) <;>
    cases ha : observer f ((b.atMode Mode.top).atMode Mode.many) <;> simp_all

end ModalityInference.ComparisonAlgebra
