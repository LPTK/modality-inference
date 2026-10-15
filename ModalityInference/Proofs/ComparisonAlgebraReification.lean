import ModalityInference.Proofs.ComparisonAlgebraOrder
import ModalityInference.Proofs.ComparisonPropagation

/-! The guarded lattice interpretation extends to a syntactic Boolean reading
of comparison polynomials. This connects reconstructed types to the exact
positive CNFs produced by propagation. -/
namespace ModalityInference.ComparisonAlgebra

def Representable (Δ : Bounds) (shape : ComparisonShape) (a : CompareTy) : Prop :=
  a.WellShaped Δ ∧ a.DefinedUnder Δ ∧ ComparisonShape.Equivalent Δ a.shape shape

def represented {a : CompareTy} (h : Representable Δ shape a) : Carrier Δ shape :=
  ⟨a, h.1, h.2.1, h.2.2⟩

noncomputable def booleanValue (f : LatticeHom (Order Δ shape) Bool) : CompareTy → Bool
  | .join a b => booleanValue f a || booleanValue f b
  | .meet a b => booleanValue f a && booleanValue f b
  | a => by
      classical
      exact if h : Representable Δ shape a then f (Order.of (represented h)) else false

@[simp] theorem booleanValue_join (f : LatticeHom (Order Δ shape) Bool) (a b : CompareTy) :
    booleanValue f (.join a b) = (booleanValue f a || booleanValue f b) := rfl

@[simp] theorem booleanValue_meet (f : LatticeHom (Order Δ shape) Bool) (a b : CompareTy) :
    booleanValue f (.meet a b) = (booleanValue f a && booleanValue f b) := rfl

theorem Representable.left {a b : CompareTy} (h : Representable Δ shape (.join a b)) :
    Representable Δ shape a :=
  ⟨h.1.1, fun η hη c hc => h.2.1 η hη c (List.mem_append_left _ hc), h.2.2⟩

theorem Representable.right {a b : CompareTy} (h : Representable Δ shape (.join a b)) :
    Representable Δ shape b :=
  ⟨h.1.2.1, fun η hη c hc => h.2.1 η hη c (List.mem_append_right _ hc),
    h.1.2.2.symm.trans h.2.2⟩

theorem booleanValue_represented (f : LatticeHom (Order Δ shape) Bool)
    (a : CompareTy) (ha : Representable Δ shape a) :
    booleanValue f a = f (Order.of (represented ha)) := by
  induction a with
  | join a b iha ihb =>
    rw [booleanValue_join, iha ha.left, ihb ha.right]
    exact (f.map_sup' _ _).symm
  | meet a b iha ihb =>
    rw [booleanValue_meet, iha ha.left, ihb ha.right]
    exact (f.map_inf' _ _).symm
  | _ => simp only [booleanValue, dif_pos ha]

theorem booleanValue_carrier (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape) :
    booleanValue f a.type = f (Order.of a) :=
  booleanValue_represented f a.type ⟨a.shaped, a.defined, a.shape_eq⟩

theorem reify_booleanValue {basis : List CompareTy} {clauses : CNF} {a : CompareTy}
    (h : ComparisonPropagation.reify basis clauses = some a)
    (f : LatticeHom (Order Δ shape) Bool) (types : TypeVar → CompareTy) (modes : ModVar → ModExpr) :
    booleanValue f (a.subst types modes) = true ↔
      CNFHolds (ComparisonPropagation.basisValue basis
        (fun t => booleanValue f (t.subst types modes))) clauses :=
  ComparisonPropagation.reify_correct h (fun t => booleanValue f (t.subst types modes))
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem reify_observer {basis : List CompareTy} {clauses : CNF} {a : CompareTy}
    (h : ComparisonPropagation.reify basis clauses = some a)
    (f : LatticeHom (Order Δ shape) Bool) (types : TypeVar → CompareTy) (modes : ModVar → ModExpr)
    (ha : Representable Δ shape (a.subst types modes)) :
    f (Order.of (represented ha)) = true ↔
      CNFHolds (ComparisonPropagation.basisValue basis
        (fun t => booleanValue f (t.subst types modes))) clauses := by
  rw [← booleanValue_represented f _ ha]
  exact reify_booleanValue h f types modes

/-- Boolean consequences of reified polynomials reflect into the original
guarded derivability relation, including after simultaneous substitution. -/
theorem reify_order {basis : List CompareTy} {left right : CNF} {a b : CompareTy}
    (ha : ComparisonPropagation.reify basis left = some a)
    (hb : ComparisonPropagation.reify basis right = some b)
    (types : TypeVar → CompareTy) (modes : ModVar → ModExpr)
    (hsa : Representable Δ shape (a.subst types modes))
    (hsb : Representable Δ shape (b.subst types modes))
    (h : ∀ f : LatticeHom (Order Δ shape) Bool,
      let value := ComparisonPropagation.basisValue basis
        (fun t => booleanValue f (t.subst types modes))
      CNFHolds value left → CNFHolds value right) :
    AlgebraSubtype Δ (a.subst types modes) (b.subst types modes) := by
  apply (subtype_iff_boolean_observers (represented hsa) (represented hsb)).mpr
  intro f
  exact Bool.le_iff_imp.mpr fun hf =>
    (reify_observer hb f types modes hsb).mpr (h f ((reify_observer ha f types modes hsa).mp hf))

end ModalityInference.ComparisonAlgebra
