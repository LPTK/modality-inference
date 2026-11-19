import Mathlib.Order.Hom.Order
import ModalityInference.Proofs.ComparisonRelativeTables

/-! Ordered coordinates carry total controls by reindexing. Indexed constructor
tables preserve recorded orbits and satisfy the inherited product and function
rules without requiring constructors to commute with the shifts. -/
namespace ModalityInference.ComparisonRelativeCoordinates

abbrev Coordinates (M C : Type*) [Preorder M] [Preorder C] := M →o C

theorem coordinates_finite {M C : Type*} [Preorder M] [Preorder C]
    [Finite M] [Finite C] : Finite (Coordinates M C) := by
  classical
  letI := Fintype.ofFinite M
  letI := Fintype.ofFinite C
  exact Finite.of_injective (fun f : Coordinates M C => (f : M → C)) DFunLike.coe_injective

section Shifts

variable {M C : Type*} [PartialOrder M] [CommMonoid M] [Lattice C]
  (hmul : ∀ a : M, Monotone (a * ·))

def shift (n : M) : LatticeHom (Coordinates M C) (Coordinates M C) where
  toFun A := ⟨fun m => A (n * m), fun _ _ h => A.monotone (hmul n h)⟩
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp] theorem shift_apply (n : M) (A : Coordinates M C) (m : M) :
    shift hmul n A m = A (n * m) := rfl

@[simp] theorem shift_one (A : Coordinates M C) : shift hmul 1 A = A := by
  ext m
  simp only [shift_apply, one_mul]

theorem shift_mul (m n : M) (A : Coordinates M C) :
    shift hmul n (shift hmul m A) = shift hmul (m * n) A := by
  ext k
  simp only [shift_apply, mul_assoc]

theorem shift_order {m n : M} (hmn : m ≤ n) (A : Coordinates M C) :
    shift hmul m A ≤ shift hmul n A := by
  intro k
  apply A.monotone
  simpa only [mul_comm k] using hmul k hmn

end Shifts

section Orbits

variable {M A C : Type*} [Preorder M] [Preorder C]
  (embed : A → C) (act : M → A → A)
  (hindex : ∀ a, Monotone (fun m => embed (act m a)))

def orbit (a : A) : Coordinates M C := ⟨fun m => embed (act m a), hindex a⟩

@[simp] theorem orbit_apply (a : A) (m : M) :
    orbit embed act hindex a m = embed (act m a) := rfl

/-- The identity coordinate prevents the orbit representation from adding an
order comparison. Transport of the base comparison supplies the converse. -/
theorem orbit_le_iff [One M]
    (hunit : ∀ a, embed (act 1 a) = embed a)
    (htransport : ∀ m a b, embed a ≤ embed b → embed (act m a) ≤ embed (act m b))
    (a b : A) : orbit embed act hindex a ≤ orbit embed act hindex b ↔ embed a ≤ embed b := by
  constructor
  · intro h
    have hh : embed (act 1 a) ≤ embed (act 1 b) := h 1
    simpa only [hunit] using hh
  · intro h m
    exact htransport m a b h

end Orbits

section DefinedOrbits

variable {M D C : Type*} [Preorder M] [Lattice D] [Lattice C]

/-- Lattice-preserving defined actions remain lattice-preserving in the
coordinate representation. -/
def latticeOrbit (embed : LatticeHom D C) (act : M → LatticeHom D D)
    (hindex : ∀ a, Monotone (fun m => embed (act m a))) :
    LatticeHom D (Coordinates M C) where
  toFun := orbit embed (fun m => act m) hindex
  map_sup' a b := by
    ext m
    exact (congrArg embed (map_sup (act m) a b)).trans (map_sup embed (act m a) (act m b))
  map_inf' a b := by
    ext m
    exact (congrArg embed (map_inf (act m) a b)).trans (map_inf embed (act m a) (act m b))

end DefinedOrbits

section OrbitShifts

variable {M A C : Type*} [PartialOrder M] [CommMonoid M] [Lattice C]
  (hmul : ∀ a : M, Monotone (a * ·)) (embed : A → C) (act : M → A → A)
  (hindex : ∀ a, Monotone (fun m => embed (act m a)))

theorem shift_orbit
    (hact : ∀ m n a, embed (act m (act n a)) = embed (act (n * m) a))
    (n : M) (a : A) :
    shift hmul n (orbit embed act hindex a) = orbit embed act hindex (act n a) := by
  ext m
  exact (hact m n a).symm

end OrbitShifts

section Tables

open ComparisonRelativeTables

variable {M A O : Type*} [Preorder M] {embed : A → O → Bool}

/-- Covariant constructors use the inputs at the current coordinate. -/
noncomputable def pair (T : IndexedTable embed M false false)
    (hle : ∀ {m n}, m ≤ n → T.le m n)
    (X Y : Coordinates M (O → Bool)) : Coordinates M (O → Bool) where
  toFun m := T.extend m (X m) (Y m)
  monotone' _ _ h := T.extend_mono (hle h) (X.monotone h) (Y.monotone h)

theorem pair_mono (T : IndexedTable embed M false false)
    (hle : ∀ {m n}, m ≤ n → T.le m n)
    {X X' Y Y' : Coordinates M (O → Bool)} (hx : X ≤ X') (hy : Y ≤ Y') :
    pair T hle X Y ≤ pair T hle X' Y' :=
  fun m => T.extend_mono (T.refl m) (hx m) (hy m)

theorem pair_recorded (T : IndexedTable embed M false false)
    (hle : ∀ {m n}, m ≤ n → T.le m n)
    (a b c : M → A)
    (ha : Monotone (fun m => embed (a m)))
    (hb : Monotone (fun m => embed (b m)))
    (hc : Monotone (fun m => embed (c m)))
    (hrow : ∀ m, (T.table m).entry (a m) (b m) (c m)) :
    pair T hle ⟨fun m => embed (a m), ha⟩ ⟨fun m => embed (b m), hb⟩ =
      (⟨fun m => embed (c m), hc⟩ : Coordinates M (O → Bool)) := by
  ext m o
  exact congrFun (T.extend_recorded (hrow m)) o

/-- Function arguments are read at the identity coordinate; the table index
controls only the function result. -/
noncomputable def fn [One M] (T : IndexedTable embed M true false)
    (hle : ∀ {m n}, m ≤ n → T.le m n)
    (X Y : Coordinates M (O → Bool)) : Coordinates M (O → Bool) where
  toFun m := T.extend m (X 1) (Y 1)
  monotone' _ _ h := T.extend_mono (hle h) (Direction.refl _ _) (Direction.refl _ _)

theorem fn_mono [One M] (T : IndexedTable embed M true false)
    (hle : ∀ {m n}, m ≤ n → T.le m n)
    {X X' Y Y' : Coordinates M (O → Bool)} (hx : X' ≤ X) (hy : Y ≤ Y') :
    fn T hle X Y ≤ fn T hle X' Y' :=
  fun m => T.extend_mono (T.refl m) (hx 1) (hy 1)

theorem fn_recorded [One M] (T : IndexedTable embed M true false)
    (hle : ∀ {m n}, m ≤ n → T.le m n)
    {X Y : Coordinates M (O → Bool)} {a b : A} (c : M → A)
    (hc : Monotone (fun m => embed (c m)))
    (hx : X 1 = embed a) (hy : Y 1 = embed b)
    (hrow : ∀ m, (T.table m).entry a b (c m)) :
    fn T hle X Y = (⟨fun m => embed (c m), hc⟩ : Coordinates M (O → Bool)) := by
  ext m o
  change T.extend m (X 1) (Y 1) o = embed (c m) o
  rw [hx, hy, T.extend_recorded (hrow m)]

end Tables

section InheritedRules

open ComparisonRelativeTables

variable {M A O : Type*} [PartialOrder M] [CommMonoid M]
  (hmul : ∀ a : M, Monotone (a * ·)) {embed : A → O → Bool}

/-- Inherited constructor comparisons use the same table at each shifted
coordinate. No equality between a constructor and its shifted inputs is used. -/
theorem pair_inherited (T : IndexedTable embed M false false)
    (hle : ∀ {m n}, m ≤ n → T.le m n) (n : M)
    {X X' Y Y' : Coordinates M (O → Bool)}
    (hx : shift hmul n X ≤ shift hmul n X')
    (hy : shift hmul n Y ≤ shift hmul n Y') :
    shift hmul n (pair T hle X Y) ≤ shift hmul n (pair T hle X' Y') :=
  fun m => T.extend_mono (T.refl (n * m)) (hx m) (hy m)

/-- The function-label comparison must be stable under a common trailing
control, as it is for the original top-adjusted function order. -/
theorem fn_inherited (T : IndexedTable embed M true false)
    (hle : ∀ {m n}, m ≤ n → T.le m n)
    (hpost : ∀ {m n}, T.le m n → ∀ r, T.le (m * r) (n * r))
    {m n : M} (hmn : T.le m n)
    {X X' Y Y' : Coordinates M (O → Bool)} (hx : X' ≤ X) (hy : Y ≤ Y') :
    shift hmul m (fn T hle X Y) ≤ shift hmul n (fn T hle X' Y') :=
  fun r => T.extend_mono (hpost hmn r) (hx 1) (hy 1)

end InheritedRules
end ModalityInference.ComparisonRelativeCoordinates
