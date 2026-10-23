import ModalityInference.Proofs.ComparisonRelativeMixedRows

/-! Same-index shadow inequalities and cross-index boundary compatibility
combine all defined and boundary rows into one ordered family of tables. -/
namespace ModalityInference.ComparisonRelativeIndexedRows

open ComparisonRelativeIntervals ComparisonRelativeMixedRows

section Relational

variable {D P Index : Type*} [Lattice D] [Preorder P]

structure Compatibility (I : IntervalData D P) (p q : Bool)
    (le : Index → Index → Prop) (f : Index → D → D → D)
    (rows : Index → P → P → P → Prop) : Prop where
  compatible : ∀ m, ComparisonRelativeMixedRows.Compatibility I p q (f m) (rows m)
  defined_index : ∀ {m n}, le m n → ∀ a b, f m a b ≤ f n a b
  boundary_cross : ∀ {m n a b c x y z}, le m n → rows m a b c → rows n x y z →
    Direction (· ≤ ·) p a x → Direction (· ≤ ·) q b y → c ≤ z

namespace Compatibility

variable {I : IntervalData D P} {p q : Bool} {le : Index → Index → Prop}
  {f : Index → D → D → D} {rows : Index → P → P → P → Prop}
  (h : Compatibility I p q le f rows)

include h

/-- The source index supplies an upper shadow and the target index supplies a
lower shadow. No extra cross-index shadow hypotheses are needed. -/
theorem mono {m n a b c x y z} (hmn : le m n)
    (habc : MixedRow (f m) (rows m) a b c) (hxyz : MixedRow (f n) (rows n) x y z)
    (hax : Direction I.Rel p a x) (hby : Direction I.Rel q b y) : I.Rel c z := by
  cases habc with
  | defined a b =>
    cases hxyz with
    | defined x y =>
      exact ((h.compatible m).defined_mono hax hby).trans (h.defined_index hmn x y)
    | boundary hr =>
      exact I.rel_trans (y := .inl (f n a b)) (h.defined_index hmn a b)
        ((h.compatible n).defined_partial hr hax hby)
  | boundary hr =>
    cases hxyz with
    | defined x y =>
      exact I.rel_trans ((h.compatible m).partial_defined hr hax hby) (h.defined_index hmn x y)
    | boundary hs => exact h.boundary_cross hmn hr hs hax hby

end Compatibility
end Relational

section Embedding

variable {D P Index : Type*} [DistribLattice D] [Preorder P]
  {I : IntervalData D P} {p q : Bool} {le : Index → Index → Prop}
  {f : Index → D → D → D} {rows : Index → P → P → P → Prop}

namespace Compatibility

def table (h : Compatibility I p q le f rows) (hrefl : ∀ m, le m m)
    (htrans : ∀ {m n r}, le m n → le n r → le m r) :
    ComparisonRelativeTables.IndexedTable I.embed Index p q where
  table m := (h.compatible m).table
  le := le
  refl := hrefl
  trans := htrans
  cross_mono hmn habc hxyz hax hby := (I.embed_le_iff _ _).mpr
    (h.mono hmn habc hxyz ((embedded_direction_iff p _ _).mp hax)
      ((embedded_direction_iff q _ _).mp hby))

theorem extend_defined (h : Compatibility I p q le f rows) (hrefl : ∀ m, le m m)
    (htrans : ∀ {m n r}, le m n → le n r → le m r) (m : Index) (a b : D) :
    (h.table hrefl htrans).extend m (I.embed (.inl a)) (I.embed (.inl b)) =
      I.embed (.inl (f m a b)) :=
  (h.table hrefl htrans).extend_recorded (.defined a b)

theorem extend_boundary (h : Compatibility I p q le f rows) (hrefl : ∀ m, le m m)
    (htrans : ∀ {m n r}, le m n → le n r → le m r)
    {m : Index} {a b c : P} (hr : rows m a b c) :
    (h.table hrefl htrans).extend m (I.embed (.inr a)) (I.embed (.inr b)) =
      I.embed (.inr c) :=
  (h.table hrefl htrans).extend_recorded (.boundary hr)

end Compatibility
end Embedding
end ModalityInference.ComparisonRelativeIndexedRows
