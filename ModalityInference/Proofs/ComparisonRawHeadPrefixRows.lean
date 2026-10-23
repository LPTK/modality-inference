import ModalityInference.Proofs.ComparisonRawHeadFiniteRows
import ModalityInference.Proofs.ComparisonRelativeTables

/-! A literal inherited prefix has only recorded boundary rows. These rows
retain the exact prefix on both inputs and on the constructor output; their
finite extension does not impose a defined constructor equation at that prefix. -/
namespace ModalityInference.ComparisonRawHeadPrefixRows

open ComparisonRawHeadFiniteOrbits ComparisonFiniteControls ComparisonStructuralLayout
  ComparisonRelativeIntervals ComparisonRelativeTables

noncomputable section

variable {Δ : Bounds} (B : Boundary Δ)

structure HeadRow (k : Constructor) (pref : ModExpr) where
  left : Fin B.heads.length
  right : Fin B.heads.length
  output : Fin B.heads.length
  equation : ∃ a b, B.heads[left] = .modal a pref ∧
    B.heads[right] = .modal b pref ∧ B.heads[output] = .modal (k.op a b) pref

namespace HeadRow

variable {B} {k : Constructor} {pref : ModExpr} {names : List ModVar}

@[ext] theorem ext {r s : HeadRow B k pref} (hl : r.left = s.left)
    (hr : r.right = s.right) (ho : r.output = s.output) : r = s := by
  cases r; cases s; cases hl; cases hr; cases ho; rfl

instance : Finite (HeadRow B k pref) :=
  Finite.of_injective (fun r : HeadRow B k pref => (r.left,r.right,r.output))
    (fun _ _ h => ext (congrArg Prod.fst h)
      (congrArg (fun p => p.2.1) h) (congrArg (fun p => p.2.2) h))

instance : Fintype (HeadRow B k pref) := Fintype.ofFinite _

def atLeft (r : HeadRow B k pref) (m : Control Δ names) : Point B names := ⟨r.left,m⟩
def atRight (r : HeadRow B k pref) (m : Control Δ names) : Point B names := ⟨r.right,m⟩
def atOutput (r : HeadRow B k pref) (m : Control Δ names) : Point B names := ⟨r.output,m⟩

theorem cross (hk : k = .prod ∨ k = .sum)
    {m n : Control Δ names} (hmn : m ≤ n) (r s : HeadRow B k pref)
    (hax : r.atLeft m ≤ s.atLeft n) (hby : r.atRight m ≤ s.atRight n) :
    r.atOutput m ≤ s.atOutput n := by
  obtain ⟨a,b,ha,hb,hc⟩ := r.equation
  obtain ⟨x,y,hx,hy,hz⟩ := s.equation
  change AlgebraSubtype Δ (.modal B.heads[r.left] (expression m))
    (.modal B.heads[s.left] (expression n)) at hax
  change AlgebraSubtype Δ (.modal B.heads[r.right] (expression m))
    (.modal B.heads[s.right] (expression n)) at hby
  change AlgebraSubtype Δ (.modal B.heads[r.output] (expression m))
    (.modal B.heads[s.output] (expression n))
  rw [ha,hx] at hax
  rw [hb,hy] at hby
  rw [hc,hz]
  rcases hk with rfl | rfl
  · exact AlgebraSubtype.prod_prefix_ordered ((le_iff_submode m n).mp hmn) hax hby
  · exact AlgebraSubtype.sum_prefix_ordered ((le_iff_submode m n).mp hmn) hax hby

end HeadRow

variable {B} {names : List ModVar}

def Row (k : Constructor) (pref : ModExpr) (m : Control Δ names)
    (a b c : Point B names) : Prop :=
  ∃ r : HeadRow B k pref, a = r.atLeft m ∧ b = r.atRight m ∧ c = r.atOutput m

theorem row_cross {k : Constructor} {pref : ModExpr} (hk : k = .prod ∨ k = .sum)
    {m n : Control Δ names} {a b c x y z : Point B names} (hmn : m ≤ n)
    (hr : Row k pref m a b c) (hs : Row k pref n x y z) (hax : a ≤ x) (hby : b ≤ y) :
    c ≤ z := by
  obtain ⟨r,rfl,rfl,rfl⟩ := hr
  obtain ⟨s,rfl,rfl,rfl⟩ := hs
  exact HeadRow.cross hk hmn r s hax hby

/-- Every active literal prefix is visible at the root of a listed head. -/
def prefixes (B : Boundary Δ) : List ModExpr := B.heads.filterMap fun a =>
  match a with
  | .modal _ pref => some pref
  | _ => none

theorem prefix_mem {k : Constructor} {pref : ModExpr} (r : HeadRow B k pref) :
    pref ∈ prefixes B := by
  obtain ⟨a,b,ha,hb,hc⟩ := r.equation
  apply List.mem_filterMap.mpr
  refine ⟨B.heads[r.left],List.getElem_mem r.left.isLt,?_⟩
  rw [ha]

theorem row_prefix_mem {k : Constructor} {pref : ModExpr} {m : Control Δ names}
    {a b c : Point B names} (hr : Row k pref m a b c) : pref ∈ prefixes B :=
  prefix_mem hr.choose

section Table

variable {D : Type*} [DistribLattice D]
    (I : IntervalData D (Point B names))

/-- Only boundary entries are included. In particular, no all-defined rows are
added at a literal partial prefix. -/
inductive Entry (k : Constructor) (pref : ModExpr) (m : Control Δ names) :
    (D ⊕ Point B names) → (D ⊕ Point B names) → (D ⊕ Point B names) → Prop
  | boundary {a b c} : Row k pref m a b c → Entry k pref m (.inr a) (.inr b) (.inr c)

omit [DistribLattice D] in
theorem entry_prefix_mem {k : Constructor} {pref : ModExpr} {m : Control Δ names}
    {a b c : D ⊕ Point B names} (hr : Entry k pref m a b c) : pref ∈ prefixes B := by
  cases hr with
  | boundary hr => exact row_prefix_mem hr

theorem entry_cross {k : Constructor} {pref : ModExpr} (hk : k = .prod ∨ k = .sum)
    {m n : Control Δ names} {a b c x y z : D ⊕ Point B names} (hmn : m ≤ n)
    (hr : Entry k pref m a b c) (hs : Entry k pref n x y z)
    (hax : Direction false (I.embed a) (I.embed x))
    (hby : Direction false (I.embed b) (I.embed y)) : I.embed c ≤ I.embed z := by
  cases hr with
  | boundary hr =>
    cases hs with
    | boundary hs =>
      exact (I.embed_le_iff _ _).mpr (row_cross hk hmn hr hs
        ((I.embed_le_iff _ _).mp hax) ((I.embed_le_iff _ _).mp hby))

def indexedTable {k : Constructor} (hk : k = .prod ∨ k = .sum) (pref : ModExpr) :
    IndexedTable I.embed (Control Δ names) false false where
  table m := {
    entry := Entry k pref m
    mono := entry_cross I hk (le_refl m) }
  le := (· ≤ ·)
  refl := le_refl
  trans := le_trans
  cross_mono := entry_cross I hk

theorem extend_recorded {k : Constructor} (hk : k = .prod ∨ k = .sum) {pref : ModExpr}
    {m : Control Δ names} {a b c : Point B names} (hr : Row k pref m a b c) :
    (indexedTable I hk pref).extend m (I.embed (.inr a)) (I.embed (.inr b)) =
      I.embed (.inr c) :=
  (indexedTable I hk pref).extend_recorded (.boundary hr)

theorem extend_eq_bot_of_not_mem {k : Constructor} (hk : k = .prod ∨ k = .sum)
    {pref : ModExpr} (hp : pref ∉ prefixes B) (m : Control Δ names)
    (x y : I.Completion) :
    (indexedTable I hk pref).extend m x y = ⊥ := by
  funext o
  apply decide_eq_false_iff_not.mpr
  rintro ⟨r,a,b,c,hm,hr,hx,hy,hc⟩
  exact hp (entry_prefix_mem hr)

end Table
end
end ModalityInference.ComparisonRawHeadPrefixRows
