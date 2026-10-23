import ModalityInference.Proofs.ComparisonRawHeadFiniteOrbits
import ModalityInference.Proofs.ComparisonRawCarrierHeterogeneous
import ModalityInference.ComparisonStructuralLayout

/-! Recorded constructor heads give finite row families on the head orbit.
Product and sum inputs carry the row's control; function inputs remain at the
unit control, and their domain is contravariant. -/
namespace ModalityInference.ComparisonRawHeadFiniteRows

open ComparisonRawHeadFiniteOrbits ComparisonFiniteControls ComparisonStructuralLayout

noncomputable section

variable {Δ : Bounds} (B : Boundary Δ)

structure HeadRow (k : Constructor) where
  left : Fin B.heads.length
  right : Fin B.heads.length
  output : Fin B.heads.length
  equation : B.heads[output] = k.op B.heads[left] B.heads[right]

namespace HeadRow

variable {B} {k : Constructor} {names : List ModVar}

@[ext] theorem ext {r s : HeadRow B k} (hl : r.left = s.left)
    (hr : r.right = s.right) (ho : r.output = s.output) : r = s := by
  cases r; cases s; cases hl; cases hr; cases ho; rfl

instance : Finite (HeadRow B k) :=
  Finite.of_injective (fun r : HeadRow B k => (r.left,r.right,r.output))
    (fun _ _ h => ext (congrArg Prod.fst h)
      (congrArg (fun p => p.2.1) h) (congrArg (fun p => p.2.2) h))

instance : Fintype (HeadRow B k) := Fintype.ofFinite _

def atLeft (r : HeadRow B k) (m : Control Δ names) : Point B names := ⟨r.left,m⟩
def atRight (r : HeadRow B k) (m : Control Δ names) : Point B names := ⟨r.right,m⟩
def atOutput (r : HeadRow B k) (m : Control Δ names) : Point B names := ⟨r.output,m⟩

theorem pair_cross (hk : k = .prod ∨ k = .sum)
    {m n : Control Δ names} (hmn : m ≤ n) (r s : HeadRow B k)
    (hax : r.atLeft m ≤ s.atLeft n) (hby : r.atRight m ≤ s.atRight n) :
    r.atOutput m ≤ s.atOutput n := by
  change AlgebraSubtype Δ (.modal B.heads[r.output] (expression m))
    (.modal B.heads[s.output] (expression n))
  rw [r.equation,s.equation]
  rcases hk with rfl | rfl
  · exact AlgebraSubtype.prod_ordered ((le_iff_submode m n).mp hmn) hax hby
  · exact AlgebraSubtype.sum_ordered ((le_iff_submode m n).mp hmn) hax hby

theorem fn_cross {m n : Control Δ names} (hmn : FutureLe m n)
    (r s : HeadRow B .fn)
    (hxa : Point.base B names s.left ≤ Point.base B names r.left)
    (hby : Point.base B names r.right ≤ Point.base B names s.right) :
    r.atOutput m ≤ s.atOutput n := by
  change AlgebraSubtype Δ (.modal B.heads[r.output] (expression m))
    (.modal B.heads[s.output] (expression n))
  rw [r.equation,s.equation]
  exact .fn ((Point.base_le_iff s.left r.left).mp hxa)
    ((Point.base_le_iff r.right s.right).mp hby) ((futureLe_iff_submode m n).mp hmn)

theorem fn_output_equivalent (r : HeadRow B .fn) (m : Control Δ names) :
    AlgebraSubtype Δ (r.atOutput m).term
      (.modal (.fn (Point.base B names r.left).term (Point.base B names r.right).term)
        (expression m)) ∧
    AlgebraSubtype Δ
      (.modal (.fn (Point.base B names r.left).term (Point.base B names r.right).term)
        (expression m)) (r.atOutput m).term := by
  change AlgebraSubtype Δ (.modal B.heads[r.output] (expression m)) _ ∧
    AlgebraSubtype Δ _ (.modal B.heads[r.output] (expression m))
  rw [r.equation]
  exact ⟨.fn (Point.base_equivalent r.left).1 (Point.base_equivalent r.right).2
      ((futureLe_iff_submode m m).mp (le_future_self m)),
    .fn (Point.base_equivalent r.left).2 (Point.base_equivalent r.right).1
      ((futureLe_iff_submode m m).mp (le_future_self m))⟩

end HeadRow

variable {B} {names : List ModVar}

def PairRow (k : Constructor) (m : Control Δ names) (a b c : Point B names) : Prop :=
  ∃ r : HeadRow B k, a = r.atLeft m ∧ b = r.atRight m ∧ c = r.atOutput m

def FnRow (m : Control Δ names) (a b c : Point B names) : Prop :=
  ∃ r : HeadRow B .fn, a = Point.base B names r.left ∧
    b = Point.base B names r.right ∧ c = r.atOutput m

theorem pair_cross {k : Constructor} (hk : k = .prod ∨ k = .sum)
    {m n : Control Δ names} {a b c x y z : Point B names} (hmn : m ≤ n)
    (hr : PairRow k m a b c) (hs : PairRow k n x y z) (hax : a ≤ x) (hby : b ≤ y) :
    c ≤ z := by
  obtain ⟨r,rfl,rfl,rfl⟩ := hr
  obtain ⟨s,rfl,rfl,rfl⟩ := hs
  exact HeadRow.pair_cross hk hmn r s hax hby

theorem fn_cross {m n : Control Δ names} {a b c x y z : Point B names}
    (hmn : FutureLe m n) (hr : FnRow m a b c) (hs : FnRow n x y z)
    (hxa : x ≤ a) (hby : b ≤ y) : c ≤ z := by
  obtain ⟨r,rfl,rfl,rfl⟩ := hr
  obtain ⟨s,rfl,rfl,rfl⟩ := hs
  exact HeadRow.fn_cross hmn r s hxa hby

end
end ModalityInference.ComparisonRawHeadFiniteRows
