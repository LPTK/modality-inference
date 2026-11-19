import ModalityInference.Proofs.ComparisonExecutableTables
import ModalityInference.Proofs.ComparisonRelativeCoordinates

/-! Executable row extensions preserve the monotone-coordinate invariant.
Their proof fields erase; evaluating them calls only the finite Boolean row
algorithm, while the agreement theorems identify the semantic constructors. -/
namespace ModalityInference.ComparisonExecutableTables

open ComparisonRelativeTables ComparisonRelativeCoordinates

variable {M A O : Type*} [PartialOrder M]
  (observations : List O) (hobs : ∀ o, o ∈ observations)
  (embed : A → O → Bool) (le : M → M → Bool) (rows : List (Row M A))
  (hrefl : ∀ m, le m m = true)
  (htrans : ∀ {m n r}, le m n = true → le n r = true → le m r = true)
  (horder : ∀ {m n}, m ≤ n → le m n = true)

def pair (hcheck : check observations embed le false false rows = true)
    (X Y : Coordinates M (O → Bool)) : Coordinates M (O → Bool) where
  toFun m := extend observations embed le false false rows m (X m) (Y m)
  monotone' m n h := by
    dsimp only
    rw [extend_eq observations hobs embed le false false rows hrefl htrans hcheck,
      extend_eq observations hobs embed le false false rows hrefl htrans hcheck]
    exact (table observations hobs embed le false false rows hrefl htrans hcheck).extend_mono
      (horder h) (X.monotone h) (Y.monotone h)

theorem pair_eq (hcheck : check observations embed le false false rows = true)
    (X Y : Coordinates M (O → Bool)) :
    pair observations hobs embed le rows hrefl htrans horder hcheck X Y =
      ComparisonRelativeCoordinates.pair (table observations hobs embed le false false rows hrefl htrans hcheck)
        horder X Y := by
  ext m o
  exact congrFun (extend_eq observations hobs embed le false false rows hrefl htrans hcheck m (X m) (Y m)) o

def fn [One M] (hcheck : check observations embed le true false rows = true)
    (X Y : Coordinates M (O → Bool)) : Coordinates M (O → Bool) where
  toFun m := extend observations embed le true false rows m (X 1) (Y 1)
  monotone' m n h := by
    dsimp only
    rw [extend_eq observations hobs embed le true false rows hrefl htrans hcheck,
      extend_eq observations hobs embed le true false rows hrefl htrans hcheck]
    exact (table observations hobs embed le true false rows hrefl htrans hcheck).extend_mono
      (horder h) (Direction.refl _ _) (Direction.refl _ _)

theorem fn_eq [One M] (hcheck : check observations embed le true false rows = true)
    (X Y : Coordinates M (O → Bool)) :
    fn observations hobs embed le rows hrefl htrans horder hcheck X Y =
      ComparisonRelativeCoordinates.fn (table observations hobs embed le true false rows hrefl htrans hcheck)
        horder X Y := by
  ext m o
  exact congrFun (extend_eq observations hobs embed le true false rows hrefl htrans hcheck m (X 1) (Y 1)) o

end ModalityInference.ComparisonExecutableTables
