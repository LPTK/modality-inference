import ModalityInference.ComparisonSignedSynthesis
import ModalityInference.ComparisonInputAction
import ModalityInference.ComparisonSelectedAction

/-! Every input binder's finite shape alternatives have fixed basis keys. Equal
shapes share a key; the common shape selectors choose which image is returned. -/
namespace ModalityInference.ComparisonSignedBranchImages
open ComparisonSelectedBases

abbrev Entry := Nat × Branch

def entries (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : List Entry :=
  (inputTypeKeys p).flatMap fun name =>
    (prepared first p solved (.flex name)).map fun branch => (name,branch)

def locate (name : Nat) (shape : ComparisonShape) : List Entry → Option Nat
  | [] => none
  | entry::rest => if entry.1==name && entry.2.shape==shape then some 0
      else (locate name shape rest).map (·+1)

def input (table : List Entry) : ComparisonSignedSynthesis.Input where
  keys := List.range table.length
  bases key := ((table[key]?).map (fun entry=>entry.2.basis.types)).getD []

def pick (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool)
    (images : List (Nat × CompareTy)) (name : Nat) : Option CompareTy := do
  let branch ← enabled world (prepared first p solved (.flex name))
  let key ← locate name branch.shape (entries first p solved)
  images.lookup key

def select (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool)
    (images : List (Nat × CompareTy)) (modes : List (Nat × ModExpr)) : Option CompareSubstitution := do
  let selected ← (inputTypeKeys p).mapM fun name=>do
    let raw ← pick first p solved world images name
    return (name,raw.subst CompareTy.var ({modes := modes} : CompareSubstitution).mode)
  return ⟨selected,modes⟩

end ModalityInference.ComparisonSignedBranchImages
