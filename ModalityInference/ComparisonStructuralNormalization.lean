import ModalityInference.ComparisonConstructorNormalization
import ModalityInference.ComparisonStructuralBasis
import ModalityInference.ComparisonStructuralActions
import ModalityInference.ComparisonLatticeCompiler

/-! Whole endpoints normalize by following their syntax and their solved shape.
Constructor distribution and signed-control actions use the same finite bases;
no choices of type representatives or Boolean worlds are performed. -/
namespace ModalityInference.ComparisonStructuralNormalization

open ComparisonControls ComparisonStructuralBasis ComparisonPropagation

def constructor (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (s t : ComparisonShape)
    (op : CompareTy → CompareTy → CompareTy) (sign : Bool → Bool)
    (a b : CompareTy) : RunResult CompareTy :=
  match basis names modes shapes s, basis names modes shapes t with
  | some left, some right =>
      match ComparisonConstructorNormalization.lift op sign left.types right.types a b with
      | some c => .success c
      | none => .rejected "constructor operand is outside its finite lattice basis"
  | _, _ => .rejected "constructor operand has no finite basis"

def modal (fuel : Nat) (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (shape : ComparisonShape)
    (a : CompareTy) (m : ModExpr) : RunResult CompareTy :=
  match basis names modes shapes shape with
  | none => .rejected "modal operand has no finite basis"
  | some b =>
      match ComparisonLatticeCompiler.compile b a with
      | none => .rejected "modal operand is outside its finite lattice basis"
      | some input => do
          let action ← ComparisonStructuralActions.prepareAction fuel b m
          match reify b.types (action.apply input) with
          | some t => .success t
          | none => .rejected "modal polynomial has no finite type realization"

def run (fuel : Nat) (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) : CompareTy → RunResult CompareTy
  | a@(.var _) | a@(.unit) | a@(.credit) => .success a
  | .prod a b => do
      let x ← run fuel names modes shapes a
      let y ← run fuel names modes shapes b
      constructor names modes shapes (a.shape.subst shapes) (b.shape.subst shapes)
        .prod id x y
  | .sum a b => do
      let x ← run fuel names modes shapes a
      let y ← run fuel names modes shapes b
      constructor names modes shapes (a.shape.subst shapes) (b.shape.subst shapes)
        .sum id x y
  | .fn a b => do
      let x ← run fuel names modes shapes a
      let y ← run fuel names modes shapes b
      constructor names modes shapes (a.shape.subst shapes) (b.shape.subst shapes)
        .fn Bool.not x y
  | .join a b => do
      return .join (← run fuel names modes shapes a) (← run fuel names modes shapes b)
  | .meet a b => do
      return .meet (← run fuel names modes shapes a) (← run fuel names modes shapes b)
  | .modal a m => do
      let x ← run fuel names modes shapes a
      modal fuel names modes shapes (a.shape.subst shapes) x m

end ModalityInference.ComparisonStructuralNormalization
