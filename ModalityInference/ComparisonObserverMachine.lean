import ModalityInference.ComparisonStructuralLayout

/-! Finite-state observers evaluate finite type expressions by structural
recursion. State cycles do not introduce recursive type terms. -/
namespace ModalityInference.ComparisonObserverMachine

open ComparisonStructuralLayout (Constructor)

structure Branch (State : Type) where
  left : Bool
  next : State

structure Node (State : Type) where
  atom : TypeVar → Bool
  unitValue : Bool
  creditValue : Bool
  action : ModExpr → Bool → Bool
  branch : Constructor → Branch State
  range : Bool → Bool

abbrev Machine (count : Nat) := Fin count → Node (Fin count)

def sign (kind : Constructor) (left : Bool) (x : Bool) : Bool :=
  if left && kind.dual then !x else x

def value {State : Type} (nodes : State → Node State) : CompareTy → State → Bool
  | .var v, i => (nodes i).atom v
  | .unit, i => (nodes i).unitValue
  | .credit, i => (nodes i).creditValue
  | .prod a b, i =>
      let br := (nodes i).branch .prod
      if br.left then value nodes a br.next else value nodes b br.next
  | .sum a b, i =>
      let br := (nodes i).branch .sum
      if br.left then value nodes a br.next else value nodes b br.next
  | .fn a b, i =>
      let br := (nodes i).branch .fn
      if br.left then !(value nodes a br.next) else value nodes b br.next
  | .modal a m, i => (nodes i).action m (value nodes a i)
  | .join a b, i => value nodes a i || value nodes b i
  | .meet a b, i => value nodes a i && value nodes b i

def branchValue {State : Type} (nodes : State → Node State)
    (i : State) (kind : Constructor) (a b : CompareTy) : Bool :=
  let br := (nodes i).branch kind
  if br.left then sign kind true (value nodes a br.next) else value nodes b br.next

end ModalityInference.ComparisonObserverMachine
