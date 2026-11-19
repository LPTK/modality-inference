import ModalityInference.ComparisonObserverMachineCheck

/-! Finite Boolean vectors and executable operations for a described observer
machine. Range membership is checked separately from evaluating an operation. -/
namespace ModalityInference.ComparisonObserverRangeEncoding

open ComparisonObserverMachine ComparisonObserverMachineCheck ComparisonStructuralLayout

abbrev Bits (count : Nat) := Fin count → Bool

def allBits : (count : Nat) → List (Bits count)
  | 0 => [Fin.elim0]
  | n + 1 => (allBits n).flatMap fun tail =>
      [Fin.cases false tail, Fin.cases true tail]

def le {count} (x y : Bits count) : Bool :=
  (List.finRange count).all fun i => !x i || y i

def equal {count} (x y : Bits count) : Bool :=
  (List.finRange count).all fun i => x i == y i

def join {count} (x y : Bits count) : Bits count := fun i => x i || y i

def meet {count} (x y : Bits count) : Bits count := fun i => x i && y i

variable {count : Nat} (data : Fin count → Description (Fin count))

def admitted (x : Bits count) : Bool :=
  (List.finRange count).all fun i => (data i).range (x i)

def vectors : List (Bits count) := (allBits count).filter (admitted data)

def unit : Bits count := fun i => (data i).unitValue

def credit : Bits count := fun i => (data i).creditValue

def atom (types : List TypeVar) (v : TypeVar) : Bits count :=
  fun i => atomValue types (data i) v

def modal (modes : List ModVar) (m : ModExpr) (x : Bits count) : Bits count :=
  fun i => action modes (data i) m (x i)

def op (k : Constructor) (x y : Bits count) : Bits count := fun i =>
  let b := (data i).branch k
  if b.left then sign k b.left (x b.next) else sign k b.left (y b.next)

def eval (types : List TypeVar) (modes : List ModVar) (a : CompareTy) : Bits count :=
  ComparisonObserverMachine.value (nodes types modes data) a

end ModalityInference.ComparisonObserverRangeEncoding
