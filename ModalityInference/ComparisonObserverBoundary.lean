import ModalityInference.ComparisonTypes
import Mathlib.Data.Finset.Card

/-! Finite subterm boundaries and explicit observer bounds computed from the
original declared endpoints and comparison query. -/
namespace ModalityInference.ComparisonObserverBoundary

def subterms : CompareTy → List CompareTy
  | a@(.var _) | a@(.unit) | a@(.credit) => [a]
  | t@(.prod a b) | t@(.sum a b) | t@(.fn a b) | t@(.join a b) | t@(.meet a b) =>
      t :: (subterms a ++ subterms b)
  | t@(.modal a _) => t :: subterms a

def closure (inputs : List CompareTy) : List CompareTy := inputs.flatMap subterms

def modes : CompareTy → Finset ModVar
  | .var _ | .unit | .credit => ∅
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => modes a ∪ modes b
  | .modal a m => modes a ∪ m.vars

def allModes : List CompareTy → Finset ModVar
  | [] => ∅
  | a :: rest => modes a ∪ allModes rest

def declaredTypes (Δ : Bounds) : List CompareTy :=
  Δ.flatMap fun c => match c with
    | .sub a b => [.ofTy a, .ofTy b]
    | _ => []

def inputs (Δ : Bounds) (queries : List CompareTy) : List CompareTy := declaredTypes Δ ++ queries

def boundary (Δ : Bounds) (queries : List CompareTy) : List CompareTy := closure (inputs Δ queries)

def names (Δ : Bounds) (queries : List CompareTy) : Finset ModVar := Δ.modVars ∪ allModes (inputs Δ queries)

def sizeBound (Δ : Bounds) (queries : List CompareTy) : Nat :=
  2 ^ (2 * (8 + 10 * (names Δ queries).card) + 2 + (boundary Δ queries).length)

def types : CompareTy → Finset TypeVar
  | .var v => {v}
  | .unit | .credit => ∅
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => types a ∪ types b
  | .modal a _ => types a

def allTypes : List CompareTy → Finset TypeVar
  | [] => ∅
  | a :: rest => types a ∪ allTypes rest

def typeNames (Δ : Bounds) (queries : List CompareTy) : Finset TypeVar := allTypes (inputs Δ queries)

def typeList : CompareTy → List TypeVar
  | .var v => [v]
  | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => typeList a ++ typeList b
  | .modal a _ => typeList a

def modeList : CompareTy → List ModVar
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => modeList a ++ modeList b
  | .modal a m => modeList a ++ m.freeVariables

def retainedTypes (Δ : Bounds) (queries : List CompareTy) : List TypeVar :=
  ((inputs Δ queries).flatMap typeList).dedup

def retainedModes (Δ : Bounds) (queries : List CompareTy) : List ModVar :=
  (Δ.modeVariables ++ (inputs Δ queries).flatMap modeList).dedup

end ModalityInference.ComparisonObserverBoundary
