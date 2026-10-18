import ModalityInference.ComparisonObserverMachineFormula
import Mathlib.Data.Nat.Pairing

/-! A fixed finite Boolean input layout for observer-machine synthesis. The
state graph and all node data are chosen symbolically in one formula. -/
namespace ModalityInference.ComparisonObserverMachineEncoding

open ComparisonControls ComparisonStructuralLayout ComparisonObserverMachine
  ComparisonObserverMachineFormula

def code : Constructor → Nat
  | .prod => 0 | .sum => 1 | .fn => 2

def constructor : Nat → Constructor
  | 0 => .prod | 1 => .sum | _ => .fn

def slot (state field index : Nat) : Nat := Nat.pair state (Nat.pair field index)

def allocate (typeCount modeCount count : Nat) (i : Fin count) : Fields count :=
  { atoms := (List.range typeCount).map (fun j => .atom (slot i 0 j))
    modes := (List.range modeCount).map (fun j =>
      (.atom (slot i 1 (Nat.pair j 0)), .atom (slot i 1 (Nat.pair j 1)),
       .atom (slot i 1 (Nat.pair j 2))))
    first := .atom (slot i 2 0)
    second := .atom (slot i 2 1)
    unitValue := .atom (slot i 3 0)
    creditValue := .atom (slot i 3 1)
    left := fun k => .atom (slot i 4 (code k))
    next := fun k j => .atom (slot i 5 (Nat.pair (code k) j))
    range := fun x => .atom (slot i 6 (if x then 1 else 0)) }

def query (Δ : Bounds) (types : List TypeVar) (modes : List ModVar) (count : Nat) : BoolExpr :=
  ComparisonObserverMachineFormula.query Δ types modes (allocate types.length modes.length count)

def decode (types : List TypeVar) (modes : List ModVar) (count : Nat) (world : Nat → Bool) :
    Fin count → ComparisonObserverMachineCheck.Description (Fin count) :=
  ComparisonObserverMachineFormula.decode (allocate types.length modes.length count) world

def observation (types : List TypeVar) (modes : List ModVar) (count : Nat)
    (a : CompareTy) (i : Fin count) : BoolExpr :=
  ComparisonObserverMachineFormula.value types modes (allocate types.length modes.length count) a i

def counterexample (Δ : Bounds) (types : List TypeVar) (modes : List ModVar) (count : Nat)
    (a b : CompareTy) : BoolExpr :=
  .and (query Δ types modes count) (.any ((List.finRange count).map fun i =>
    .and (observation types modes count a i) (.imp (observation types modes count b i) (.const false))))

end ModalityInference.ComparisonObserverMachineEncoding
