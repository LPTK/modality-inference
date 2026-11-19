import ModalityInference.ComparisonObserverMachineFormula
import ModalityInference.ComparisonObserverRangeEncoding

/-! Symbolic finite observer vectors and operations. Table lookup compiles an
address decoder by recursion on its bits, without enumerating assignments to
the surrounding formula. -/
namespace ModalityInference.ComparisonObserverRangeFormula

open ComparisonObserverMachineFormula ComparisonStructuralLayout

abbrev Bits (count : Nat) := Fin count → BoolExpr

def eval {count} (x : Bits count) (world : Nat → Bool) : ComparisonObserverRangeEncoding.Bits count :=
  fun i => (x i).eval world

def le {count} (x y : Bits count) : BoolExpr :=
  .all ((List.finRange count).map fun i => .imp (x i) (y i))

def equal {count} (x y : Bits count) : BoolExpr :=
  .all ((List.finRange count).map fun i => .equal (x i) (y i))

def join {count} (x y : Bits count) : Bits count := fun i => .or (x i) (y i)

def meet {count} (x y : Bits count) : Bits count := fun i => .and (x i) (y i)

variable {count : Nat} (data : Fin count → Fields count)

def admitted (x : Bits count) : BoolExpr :=
  .all ((List.finRange count).map fun i => rangeAt (data i) (x i))

def unit : Bits count := fun i => (data i).unitValue

def credit : Bits count := fun i => (data i).creditValue

def atom (types : List TypeVar) (v : TypeVar) : Bits count :=
  fun i => ComparisonObserverMachineFormula.atom types (data i) v

def modal (names : List ModVar) (m : ModExpr) (x : Bits count) : Bits count :=
  fun i => action names (data i) m (x i)

def op (k : Constructor) (x y : Bits count) : Bits count := fun i =>
  mux ((data i).left k)
    (if k.dual then .imp (successor data i k x) (.const false) else successor data i k x)
    (successor data i k y)

def lookup : {count : Nat} → (ComparisonObserverRangeEncoding.Bits count → BoolExpr) →
    Bits count → BoolExpr
  | 0, values, _ => values Fin.elim0
  | _ + 1, values, input => mux (input 0)
      (lookup (fun tail => values (Fin.cases true tail)) (fun i => input i.succ))
      (lookup (fun tail => values (Fin.cases false tail)) (fun i => input i.succ))

end ModalityInference.ComparisonObserverRangeFormula
