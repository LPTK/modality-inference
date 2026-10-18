import ModalityInference.ComparisonObserverBoundary
import ModalityInference.ComparisonObserverMachineEncoding
import ModalityInference.ModeBackend

/-! A fixed-endpoint algebraic comparison query. Observer states, scalar
worlds and constructor choices are represented symbolically at one input bound. -/
namespace ModalityInference.ComparisonObserverDecision

def counterexample (Δ : Bounds) (a b : CompareTy) : BoolExpr :=
  ComparisonObserverMachineEncoding.counterexample Δ
    (ComparisonObserverBoundary.retainedTypes Δ [a,b])
    (ComparisonObserverBoundary.retainedModes Δ [a,b])
    (ComparisonObserverBoundary.sizeBound Δ [a,b]) a b

def query (Δ : Bounds) (a b : CompareTy) : BoolExpr :=
  .imp (counterexample Δ a b) (.const false)

/-- A successful report has `valid = true` exactly when the comparison holds
on the guarded context domain established by the decision theorem. -/
def run (fuel : Nat) (Δ : Bounds) (a b : CompareTy) : RunResult ConcreteBackend.Report :=
  ConcreteBackend.decideFormula fuel (query Δ a b)

end ModalityInference.ComparisonObserverDecision
