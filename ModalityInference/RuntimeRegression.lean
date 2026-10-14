import ModalityInference.Runtime

/-! Runtime capture and higher-order execution checks, without inference or
the annotated proof representation. -/
namespace ModalityInference.RuntimeRegression

-- Captures retain de Bruijn positions and discard unused environment entries.
#guard match Runtime.evalFuel 1 {}
    [.credit (.heap 0), .credit (.heap 1), .credit (.heap 2)]
    (.lam () (.var 2)) with
  | .success (.closure [.unit, .credit (.heap 1), .unit] (.var 2)) => true
  | _ => false

-- A closure returned by a call preserves an outer binding under both binders.
def nested : RawTerm := .lam () (.lam () (.var 2))
#guard match Runtime.evalFuel 5 {} [.credit (.heap 8)] (.app nested .unit) with
  | .success (.closure [.unit, .credit (.heap 8)] (.var 2)) => true
  | _ => false
#guard match Runtime.evalFuel 8 {} [.credit (.heap 8)]
    (.app (.app nested .unit) .unit) with
  | .success (.credit (.heap 8)) => true
  | _ => false

-- Exhaustion and rejection remain distinct, including an unused definition.
#guard match Runtime.evalFuel 1 {} [] (.defn .unit .unit) with
  | .exhausted => true
  | _ => false
#guard match Runtime.evalFuel 4 {} [] (.defn (.app .unit .unit) .unit) with
  | .rejected "application of a non-function" => true
  | _ => false

end ModalityInference.RuntimeRegression
