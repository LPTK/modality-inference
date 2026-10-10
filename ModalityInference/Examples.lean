import ModalityInference.Inference
import ModalityInference.Generation
import ModalityInference.SchemeSubsumption
import ModalityInference.Semantics

namespace ModalityInference.Examples
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def identity : RawTerm := .lam () (.var 0)
def heapPair : RawTerm := .pair .unit .unit
def stackPair : RawTerm := .stackPair .unit .unit
def reusePair : RawTerm := .split stackPair (.reuse (.var 0) (.var 1) (.var 2))
def stackScoped : RawTerm := .region (.split reusePair .unit)
def stackEscape : RawTerm := .region reusePair
def polyIdentity : RawTerm := .defn identity
  (.pair (.app (.var 0) .unit) (.app (.var 0) heapPair))
def branchUsage : RawTerm := .lam () (.case (.inl .unit) .unit (.var 1))
def inconsistentUnused : RawTerm := .defn (.app .unit .unit) .unit
def nonClosedDef : RawTerm := .lam () (.defn (.var 0) .unit)
def duplicateCredit : RawTerm := .split heapPair
  (.pair (.reuse (.var 0) .unit .unit) (.reuse (.var 0) .unit .unit))
def initialSupplies : Supplies := {}

#eval (infer 2000 [] heapPair).isSuccess
#eval (infer 2000 [] identity).isSuccess
#eval (infer 2000 [] stackScoped).isSuccess
#eval (infer 2000 [] stackEscape).isSuccess
#eval (infer 5000 [] polyIdentity).isSuccess
#eval (infer 2000 [] branchUsage).isSuccess
#eval (infer 2000 [] inconsistentUnused).isSuccess
#eval (infer 2000 [] nonClosedDef).isSuccess
#eval (infer 4000 [] duplicateCredit).isSuccess

end ModalityInference.Examples
