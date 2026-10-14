import ModalityInference.Inference
import ModalityInference.Annotations
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

def capturedCreditScheme : Scheme := .mono (.modal .credit (.var (.flex 0)))
def polymorphicCapturedCredit : SchemeValue :=
  ⟨{modParams := [0], body := .fn .unit capturedCreditScheme.body},
    .closure [.credit (.heap 0)] [some capturedCreditScheme] (.var 1)⟩

def rejected {α : Type} : RunResult α → Bool
  | .rejected _ => true
  | _ => false
def exhausted {α : Type} : RunResult α → Bool
  | .exhausted => true
  | _ => false

#guard (infer 2000 [] heapPair).isSuccess
#guard (infer 2000 [] identity).isSuccess
#guard (infer 2000 [] stackScoped).isSuccess
#guard rejected (infer 2000 [] stackEscape)
#guard (infer 5000 [] polyIdentity).isSuccess
#guard (infer 2000 [] branchUsage).isSuccess
#guard rejected (infer 2000 [] inconsistentUnused)
#guard rejected (infer 2000 [] nonClosedDef)
#guard rejected (infer 4000 [] duplicateCredit)

-- Inference preserves source syntax through locks, sharing and closed definitions.
def preservesSource (Γ : Context) (t : RawTerm) : Bool :=
  match infer 5000 Γ t with
  | .success result => decide (result.elaborated = t)
  | _ => false
#guard preservesSource [] identity
#guard preservesSource [some (.mono (.var (.flex 0)))]
  (.lam () (.pair (.var 1) (.var 1)))
#guard preservesSource [] (.lam () (.lam () (.var 1)))
#guard preservesSource [] (.defn (.app identity identity) (.app (.var 0) .unit))
#guard preservesSource [] polyIdentity

end ModalityInference.Examples
