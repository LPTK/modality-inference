import ModalityInference.SchemeSubsumption
import ModalityInference.ComparisonCompoundSpine

/-! Splitting a modal spine across quantified parameters does not discharge
the residual guards required of its images and instantiated body. -/
namespace ModalityInference.ComparisonCompoundSpineRegression

def bad : ModExpr := .leftResidual .epsilon .bottom
def mu : ModExpr := .var (.flex 0)
def nu : ModExpr := .var (.flex 1)
def inner : Ty := .modal (.modal .unit bad) bad
def capsule : Ty := .modal (.modal (.modal .unit .top) bad) bad
def source : Scheme := { modParams := [0, 1], body := .modal .unit (.compose mu nu) }
def target : Scheme := .mono capsule
def mixedSource : Scheme :=
  { modParams := [0, 1]
    body := .prod (.modal .unit (.compose mu nu)) (.fn (.modal .unit nu) .unit) }
def mixedTarget : Scheme :=
  .mono (.prod (.modal capsule .top) (.fn (.modal inner .bottom) .unit))

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

#guard match checkSubsumption 20000 source target with
  | .rejected _ => true
  | _ => false

#guard match checkSubsumption 20000 mixedSource mixedTarget with
  | .rejected _ => true
  | _ => false

#guard match checkSubsumption 20000 { source with bounds := [.defined nu] } target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonCompoundSpineRegression
