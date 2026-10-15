import ModalityInference.SchemeSubsumption

/-! Literal matching and total outer suffixes do not discharge the guards of
undefined inner annotations in public signature comparison. -/
namespace ModalityInference.ComparisonFrozenContextRegression

def bad : ModExpr := .leftResidual .epsilon .bottom
def base : Ty := .var (.rigid 0)
def typeSource : Scheme := { typeParams := [0], body := .modal (.var (.flex 0)) bad }
def typeTarget : Scheme := .mono (.modal (.modal base bad) .top)
def sharedSource : Scheme :=
  { modParams := [0]
    body := .prod (.modal base (.close (.var (.flex 0)))) (.modal base (.var (.flex 0))) }
def sharedTarget : Scheme := .mono
  (.prod (.modal (.modal base (.close bad)) .top) (.modal (.modal base bad) .top))

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

#guard match checkSubsumption 20000 typeSource typeTarget with
  | .rejected _ => true
  | _ => false

#guard match checkSubsumption 20000 sharedSource sharedTarget with
  | .rejected _ => true
  | _ => false

-- Literal matching does not discharge a source definedness guard.
#guard match checkSubsumption 20000
    { sharedSource with bounds := [.defined (.var (.flex 0))] } sharedTarget with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonFrozenContextRegression
