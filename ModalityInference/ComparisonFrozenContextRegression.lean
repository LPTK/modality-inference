import ModalityInference.SchemeSubsumption

/-! Total outer annotations must expose shared literal partial contexts. -/
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
  | .success result => result.substitution.types.map Prod.fst == [0] &&
      result.substitution.modes.isEmpty
  | _ => false

#guard match checkSubsumption 20000 sharedSource sharedTarget with
  | .success result => result.substitution.types.isEmpty &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

-- Literal matching does not discharge a source definedness guard.
#guard match checkSubsumption 20000
    { sharedSource with bounds := [.defined (.var (.flex 0))] } sharedTarget with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonFrozenContextRegression
