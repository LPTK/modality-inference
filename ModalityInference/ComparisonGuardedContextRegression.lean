import ModalityInference.SchemeSubsumption

/-! Defining a compound source annotation does not define a partial type image.
Source constraints remain obligations under the declared assumptions. -/
namespace ModalityInference.ComparisonGuardedContextRegression

def bad : ModExpr := .leftResidual .epsilon .bottom
def base : Ty := .var (.rigid 0)
def mu : ModExpr := .var (.flex 0)
def source : Scheme :=
  { typeParams := [0], modParams := [0]
    bounds := [.mode mu .bottom, .mode .bottom mu]
    body := .modal (.var (.flex 0)) (.leftResidual mu .bottom) }
def target : Scheme := .mono (.modal base bad)

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

#guard match checkSubsumption 20000 source target with
  | .rejected _ => true
  | _ => false

-- The explicit type guard agrees with the required definedness of every image.
#guard match checkSubsumption 20000
    { source with bounds := source.bounds ++ [.sub (.var (.flex 0)) (.var (.flex 0))] }
    target with
  | .rejected _ => true
  | _ => false

-- Contradictory source constraints do not become target assumptions.
#guard match checkSubsumption 20000
    { source with bounds := source.bounds ++ [.mode .epsilon mu] } target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonGuardedContextRegression
