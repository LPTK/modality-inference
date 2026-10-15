import ModalityInference.SchemeSubsumption

/-! Original source guards can make a compound action total while its type
operand remains partial. The guards stay in the final symbolic obligation. -/
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
  | .success result => result.substitution.types.map Prod.fst == [0] &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

-- The original type guard still requires the otherwise partial image defined.
#guard match checkSubsumption 20000
    { source with bounds := source.bounds ++ [.sub (.var (.flex 0)) (.var (.flex 0))] }
    target with
  | .rejected _ => true
  | _ => false

-- A conflicting mode guard cannot be erased by the totality classification.
#guard match checkSubsumption 20000
    { source with bounds := source.bounds ++ [.mode .epsilon mu] } target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonGuardedContextRegression
