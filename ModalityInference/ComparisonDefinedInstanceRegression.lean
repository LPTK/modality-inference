import ModalityInference.SchemeSubsumption
import ModalityInference.Inference
import ModalityInference.ComparisonModePrepassRegression

/-! Defined instances retain symbolic expressions when their guards follow from
the declared bounds. Comparison discharges those guards, while inference retains
them as residual obligations. -/
namespace ModalityInference.ComparisonDefinedInstanceRegression

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def rejected : RunResult α → Bool
  | .rejected _ => true
  | _ => false

def η : ModExpr := .var (.rigid 0)
def r : ModExpr := .leftResidual η .bottom
def A : Ty := .var (.rigid 0)
def modeSource : Scheme :=
  { modParams := [0], body := .modal .unit (.var (.flex 0)) }
def modeTarget : Scheme :=
  { bounds := [.defined r], body := .modal .unit r }
def typeSource : Scheme :=
  { typeParams := [0], body := .var (.flex 0) }
def typeTarget : Scheme :=
  { bounds := [.defined r], body := .modal A r }

-- A guard can justify the literal symbolic image without fixing its rigid input.
#guard match checkSubsumption 20000 modeSource modeTarget with
  | .success result => result.substitution.types.isEmpty &&
      result.substitution.modes == [(0, r)]
  | _ => false
#guard rejected (checkSubsumption 20000 modeSource { modeTarget with bounds := [] })

#guard match checkSubsumption 20000 typeSource typeTarget with
  | .success result => result.substitution.types == [(0, .modal (.var (.rigid 0)) r)] &&
      result.substitution.modes.isEmpty
  | _ => false
#guard rejected (checkSubsumption 20000 typeSource { typeTarget with bounds := [] })

-- Reflexive body comparison still has to discharge body definedness.
def bad : ModExpr := .leftResidual .epsilon .bottom
def badBody : Ty := .modal .unit bad
#guard rejected (checkSubsumption 20000 (.mono badBody) (.mono badBody))

-- Every quantified image is defined, including images unused by body and bounds.
#guard match checkSubsumption 20000
    { typeParams := [0], modParams := [0], body := .unit } (.mono .unit) with
  | .success result => result.substitution.types == [(0, .unit)] &&
      result.substitution.modes == [(0, .epsilon)]
  | _ => false

-- The admissibility discipline does not impose consistency on target assumptions.
#guard (checkSubsumption 20000 (.mono badBody)
  { bounds := [.mode .top .bottom], body := badBody }).isSuccess

-- A compatible rigid interval still requires an internal lattice witness.
def head (n : Nat) : Ty := .var (.rigid n)
def crossed : Bounds :=
  [.sub (head 0) (head 2), .sub (head 0) (head 3),
   .sub (head 1) (head 2), .sub (head 1) (head 3)]
def interval : Scheme :=
  { typeParams := [0]
    bounds := [.sub (head 0) (.var (.flex 0)), .sub (head 1) (.var (.flex 0)),
      .sub (.var (.flex 0)) (head 2), .sub (.var (.flex 0)) (head 3)]
    body := .unit }
#guard (checkSubsumption 20000 interval { bounds := crossed, body := .unit }).isSuccess
#guard rejected (checkSubsumption 20000 interval { bounds := crossed.drop 1, body := .unit })

-- Coupled type and modality constraints remain accepted by the public checker.
#guard match checkSubsumption 20000 ComparisonModePrepassRegression.source
    ComparisonModePrepassRegression.target with
  | .success result => result.substitution.types.map Prod.fst == [0, 1] &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

-- Inference retains the written symbolic type and emits its definedness guard.
#guard match infer 2000 [some (.mono (.modal .unit r))] (.var 0) with
  | .success result => result.scheme.body == .modal .unit r &&
      result.residual == [.defined r] &&
      result.substitution.types.isEmpty && result.substitution.modes.isEmpty
  | _ => false
#guard rejected (infer 2000 [some (.mono badBody)] (.var 0))

end ModalityInference.ComparisonDefinedInstanceRegression
