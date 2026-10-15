import ModalityInference.ComparisonJointChecker

namespace ModalityInference.ComparisonJointBatchRegression

def A : Ty := .var (.rigid 0)
def B : Ty := .var (.rigid 1)
def C : Ty := .var (.rigid 2)
def D : Ty := .var (.rigid 3)
def X : Ty := .var (.flex 0)
def Y : Ty := .var (.flex 1)
def mu : ModExpr := .var (.flex 0)
def globalMode : ModExpr := .const Mode.global

def source : Scheme :=
  { typeParams := [0, 1]
    modParams := [0]
    bounds := [.sub A X, .sub (.modal X mu) (.modal B .top),
      .sub C Y, .sub (.modal Y mu) (.modal D .top)]
    body := .unit }

def target : Scheme :=
  { bounds := [.sub (.modal A globalMode) (.modal B .top),
      .sub (.modal C globalMode) (.modal D .top)]
    body := .unit }

-- Independent opaque groups share one modality; X=A, Y=C, and mu=global
-- satisfy the declared bounds with exactly the quantified substitution domains.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
#guard match ComparisonJointChecker.run 20000 source target with
  | .success result => result.types.map Prod.fst == [0, 1] &&
      result.modes.map Prod.fst == [0]
  | _ => false

end ModalityInference.ComparisonJointBatchRegression
