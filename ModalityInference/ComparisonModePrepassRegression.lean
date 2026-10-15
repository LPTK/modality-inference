import ModalityInference.SchemeSubsumption
import ModalityInference.ComparisonModePrepass
/-! Coupled opaque type and modality obligations retain one scalar choice. -/
namespace ModalityInference.ComparisonModePrepassRegression
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def A : Ty := .var (.rigid 0)
def B : Ty := .var (.rigid 1)
def X : Ty := .var (.flex 0)
def Y : Ty := .var (.flex 1)
def μ : ModExpr := .var (.flex 0)
def source : Scheme :=
  { typeParams := [0,1], modParams := [0]
    bounds := [.sub A X, .sub (.modal X μ) (.modal Y .top), .sub Y B]
    body := .unit }
def target : Scheme :=
  { bounds := [.sub (.modal A (.const Mode.global)) (.modal B .top)]
    body := .unit }
def retry (source target : Scheme) : RunResult ComparisonChecker.Evidence := do
  let p := SchemePreparation.prepare [] source target
  let solved ← ComparisonShapeSolver.prepare 20000 p
  match solved with
  | .infeasibleAssumptions => .rejected "shapes"
  | .solved shapes => do
    let before ← ComparisonModePrepass.attempt 20000 p shapes
    ComparisonChecker.refineContexts 20000 p shapes before
-- A source modality must remain coupled to both opaque interval leaves.
#guard match retry source target with
  | .success result => result.substitution.types.map Prod.fst == [0, 1] &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

-- This guard conflicts with the only declared locality information.
#guard match retry { source with bounds := source.bounds ++ [.mode .epsilon μ] } target with
  | .rejected _ => true
  | _ => false

-- Ordinary ordered bounds remain accepted by the same symbolic path.
#guard match retry source { target with bounds := [.sub A B] } with
  | .success _ => true
  | _ => false

-- The public entry point preserves the same source-domain witness.
#guard match checkSubsumption 20000 source target with
  | .success result => result.substitution.types.map Prod.fst == [0, 1] &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

#guard match checkSubsumption 20000
    { source with bounds := source.bounds ++ [.mode .epsilon μ] } target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonModePrepassRegression
