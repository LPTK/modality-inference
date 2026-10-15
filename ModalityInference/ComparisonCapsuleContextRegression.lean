import ModalityInference.SchemeSubsumption

/-! Shared partial images must compensate different positive and negative
occurrence actions with one uniformly synthesized suffix. -/
namespace ModalityInference.ComparisonCapsuleContextRegression

def bad : ModExpr := .leftResidual .epsilon .bottom
def capsule : Ty := .modal (.var (.rigid 0)) bad
def shared : ModExpr := .const ⟨false, false, false⟩

def mixedSource : Scheme :=
  { typeParams := [0]
    body := .prod (.modal (.var (.flex 0)) shared)
      (.fn (.modal (.var (.flex 0)) .bottom) .unit) }

def mixedTarget : Scheme :=
  .mono (.prod (.modal capsule shared) (.fn (.modal capsule shared) .unit))

def symbolicSource : Scheme :=
  { typeParams := [0]
    body := .prod (.modal (.var (.flex 0)) (.var (.rigid 0)))
      (.fn (.modal (.var (.flex 0)) (.var (.rigid 1))) .unit) }

def symbolicTarget : Scheme :=
  .mono (.prod (.modal capsule (.compose (.var (.rigid 2)) (.var (.rigid 0))))
    (.fn (.modal capsule (.compose (.var (.rigid 2)) (.var (.rigid 1)))) .unit))

def constrainedModeSource : Scheme :=
  { typeParams := [0], modParams := [0]
    bounds := [.mode (.var (.flex 0)) .epsilon, .mode .epsilon (.var (.flex 0))]
    body := .prod (.modal (.var (.flex 0)) (.var (.flex 0)))
      (.fn (.modal (.var (.flex 0)) .bottom) .unit) }

def rejected (r : RunResult α) : Bool :=
  match r with | .rejected _ => true | _ => false

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

#guard match checkSubsumption 20000 mixedSource mixedTarget with
  | .success result => result.substitution.types.map Prod.fst == [0] &&
      result.substitution.modes.isEmpty
  | _ => false
#guard (checkSubsumption 20000 symbolicSource symbolicTarget).isSuccess

-- The shared suffix and the original modality satisfy written bounds together.
#guard match checkSubsumption 20000 constrainedModeSource mixedTarget with
  | .success result => result.substitution.types.map Prod.fst == [0] &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

-- Written source guards still exclude a partial parameter image.
#guard rejected (checkSubsumption 20000
  { mixedSource with bounds := [.sub (.var (.flex 0)) (.var (.flex 0))] } mixedTarget)

-- A common frozen base does not discharge an inconsistent scalar interval.
#guard rejected (checkSubsumption 20000
  { typeParams := [0], body := .prod (.var (.flex 0)) (.fn (.var (.flex 0)) .unit) }
  (.mono (.prod (.modal capsule .bottom) (.fn (.modal capsule .top) .unit))))

-- Literal operands below partial annotations retain their fixed identities.
#guard rejected (checkSubsumption 20000 mixedSource
  (.mono (.prod (.modal capsule shared)
    (.fn (.modal (.modal (.var (.rigid 1)) bad) shared) .unit))))

end ModalityInference.ComparisonCapsuleContextRegression
