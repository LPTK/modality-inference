import ModalityInference.SchemeSubsumption

/-! An undefined capsule remains undefined under total outer actions. Public
comparison must discharge its guard even when suffix constraints are solvable. -/
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
  | .rejected _ => true
  | _ => false
#guard rejected (checkSubsumption 20000 symbolicSource symbolicTarget)

-- Fixing the original modality still leaves the target capsule undefined.
#guard match checkSubsumption 20000 constrainedModeSource mixedTarget with
  | .rejected _ => true
  | _ => false

-- An explicit image guard agrees with the implicit quantified-image obligation.
#guard rejected (checkSubsumption 20000
  { mixedSource with bounds := [.sub (.var (.flex 0)) (.var (.flex 0))] } mixedTarget)

-- Crossed suffix constraints do not supply the missing capsule guard.
#guard rejected (checkSubsumption 20000
  { typeParams := [0], body := .prod (.var (.flex 0)) (.fn (.var (.flex 0)) .unit) }
  (.mono (.prod (.modal capsule .bottom) (.fn (.modal capsule .top) .unit))))

-- Changing a literal head also leaves the capsule guard unavailable.
#guard rejected (checkSubsumption 20000 mixedSource
  (.mono (.prod (.modal capsule shared)
    (.fn (.modal (.modal (.var (.rigid 1)) bad) shared) .unit))))

end ModalityInference.ComparisonCapsuleContextRegression
