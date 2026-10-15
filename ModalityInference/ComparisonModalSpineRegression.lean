import ModalityInference.SchemeSubsumption

/-! A modal spine containing an undefined residual cannot be an admissible
public comparison image, even when its other annotations are total. -/
namespace ModalityInference.ComparisonModalSpineRegression

def bad : ModExpr := .leftResidual .epsilon .bottom
def mu : ModExpr := .var (.flex 0)
def capsule : Ty := .modal (.modal .unit .top) bad
def source : Scheme := { modParams := [0], body := .modal .unit mu }
def target : Scheme := .mono capsule
def mixedSource : Scheme :=
  { modParams := [0], body := .prod (.modal .unit mu) (.fn (.modal .unit mu) .unit) }
def mixedTarget : Scheme :=
  .mono (.prod (.modal capsule .top) (.fn (.modal capsule .bottom) .unit))

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

#guard match checkSubsumption 20000 source target with
  | .rejected _ => true
  | _ => false

#guard match checkSubsumption 20000 mixedSource mixedTarget with
  | .rejected _ => true
  | _ => false

-- The partial image cannot satisfy a written definedness requirement.
#guard match checkSubsumption 20000 { source with bounds := [.defined mu] } target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonModalSpineRegression
