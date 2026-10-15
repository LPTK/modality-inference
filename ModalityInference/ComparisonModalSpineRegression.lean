import ModalityInference.SchemeSubsumption

/-! A shared modality can include total annotations below a partial factor.
Those annotations belong to its literal prefix, before its synthesized suffix. -/
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
  | .success result => result.substitution.types.isEmpty &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

#guard match checkSubsumption 20000 mixedSource mixedTarget with
  | .success result => result.substitution.types.isEmpty &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false

-- The partial image cannot satisfy a written definedness requirement.
#guard match checkSubsumption 20000 { source with bounds := [.defined mu] } target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonModalSpineRegression
