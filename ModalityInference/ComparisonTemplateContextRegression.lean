import ModalityInference.SchemeSubsumption

/-! A shared structured image has independent partial leaf intervals and one
root action. Template exposure must keep all these choices jointly quantified. -/
namespace ModalityInference.ComparisonTemplateContextRegression

def partialA : Ty := .modal (.var (.rigid 0)) (.leftResidual .epsilon .bottom)
def partialB : Ty := .modal (.var (.rigid 1)) (.leftResidual .epsilon .bottom)
def q : ModExpr := .const Mode.absorbing
def source : Scheme :=
  { typeParams := [0]
    body := .prod (.modal (.var (.flex 0)) q)
      (.fn (.modal (.var (.flex 0)) .bottom) .unit) }
def upper : Ty := .prod partialA (.modal partialB q)
def lower : Ty := .prod (.modal partialA q) partialB
def target : Scheme := .mono (.prod (.modal upper q) (.fn (.modal lower q) .unit))

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

#guard match checkSubsumption 20000 source target with
  | .success result => result.substitution.types.map Prod.fst == [0] &&
      result.substitution.modes.isEmpty
  | _ => false

-- Every written guard remains an obligation after structural parameterization.
#guard match checkSubsumption 20000
    { source with bounds := [.sub (.var (.flex 0)) (.var (.flex 0))] } target with
  | .rejected _ => true
  | _ => false

end ModalityInference.ComparisonTemplateContextRegression
