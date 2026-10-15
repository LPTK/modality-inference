import ModalityInference.ComparisonPartialModes

/-! Direct modality occurrences may range over a complete outer target spine.
Every label below its last partial action is retained literally. -/
namespace ModalityInference.ComparisonModalSpine

def act : List ModExpr → Ty → Ty
  | [], base => base
  | m :: ms, base => .modal (act ms base) m

/-- Expose the outer annotations above an exact fixed operand. Stopping on
literal equality keeps partial annotations inside that operand unchanged. -/
def factor (base : Ty) : Ty → Option (List ModExpr)
  | .modal inner m =>
      if .modal inner m == base then some [] else (factor base inner).map (m :: ·)
  | target => if target == base then some [] else none

end ModalityInference.ComparisonModalSpine
