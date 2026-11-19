import ModalityInference.ComparisonTypes

/-! The syntax shared by semantic and executable modal-suffix normalizers. -/
namespace ModalityInference.ComparisonRawCarrierSuffix

structure Normalized where
  literal : Option ModExpr
  control : ModExpr
  deriving DecidableEq

def prefixApply (p : Option ModExpr) (a : CompareTy) : CompareTy :=
  match p with
  | none => a
  | some m => .modal a m

def Normalized.apply (s : Normalized) (a : CompareTy) : CompareTy :=
  .modal (prefixApply s.literal a) s.control

end ModalityInference.ComparisonRawCarrierSuffix
