import ModalityInference.Proofs.ComparisonExecutableSyntax
import ModalityInference.Proofs.ScalarDecision

/-! The symbolic scalar decision procedure discharges all definedness tests of
executable suffix normalization and syntax evaluation. -/
namespace ModalityInference.ComparisonExecutableSuffix

def normalizeScalar (Δ : Bounds) (m : ModExpr) : ComparisonRawCarrierSuffix.Normalized :=
  normalize (ScalarDecision.defined Δ) m

theorem scalar_correctOn (Δ : Bounds) (labels : List ModExpr) :
    CorrectOn Δ (ScalarDecision.defined Δ) labels :=
  fun m _ => ScalarDecision.defined_correct Δ m

theorem normalizeScalar_eq (Δ : Bounds) (m : ModExpr) :
    normalizeScalar Δ m = ComparisonRawCarrierSuffix.normalize Δ m :=
  normalize_eq (scalar_correctOn Δ (tests m))

end ModalityInference.ComparisonExecutableSuffix

namespace ModalityInference.ComparisonExecutableSyntax.Agreement

open ComparisonRelativeCoordinates ComparisonRelativeSyntax

variable {Δ : Bounds} {M V N A O : Type*} [PartialOrder N] [CommMonoid N]
  {embed : A → O → Bool} {E : Data M V} {S : Model Δ N A O embed}
  {decode : V → Coordinates N (O → Bool)} {controlMap : M → N}

theorem eval_eq_scalar (h : Agreement E S decode controlMap)
    (ht : E.total = ScalarDecision.defined Δ) {a : CompareTy}
    (hc : ControlsCorrectOn E S controlMap (controlLabels E.total a)) (p : Option ModExpr) :
    decode (E.eval a p) = S.denote a p := by
  apply h.eval_eq (hc := hc)
  simpa only [ht] using ComparisonExecutableSuffix.scalar_correctOn Δ (totalTests a)

theorem evalRaw_eq_scalar (h : Agreement E S decode controlMap)
    (ht : E.total = ScalarDecision.defined Δ) {a : Ty}
    (hc : ControlsCorrectOn E S controlMap (controlLabels E.total (.ofTy a))) :
    decode (E.evalRaw a) = S.denote (.ofTy a) none := h.eval_eq_scalar ht hc none

end ModalityInference.ComparisonExecutableSyntax.Agreement
