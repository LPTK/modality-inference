import ModalityInference.ComparisonFiniteCertificateInputs
import ModalityInference.Proofs.ComparisonObserverShadowQuerySupport
import ModalityInference.Proofs.ComparisonExecutableSuffix
import ModalityInference.Proofs.ScalarDecision

/-! The deterministic executable input support is exactly the support used
by the finite comparison model construction. -/
namespace ModalityInference.ComparisonFiniteCertificateInputs

@[simp] theorem normalize_eq (Δ : Bounds) (m : ModExpr) :
    ComparisonExecutableSuffix.normalize (ScalarDecision.defined Δ) m =
      ComparisonRawCarrierSuffix.normalize Δ m :=
  ComparisonExecutableSuffix.normalize_eq (fun n _ => ScalarDecision.defined_correct Δ n)

theorem calls_eq (Δ : Bounds) (a : Ty) (p : Option ModExpr) :
    calls Δ a p = ComparisonRawHeadTrace.calls Δ a p := by
  induction a generalizing p <;> cases p <;>
    simp_all only [calls, ComparisonRawHeadTrace.calls, normalize_eq]

theorem controlNames_eq (Δ : Bounds) (s : Site) :
    controlNames Δ s = ComparisonRawHeadTrace.controlNames Δ s := by
  rcases s with ⟨a,p⟩
  cases a <;> cases p <;> simp only [controlNames, ComparisonRawHeadTrace.controlNames, normalize_eq]

theorem names_eq (Δ : Bounds) (sites : List Site) :
    names Δ sites = ComparisonRawHeadTrace.modeNames Δ sites := by
  simp only [names, ComparisonRawHeadTrace.modeNames, ComparisonRawHeadTrace.rawHeads,
    funext (controlNames_eq Δ)]
  rfl

theorem support_eq (queries : List CompareTy) :
    support queries = ComparisonObserverShadowQuerySupport.support queries := rfl

theorem sites_eq (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    sites Δ raw queries = ComparisonObserverShadowQuerySupport.sites Δ raw queries := by
  simp only [sites, ComparisonObserverShadowQuerySupport.sites,
    ComparisonObserverShadowModel.RawInput.trace, ComparisonRawHeadTrace.ofInputs,
    ComparisonObserverShadowQuerySupport.rawInputs, support_eq, calls_eq]
  rfl

theorem sourceNames_eq (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    sourceNames Δ raw queries = ComparisonRawHeadTrace.modeNames Δ
      (ComparisonObserverShadowQuerySupport.sites Δ raw queries) := by
  rw [sourceNames, names_eq, sites_eq]

end ModalityInference.ComparisonFiniteCertificateInputs
