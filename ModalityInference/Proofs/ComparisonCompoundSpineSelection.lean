import ModalityInference.Proofs.ComparisonCompoundSpine
import ModalityInference.Proofs.ComparisonExactMatchingScope

namespace ModalityInference.ComparisonCompoundSpine

theorem independent_scoped {p : Prepared}
    (ht : ∀ v ∈ p.targetType.modVars, ComparisonInstance.modeAllowed p v = false) :
    ComparisonExactContext.Scoped p (independent p) := by
  apply ComparisonContext.solvePriorityComponents_property _ _ _ _ _
    (ComparisonExactContext.Scoped p)
    (fun request : Request => ∀ v ∈ request.2.vars, ComparisonInstance.modeAllowed p v = false)
    (by constructor <;> simp)
    (fun request hr v hv => ht v (requests_support p hr hv))
  intro request hreq before after hb hm
  exact ComparisonInstance.matchMode_scoped hm hreq hb

theorem prepare_success {p : Prepared} (hf : ComparisonInstance.targetFresh p = true) :
    prepare p = some (independent p) := by
  have hm := (Bool.and_eq_true_iff.mp hf).2
  simp only [List.all_eq_true, Bool.not_eq_true'] at hm
  have hs := independent_scoped (p := p) (fun v hv =>
    hm v ((p.targetType.mem_modeVariables v).mpr hv))
  have hc := (ComparisonExactContext.scopeCheck_iff p _).mpr hs
  simp [prepare, hf, hc]

end ModalityInference.ComparisonCompoundSpine
