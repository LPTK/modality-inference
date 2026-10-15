import ModalityInference.Proofs.GuardedSourceTyping
import ModalityInference.Proofs.SourceSoundness

/-! Resource soundness of the guarded source judgment, independently of inference. -/
namespace ModalityInference

/-- Every guarded source derivation has a defined ground result under a model. -/
theorem GuardedSourceTyping.realize_defined {Δ Γ t a}
    (h : GuardedSourceTyping Δ Γ t a) {ρ} (hΔ : GroundModels ρ Δ) :
    (a.realize ρ).isSome := h.to_sourceTyping.realize_defined hΔ

/-- The stricter source judgment retains the verified resource semantics. -/
theorem GuardedSourceTyping.resource_semantic {Δ Γ t a ρ w γ reserved ground}
    (h : GuardedSourceTyping Δ Γ t a) (hΔ : GroundModels ρ Δ)
    (hγ : Runtime.ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (ha : a.realize ρ = some ground) :
    Runtime.ResourceSemanticEvaluation w γ t ground (ContextResources Γ reserved) :=
  h.to_sourceTyping.resource_semantic hΔ hγ ha

end ModalityInference
