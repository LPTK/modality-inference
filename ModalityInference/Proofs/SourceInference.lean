import ModalityInference.SourceTyping
import ModalityInference.Proofs.InferenceDerivation
import ModalityInference.Proofs.GenerationSoundness
import ModalityInference.Proofs.InferenceCompleteness
import ModalityInference.Proofs.SourceSoundness

/-! Inference guarantees for the paper's direct, unannotated typing judgment. -/
namespace ModalityInference

theorem Generates.source_sound {Γ : Context} {t a cs Δ σ}
    (h : Generates (Γ.map ContextEntry.binding) t a cs) (hh : h.Hygienic)
    (hs : Solution cs Δ σ) (hσ : σ.WellFormedUnder Δ) :
    SourceTyping Δ (Γ.subst σ) t (σ.ty a) :=
  SourceTyping.of_rawTyping (h.sound hh hs hσ)

/-- Successful inference returns the input itself, with a direct source typing
derivation at the inferred type under the returned bounds and substitution. -/
theorem inference_source_sound {fuel Γ t result}
    (h : infer fuel Γ t = .success result) :
    result.elaborated = t ∧
      SourceTyping result.residual (Γ.subst result.substitution)
        result.elaborated result.scheme.body := by
  obtain ⟨a, cs, hg, hh, hs, hw, he⟩ := infer_derivation h
  refine ⟨infer_term h, ?_⟩
  simpa only [infer_term h, he] using hg.source_sound hh hs hw

/-- Inference's actual output executes safely in the raw runtime at every
ground instance satisfying its residual bounds and environment interpretation. -/
theorem inference_source_semantic {fuel Γ t result ρ w γ reserved ground}
    (hi : infer fuel Γ t = .success result) (hΔ : GroundModels ρ result.residual)
    (hγ : Runtime.ResourceEnvironmentInterpretation ρ w
      (Γ.subst result.substitution) γ reserved)
    (ha : result.scheme.body.realize ρ = some ground) :
    Runtime.ResourceSemanticEvaluation w γ result.elaborated ground
      (ContextResources (Γ.subst result.substitution) reserved) :=
  (inference_source_sound hi).2.resource_semantic hΔ hγ ha

/-- Every closed source derivation is accepted with sufficiently large fuel. -/
theorem SourceTyping.inference_complete {t a} (h : SourceTyping [] [] t a) :
    ∃ n, ∀ fuel ≥ n, ∃ result, infer fuel [] t = .success result :=
  ModalityInference.inference_complete h.to_rawTyping

/-- Every successful result covers every ground instance of any valid closed
source type, up to subtyping. -/
theorem SourceTyping.inference_ground_principal {t a fuel result}
    (ht : SourceTyping [] [] t a) (hi : infer fuel [] t = .success result)
    (ρ τ : GroundAssignment) :
    SchemeCovers ρ τ result.scheme (Scheme.generalize [] a) :=
  ModalityInference.inference_ground_principal ht.to_rawTyping hi ρ τ

end ModalityInference
