import ModalityInference.Proofs.GuardedGenerationSoundness
import ModalityInference.Proofs.SourceInference
import ModalityInference.Proofs.GuardedSourceSoundness

/-! Actual inference outputs satisfy the guarded source typing discipline. -/
namespace ModalityInference

/-- Hygienic generation supplies a direct source derivation whose changed
context bindings are justified by defined scheme-comparison witnesses. -/
theorem Generates.guarded_source_sound {Γ : Context} {t a cs Δ σ}
    (h : Generates (Γ.map ContextEntry.binding) t a cs) (hh : h.Hygienic)
    (hs : Solution cs Δ σ) (hσ : σ.WellFormedUnder Δ) :
    GuardedSourceTyping Δ (Γ.subst σ) t (σ.ty a) :=
  (h.guarded_raw_sound hh hs hσ).source

/-- Successful inference has a source derivation using defined instances and
only identity or guarded scheme replacement in context weakening. No global
wellformedness assumption is imposed on the input context. -/
theorem inference_guarded_source_sound {fuel Γ t result}
    (h : infer fuel Γ t = .success result) :
    result.elaborated = t ∧
      GuardedSourceTyping result.residual (Γ.subst result.substitution)
        result.elaborated result.scheme.body := by
  obtain ⟨a, cs, hg, hh, hs, hw, he⟩ := infer_derivation h
  refine ⟨infer_term h, ?_⟩
  simpa only [infer_term h, he] using hg.guarded_source_sound hh hs hw

/-- The guarded derivation and all returned image/body guards hold under the
actual residual constraints returned by inference. -/
theorem inference_guarded_source_defined {fuel Γ t result}
    (h : infer fuel Γ t = .success result) :
    result.substitution.WellFormedUnder result.residual ∧
      result.scheme.body.DefinedUnder result.residual ∧
      GuardedSourceTyping result.residual (Γ.subst result.substitution)
        result.elaborated result.scheme.body :=
  ⟨(inference_source_defined h).1, (inference_source_defined h).2,
    (inference_guarded_source_sound h).2⟩

/-- Every closed derivation using guarded context comparisons is accepted with
sufficient fuel. -/
theorem GuardedSourceTyping.inference_complete {t a}
    (h : GuardedSourceTyping [] [] t a) :
    ∃ n, ∀ fuel ≥ n, ∃ result, infer fuel [] t = .success result :=
  h.to_sourceTyping.inference_complete

/-- Successful inference covers every ground instance of every closed guarded
source derivation. -/
theorem GuardedSourceTyping.inference_ground_principal {t a fuel result}
    (ht : GuardedSourceTyping [] [] t a) (hi : infer fuel [] t = .success result)
    (ρ τ : GroundAssignment) :
    SchemeCovers ρ τ result.scheme (Scheme.generalize [] a) :=
  ht.to_sourceTyping.inference_ground_principal hi ρ τ

end ModalityInference
