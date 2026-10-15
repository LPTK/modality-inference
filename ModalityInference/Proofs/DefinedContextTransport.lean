import ModalityInference.Proofs.DefinedInstantiation
import ModalityInference.Proofs.TypingAdmissibility
import ModalityInference.Proofs.SourceInference

/-! Auxiliary context transport preserves admissible instances. It does not
assert a uniformly defined skolem witness for every unused context binding. -/
namespace ModalityInference

theorem Subsumes.instantiate_under {Δ : Bounds} {source target : Scheme}
    {θ : Substitution} (h : Subsumes Δ source target) (hΔ : Δ.TypeBoundsDefined)
    (hi : InstantiatesUnder Δ target θ)
    (hb : EntailsAll Δ (θ.bounds target.bounds)) :
    ∃ σ, InstantiatesUnder Δ source σ ∧ EntailsAll Δ (σ.bounds source.bounds) ∧
      Subtype Δ (σ.ty source.body) (θ.ty target.body) := by
  obtain ⟨σ, hσ, hbounds, hbody⟩ := h.instantiate hi.domain hb hi.body
  have hd := (hbody.definedUnder_iff hΔ).mpr hi.body
  obtain ⟨τ, hτ, he, hconstraints⟩ := hσ.exists_under hbounds hd
  exact ⟨τ, hτ, hconstraints ▸ hbounds, he ▸ hbody⟩

theorem ContextLe.instantiate_under {Δ : Bounds} {source target : Context}
    {i : Nat} {scheme : Scheme} {θ : Substitution}
    (h : ContextLe Δ source target) (hΔ : Δ.TypeBoundsDefined)
    (hl : target[i]? = some (some scheme)) (hi : InstantiatesUnder Δ scheme θ)
    (hb : EntailsAll Δ (θ.bounds scheme.bounds)) :
    ∃ s σ, source[i]? = some (some s) ∧ InstantiatesUnder Δ s σ ∧
      EntailsAll Δ (σ.bounds s.bounds) ∧
      Subtype Δ (σ.ty s.body) (θ.ty scheme.body) := by
  obtain ⟨s, hs, hsub⟩ := h.kept hl
  obtain ⟨σ, hσ, hbounds, hbody⟩ := hsub.instantiate_under hΔ hi hb
  exact ⟨s, σ, hs, hσ, hbounds, hbody⟩

theorem inference_residual_typeBoundsDefined {fuel : Nat} {Γ : Context} {t : RawTerm}
    {result : Inferred} (h : infer fuel Γ t = .success result) :
    result.residual.TypeBoundsDefined := by
  simp only [infer, bind, pure, RunResult.bind] at h
  repeat' (split at h <;> try contradiction)
  cases h
  exact solveFrom_typeBoundsDefined ‹solveFrom _ _ _ _ = .success _›

theorem inference_context_instance_transport {fuel : Nat} {Γ : Context} {t : RawTerm}
    {result : Inferred} (h : infer fuel Γ t = .success result)
    {source target : Context} {i : Nat} {scheme : Scheme} {θ : Substitution}
    (hc : ContextLe result.residual source target)
    (hl : target[i]? = some (some scheme))
    (hi : InstantiatesUnder result.residual scheme θ)
    (hb : EntailsAll result.residual (θ.bounds scheme.bounds)) :
    ∃ s σ, source[i]? = some (some s) ∧ InstantiatesUnder result.residual s σ ∧
      EntailsAll result.residual (σ.bounds s.bounds) ∧
      Subtype result.residual (σ.ty s.body) (θ.ty scheme.body) :=
  hc.instantiate_under (inference_residual_typeBoundsDefined h) hl hi hb

end ModalityInference
