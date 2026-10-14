import ModalityInference.Proofs.ResourceSubtyping
import ModalityInference.Proofs.GroundSkolemization
import ModalityInference.Proofs.ConstraintModels

/-! Declarative scheme and context subsumption preserve instance-indexed resources.
Target skolems are realized without changing source free variables or ambient bounds. -/
namespace ModalityInference

theorem Subsumes.resource_semantic {ρ w Δ s t v reserved}
    (h : Subsumes Δ s t) (hΔ : GroundModels ρ Δ)
    (hv : ResourceSchemeInterpretation ρ w s v reserved) :
    ResourceSchemeInterpretation ρ w t v reserved := by
  refine ⟨hv.1, ?_⟩
  intro η ground hη ht
  obtain ⟨θ, hb, he, hft, hfm⟩ := hη.skolemize (s := s) hΔ
  have hb := hb.assumptions_right
  obtain ⟨σ, hσ, hcs, hab⟩ := h
  obtain ⟨source, hsource⟩ := Option.isSome_iff_exists.mp
    (show ((σ.ty s.body).realize θ).isSome = true from
      (hab.realize_defined hb).trans (by rw [he, ht]; rfl))
  obtain ⟨owned, ho, hr⟩ := (hv.ambient_congr hft hfm).2 _ source
    (hσ.ground (hcs.groundModels hb)) (s.body.realize_ground hsource)
  exact let ⟨target, htarget, ht'⟩ := hab.resource_semantic hb hsource (he.trans ht) hr
    ⟨target, htarget.trans ho, ht'⟩

theorem ContextLe.kept {Δ Γ Γ'} (h : ContextLe Δ Γ Γ')
    {i : Nat} {t : Scheme} (hi : Γ'[i]? = some (some t)) :
    ∃ s, Γ[i]? = some (some s) ∧ Subsumes Δ s t := by
  induction h generalizing i
  all_goals cases i <;> simp_all

theorem ContextLe.resource_semantics {ρ w Δ Γ Γ' γ reserved}
    (hΔ : GroundModels ρ Δ) (h : ContextLe Δ Γ Γ')
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved) :
    ResourceEnvironmentInterpretation ρ w Γ' γ reserved ∧
      ContextResources Γ' reserved ⊆ ContextResources Γ reserved := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  case refine_1 =>
    exact fun i t hi =>
      let ⟨s, hs, hsub⟩ := h.kept hi
      let ⟨v, hvalue, hv⟩ := hγ.1 i s hs
      ⟨v, hvalue, hsub.resource_semantic hΔ hv⟩
  case refine_2 =>
    exact fun i j s t hij hi hj =>
      let ⟨s', hi', _⟩ := h.kept hi
      let ⟨t', hj', _⟩ := h.kept hj
      hγ.2 i j s' t' hij hi' hj'
  case refine_3 =>
    exact fun l ⟨i, t, hi, hl⟩ =>
      let ⟨s, hs, _⟩ := h.kept hi
      ⟨i, s, hs, hl⟩

end ModalityInference
