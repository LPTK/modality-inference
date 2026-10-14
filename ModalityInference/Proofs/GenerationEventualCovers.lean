import ModalityInference.Proofs.TypingInstances
import ModalityInference.Proofs.Generation

/-! Semantic comparison of schemes used by completeness. Each target instance
is represented by a source instance, possibly under a different ambient model. -/
namespace ModalityInference

def SchemeCovers (ρ τ : GroundAssignment) (source target : Scheme) : Prop :=
  ∀ η b, GroundInstantiates τ target η → target.body.realize η = some b →
    ∃ ζ a, GroundInstantiates ρ source ζ ∧ source.body.realize ζ = some a ∧
      Subtype [] a.reify b.reify

theorem SchemeCovers.refl (ρ : GroundAssignment) (s : Scheme) : SchemeCovers ρ ρ s s :=
  fun η b hη hb => ⟨η, b, hη, hb, .refl⟩

theorem SchemeCovers.trans {ρ η τ : GroundAssignment} {s t u : Scheme}
    (hst : SchemeCovers ρ η s t) (htu : SchemeCovers η τ t u) : SchemeCovers ρ τ s u := by
  intro ζ c hζ hc
  obtain ⟨ξ, b, hξ, hb, hbc⟩ := htu ζ c hζ hc
  obtain ⟨χ, a, hχ, ha, hab⟩ := hst ξ b hξ hb
  exact ⟨χ, a, hχ, ha, hab.trans hbc⟩

theorem Subsumes.ground_covers {ρ Δ s t} (h : Subsumes Δ s t)
    (hΔ : GroundModels ρ Δ) : SchemeCovers ρ ρ s t := by
  intro η ground hη ht
  obtain ⟨θ, hb, he, hft, hfm⟩ := hη.skolemize (s := s) hΔ
  have hb := hb.assumptions_right
  obtain ⟨σ, hσ, hcs, hab⟩ := h
  obtain ⟨source, hsource⟩ := Option.isSome_iff_exists.mp
    (show ((σ.ty s.body).realize θ).isSome = true from
      (hab.realize_defined hb).trans (by rw [he, ht]; rfl))
  have hi := hσ.ground (hcs.groundModels hb)
  obtain ⟨hreb, hbody⟩ := hi.rebase hft hfm
  exact ⟨s.rebase ρ (σ.ground θ), source, hreb,
    hbody.trans (s.body.realize_ground hsource), hab.ground hb hsource (he.trans ht)⟩

theorem SchemeCovers.source_congr {ρ ρ' τ : GroundAssignment} {s t : Scheme}
    (h : SchemeCovers ρ τ s t)
    (ht : ∀ v ∈ s.freeTypes, ρ'.types v = ρ.types v)
    (hm : ∀ v ∈ s.freeModes, ρ'.modes v = ρ.modes v) : SchemeCovers ρ' τ s t := by
  intro η b hη hb
  obtain ⟨ζ, a, hζ, ha, hab⟩ := h η b hη hb
  obtain ⟨hi, he⟩ := hζ.rebase ht hm
  exact ⟨s.rebase ρ' ζ, a, hi, he.trans ha, hab⟩

theorem SchemeCovers.target_congr {ρ τ τ' : GroundAssignment} {s t : Scheme}
    (h : SchemeCovers ρ τ s t)
    (ht : ∀ v ∈ t.freeTypes, τ.types v = τ'.types v)
    (hm : ∀ v ∈ t.freeModes, τ.modes v = τ'.modes v) : SchemeCovers ρ τ' s t := by
  intro η b hη hb
  obtain ⟨hi, he⟩ := hη.rebase ht hm
  exact h (t.rebase τ η) b hi (he.trans hb)

def ContextCovers (ρ τ : GroundAssignment) (source target : Context) : Prop :=
  ∀ (i : Nat) t, target[i]? = some (some t) →
    ∃ s, source[i]? = some (some s) ∧ SchemeCovers ρ τ s t

theorem ContextCovers.refl (ρ : GroundAssignment) (Γ : Context) : ContextCovers ρ ρ Γ Γ :=
  fun _ t ht => ⟨t, ht, SchemeCovers.refl ρ t⟩

theorem ContextCovers.trans {ρ η τ : GroundAssignment} {Γ₁ Γ₂ Γ₃ : Context}
    (h₁ : ContextCovers ρ η Γ₁ Γ₂) (h₂ : ContextCovers η τ Γ₂ Γ₃) :
    ContextCovers ρ τ Γ₁ Γ₃ := by
  intro i t ht
  obtain ⟨s, hs, hst⟩ := h₂ i t ht
  obtain ⟨r, hr, hrs⟩ := h₁ i s hs
  exact ⟨r, hr, hrs.trans hst⟩

theorem ContextLe.ground_covers {ρ Δ Γ Γ'} (h : ContextLe Δ Γ Γ')
    (hΔ : GroundModels ρ Δ) : ContextCovers ρ ρ Γ Γ' := by
  intro i t ht
  obtain ⟨s, hs, hst⟩ := h.kept ht
  exact ⟨s, hs, hst.ground_covers hΔ⟩

def AlgorithmicContextCovers (ρ τ : GroundAssignment) (source : AlgorithmicContext)
    (target : Context) (used : Finset Nat) : Prop :=
  ∀ i ∈ used, ∀ t, target[i]? = some (some t) →
    ∃ s, Lookup source i s ∧ SchemeCovers ρ τ s t

theorem AlgorithmicContextCovers.restrict {ρ τ source target used used'}
    (h : AlgorithmicContextCovers ρ τ source target used) (hh : used' ⊆ used) :
    AlgorithmicContextCovers ρ τ source target used' :=
  fun i hi t ht => h i (hh hi) t ht

theorem AlgorithmicContextCovers.trans {ρ η τ source middle target used}
    (h : AlgorithmicContextCovers ρ η source middle used)
    (ht : ContextCovers η τ middle target) : AlgorithmicContextCovers ρ τ source target used := by
  intro i hi t hti
  obtain ⟨s, hs, hst⟩ := ht i t hti
  obtain ⟨r, hr, hrs⟩ := h i hi s hs
  exact ⟨r, hr, hrs.trans hst⟩

theorem AlgorithmicContextCovers.nil (ρ τ : GroundAssignment) (used : Finset Nat) :
    AlgorithmicContextCovers ρ τ [] [] used := by
  intro i hi t ht
  simp at ht

end ModalityInference
