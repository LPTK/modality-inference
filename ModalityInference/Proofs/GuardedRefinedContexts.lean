import ModalityInference.Proofs.GuardedContexts
import ModalityInference.Proofs.RefinedReuse

/-! Guarded context certificates for locks, usage splitting, and refined lookups. -/
namespace ModalityInference

theorem Scheme.refined_lock_guardsBody (s : Scheme) (p : Nat) (ms : List ModExpr) :
    ((s.refineMode p).lockAll ms).withAssumptions.GuardsBody :=
  ((s.refineMode_guardsBody p).lockAll ms).withAssumptions

theorem UsageSplit.declarative_refined_guarded {Γ Γ₁ Γ₂ : AlgorithmicContext}
    {Δ : Bounds} {p : Nat} (h : UsageSplit Γ Γ₁ Γ₂)
    (hf : Γ.RefinementFresh p Δ) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars) :
    ∃ joined, GuardedContextLe Δ (Γ.refinedContext p ms) joined ∧
      ContextJoin Δ (Γ₁.refinedContext p ms) (Γ₂.refinedContext p ms) joined := by
  obtain ⟨joined, hc, hj⟩ := h.declarative_refined hf ms hm
  exact ⟨joined, hc.guarded_of_source (Γ.refinedContext_guardsBodies p ms), hj⟩

theorem AlgorithmicContext.refinedContext_guarded_lock {Γ : AlgorithmicContext} {p : Nat}
    {Δ : Bounds} {m : ModExpr} (hf : Γ.RefinementFresh p Δ)
    (hm : Γ.FreshForMode m) (hp : .flex p ∉ m.vars) (ms : List ModExpr) :
    ∃ source, GuardedContextLe Δ (Γ.refinedContext p ms) source ∧
      Lock Δ m source (Γ.refinedContext p (m :: ms)) := by
  obtain ⟨source, hc, hl⟩ := Γ.refinedContext_lock hf hm hp ms
  exact ⟨source, hc.guarded_of_source (Γ.refinedContext_guardsBodies p ms), hl⟩

theorem Lookup.refinedContext_guarded_typing {Γ : AlgorithmicContext} {i : Nat} {s : Scheme}
    {σ : Substitution} {p : Nat} {Δ : Bounds} (h : Lookup Γ i s)
    (hf : Γ.RefinementFresh p Δ) (hi : Instantiates s σ) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars)
    (hb : EntailsAll Δ (σ.bounds (s.lockAll ms).bounds)) (hd : (σ.ty s.body).DefinedUnder Δ) :
    GuardedSourceTyping Δ (Γ.refinedContext p ms) (.var i) (σ.ty (s.lockAll ms).body) := by
  obtain ⟨t, τ, ht, hi', hb', hd', hsub, _⟩ := h.refinedContext_instance hf hi ms hm hb hd
  obtain ⟨υ, hu, he, hc⟩ := hi'.exists_under hb' hd'
  exact (GuardedSourceTyping.var ht hu (hc ▸ hb')).subs (.refl _ _) (he ▸ hsub)

theorem Lookup.substAvoid_refined_guarded_typing {Γ : AlgorithmicContext} {i : Nat} {s : Scheme}
    {θ σ : Substitution} {Δ : Bounds} (h : Lookup Γ i s) (hi : Instantiates s θ)
    (hΓ : Γ.LocksScoped) (avoid : Bounds)
    (hf : ∀ m, .lock m ∈ Γ → .defined (m.subst σ.mode) ∈ avoid) (hΔ : Δ ⊆ avoid)
    (hb : EntailsAll Δ (σ.bounds (θ.bounds s.bounds)))
    (hd : (σ.ty (θ.ty s.body)).DefinedUnder Δ) :
    ∃ lower, ∀ p ≥ lower,
      GuardedSourceTyping Δ ((Γ.substAvoid σ avoid).refinedContext p) (.var i)
        (σ.ty (θ.ty s.body)) := by
  obtain ⟨lower, hp⟩ := Γ.substAvoid_refinementFresh_eventually σ Δ avoid hΔ
  obtain ⟨t, τ, hl, hi', he, hb'⟩ := h.substAvoid_instance hi hΓ avoid hf
  refine ⟨lower, fun p hlarge => ?_⟩
  simpa only [Scheme.lockAll, he] using
    hl.refinedContext_guarded_typing (hp p hlarge) hi' [] (by simp)
      ((hb' Δ).mpr hb) (he.symm ▸ hd)

theorem GuardedTyping.lam_refined {Γ : AlgorithmicContext} {p : Nat} {Δ : Bounds}
    {m : ModExpr} {a b : Ty} {t : AnnotatedTerm}
    (hf : Γ.RefinementFresh p Δ) (hscope : Γ.FreshForMode m) (hp : .flex p ∉ m.vars)
    (ha : (Scheme.mono a).freshModeIndex ≤ p)
    (hd : EntailsAll Δ a.wellFormedBounds) (hm : Entails Δ (.defined m))
    (ht : GuardedTyping Δ
      (AlgorithmicContext.refinedContext (.binding (some (.mono a)) :: .lock m :: Γ) p) t b) :
    GuardedTyping Δ (Γ.refinedContext p)
      (.lam ((Γ.refinedContext p [m]).restrict (t.freeVars 1)) t) (.modal (.fn a b) m) := by
  obtain ⟨source, hc, hl⟩ := Γ.refinedContext_guarded_lock hf hscope hp []
  exact (GuardedSourceTyping.lam hd hm hl
    (ht.subs (.keep (.refl _ _) (Scheme.subsumesUnder_refineMode_withAssumptions ha Δ))
      .refl)).subs hc .refl

end ModalityInference
