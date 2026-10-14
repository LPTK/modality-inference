import ModalityInference.Proofs.SubstitutedContexts

/-! Freshening substituted scheme binders away from all ambient bounds and locks. -/
namespace ModalityInference

def Scheme.substAvoid (s : Scheme) (σ : Substitution) (avoid : Bounds) : Scheme :=
  (s.subst σ).subst (.identityAt avoid.freshTypeIndex avoid.freshModeIndex)

def AlgorithmicContext.substAvoid (Γ : AlgorithmicContext) (σ : Substitution)
    (avoid : Bounds) : AlgorithmicContext :=
  Γ.transform (fun s => s.substAvoid σ avoid) σ

theorem Instantiates.substAvoid {s : Scheme} {θ : Substitution} (hi : Instantiates s θ)
    (σ : Substitution) (avoid : Bounds) :
    ∃ τ, Instantiates (s.substAvoid σ avoid) τ ∧
      τ.ty (s.substAvoid σ avoid).body = σ.ty (θ.ty s.body) ∧
      ∀ Δ, EntailsAll Δ (τ.bounds (s.substAvoid σ avoid).bounds) ↔
        EntailsAll Δ (σ.bounds (θ.bounds s.bounds)) := by
  obtain ⟨τ, hτ, he, hb⟩ := hi.substitute σ
  obtain ⟨τ', hτ', he', hb'⟩ := hτ.substitute (.identityAt avoid.freshTypeIndex avoid.freshModeIndex)
  refine ⟨τ', hτ', ?_, ?_⟩
  · simpa only [Substitution.ty, Substitution.identityAt_type, Substitution.identityAt_mode,
      TypeExpr.subst_id] using he'.trans (congrArg
        (Substitution.ty (.identityAt avoid.freshTypeIndex avoid.freshModeIndex)) he)
  · exact fun Δ => (hb' Δ).trans ((Substitution.identity_bounds_entails
      (Substitution.identityAt_type _ _) (Substitution.identityAt_mode _ _) _ Δ).trans (hb Δ))

theorem Scheme.substAvoid_fresh (s : Scheme) (σ : Substitution) (avoid : Bounds) :
    (s.substAvoid σ avoid).FreshForBounds avoid :=
  (s.subst σ).subst_freshForBounds _ _ ((s.subst σ).freshening_identityAt _ _).1.le
    ((s.subst σ).freshening_identityAt _ _).2.le

theorem Scheme.share_substAvoid (s : Scheme) (σ : Substitution) (avoid : Bounds) :
    s.share.substAvoid σ avoid = (s.substAvoid σ avoid).share := by
  simp only [substAvoid, share_subst]

theorem AlgorithmicContext.substAvoid_freshForBounds (Γ : AlgorithmicContext) (σ : Substitution)
    (avoid : Bounds) {s : Scheme} (hs : .binding (some s) ∈ Γ.substAvoid σ avoid) :
    s.FreshForBounds avoid := by
  obtain ⟨entry, _, he⟩ := List.mem_map.mp hs
  cases entry with
  | lock m => cases he
  | binding entry =>
    cases entry with
    | none => cases he
    | some source => cases he; exact source.substAvoid_fresh σ avoid

theorem AlgorithmicContext.substAvoid_freshForMode (Γ : AlgorithmicContext) (σ : Substitution)
    (avoid : Bounds) {m : ModExpr} (hm : Constraint.defined m ∈ avoid) :
    (Γ.substAvoid σ avoid).FreshForMode m :=
  fun _ hs => (Γ.substAvoid_freshForBounds σ avoid hs).defined hm

theorem AlgorithmicContext.substAvoid_locksScoped (Γ : AlgorithmicContext) (σ : Substitution)
    (avoid : Bounds) (hf : ∀ m, .lock m ∈ Γ → .defined (m.subst σ.mode) ∈ avoid) :
    (Γ.substAvoid σ avoid).LocksScoped := by
  induction Γ with
  | nil => trivial
  | cons entry Γ ih =>
    cases entry with
    | binding entry => exact ih (fun m hm => hf m (List.mem_cons_of_mem _ hm))
    | lock m =>
      exact ⟨AlgorithmicContext.substAvoid_freshForMode Γ σ avoid (hf m List.mem_cons_self),
        ih (fun n hn => hf n (List.mem_cons_of_mem _ hn))⟩

theorem Lookup.substAvoid_instance {Γ : AlgorithmicContext} {i : Nat} {s : Scheme}
    {θ σ : Substitution} (h : Lookup Γ i s) (hi : Instantiates s θ)
    (hΓ : Γ.LocksScoped) (avoid : Bounds)
    (hf : ∀ m, .lock m ∈ Γ → .defined (m.subst σ.mode) ∈ avoid) :
    ∃ t τ, Lookup (Γ.substAvoid σ avoid) i t ∧ Instantiates t τ ∧
      τ.ty t.body = σ.ty (θ.ty s.body) ∧
      ∀ Δ, EntailsAll Δ (τ.bounds t.bounds) ↔ EntailsAll Δ (σ.bounds (θ.bounds s.bounds)) := by
  exact h.transform_instance (fun _ _ hi => hi.substAvoid σ avoid) hi hΓ
    (Γ.substAvoid_locksScoped σ avoid hf)

theorem AlgorithmicContext.refinementFresh_eventually (Γ : AlgorithmicContext) (Δ : Bounds)
    (hf : ∀ s, .binding (some s) ∈ Γ → s.FreshForBounds Δ) :
    ∃ lower, ∀ p ≥ lower, Γ.RefinementFresh p Δ := by
  let indices := Δ.freshModeIndex :: Γ.flatMap (fun
    | .binding none => []
    | .binding (some s) => [s.freshModeIndex]
    | .lock m => m.freeVariables.map ModVar.index)
  let lower := indices.foldl (fun n v => max n (v + 1)) 0
  refine ⟨lower, ?_⟩
  intro p hp
  have hb (n : Nat) (hn : n ∈ indices) : n < p :=
    ((freshFold_bounds id indices 0).2 n hn).trans_le hp
  have hΔ : .flex p ∉ Δ.modVars := fun hv => Nat.lt_irrefl p
    ((Bounds.lt_freshModeIndex ((Bounds.mem_modeVariables Δ _).mpr hv)).trans
      (hb _ List.mem_cons_self))
  refine ⟨?_, ?_⟩
  · intro s hs
    exact ⟨(hb _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
      ⟨.binding (some s), hs, by simp⟩))).le,
      (s.refineMode_freshForBounds p Δ).mpr ⟨hf s hs, hΔ⟩⟩
  · intro m hm hp
    exact Nat.lt_irrefl p (hb p (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
      ⟨.lock m, hm, List.mem_map.mpr ⟨.flex p, by simpa using hp, rfl⟩⟩)))

theorem AlgorithmicContext.substAvoid_refinementFresh_eventually (Γ : AlgorithmicContext)
    (σ : Substitution) (Δ avoid : Bounds) (hΔ : Δ ⊆ avoid) :
    ∃ lower, ∀ p ≥ lower, (Γ.substAvoid σ avoid).RefinementFresh p Δ :=
  (Γ.substAvoid σ avoid).refinementFresh_eventually Δ
    (fun _ hs => (Γ.substAvoid_freshForBounds σ avoid hs).of_subset hΔ)

theorem Lookup.substAvoid_refined_typing {Γ : AlgorithmicContext} {i : Nat} {s : Scheme}
    {θ σ : Substitution} {Δ : Bounds} (h : Lookup Γ i s) (hi : Instantiates s θ)
    (hΓ : Γ.LocksScoped) (avoid : Bounds)
    (hf : ∀ m, .lock m ∈ Γ → .defined (m.subst σ.mode) ∈ avoid) (hΔ : Δ ⊆ avoid)
    (hb : EntailsAll Δ (σ.bounds (θ.bounds s.bounds)))
    (hd : (σ.ty (θ.ty s.body)).DefinedUnder Δ) :
    ∃ lower, ∀ p ≥ lower,
      Typing Δ ((Γ.substAvoid σ avoid).refinedContext p) (.var i) (σ.ty (θ.ty s.body)) := by
  obtain ⟨lower, hp⟩ := Γ.substAvoid_refinementFresh_eventually σ Δ avoid hΔ
  obtain ⟨t, τ, hl, hi', he, hb'⟩ := h.substAvoid_instance hi hΓ avoid hf
  refine ⟨lower, fun p hlarge => ?_⟩
  simpa only [Scheme.lockAll, he] using
    hl.refinedContext_typing (hp p hlarge) hi' [] (by simp) ((hb' Δ).mpr hb) (he.symm ▸ hd)

theorem UsageSplit.substAvoid {Γ Γ₁ Γ₂ : AlgorithmicContext} (h : UsageSplit Γ Γ₁ Γ₂)
    (σ : Substitution) (avoid : Bounds) :
    UsageSplit (Γ.substAvoid σ avoid) (Γ₁.substAvoid σ avoid) (Γ₂.substAvoid σ avoid) :=
  h.transform (fun s => s.substAvoid σ avoid) σ (fun s => s.share_substAvoid σ avoid)

end ModalityInference
