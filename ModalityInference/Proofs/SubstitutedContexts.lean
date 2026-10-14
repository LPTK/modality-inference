import ModalityInference.Proofs.RefinedLocks

/-! Sharing commutes with capture-avoiding substitution of algorithmic contexts. -/
namespace ModalityInference

theorem Scheme.share_fresheningIndices (s : Scheme) (σ : Substitution) :
    s.share.fresheningIndices σ = s.fresheningIndices σ := by
  have ht (p : Nat) : (s.share.fresheningIndices σ).1 ≤ p ↔ (s.fresheningIndices σ).1 ≤ p := by
    simp [fresheningIndices, freshFold_le_iff, share, TypeExpr.typeVariables,
      TypeExpr.modeVariables, Bounds.typeVariables, Bounds.modeVariables,
      Constraint.typeVariables, Constraint.modeVariables, ModExpr.freeVariables,
      or_imp, forall_and, and_assoc]
    tauto
  have hm (p : Nat) : (s.share.fresheningIndices σ).2 ≤ p ↔ (s.fresheningIndices σ).2 ≤ p := by
    simp [fresheningIndices, freshFold_le_iff, share, TypeExpr.typeVariables,
      TypeExpr.modeVariables, Bounds.typeVariables, Bounds.modeVariables,
      Constraint.typeVariables, Constraint.modeVariables, ModExpr.freeVariables,
      or_imp, forall_and, and_assoc]
    tauto
  exact Prod.ext (Nat.le_antisymm ((ht _).mpr (Nat.le_refl _)) ((ht _).mp (Nat.le_refl _)))
    (Nat.le_antisymm ((hm _).mpr (Nat.le_refl _)) ((hm _).mp (Nat.le_refl _)))

theorem Scheme.share_subst (s : Scheme) (σ : Substitution) :
    s.share.subst σ = (s.subst σ).share := by
  simp only [Scheme.subst, share_fresheningIndices]
  simp [instantiate, freshSubstitution, share, Substitution.ty, TypeExpr.subst,
    Substitution.bounds, Substitution.constraint, Constraint.subst, ModExpr.subst]

def AlgorithmicContext.subst (Γ : AlgorithmicContext) (σ : Substitution) : AlgorithmicContext :=
  Γ.map fun
    | .binding s => .binding (s.map (fun s => s.subst σ))
    | .lock m => .lock (m.subst σ.mode)

theorem UsageSplit.substitute {Γ Γ₁ Γ₂ : AlgorithmicContext} (h : UsageSplit Γ Γ₁ Γ₂)
    (σ : Substitution) : UsageSplit (Γ.subst σ) (Γ₁.subst σ) (Γ₂.subst σ) := by
  induction h with
  | nil => exact .nil
  | lock _ ih => exact .lock ih
  | drop _ ih => exact .drop ih
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | share _ he ih =>
    subst_vars
    exact .share ih (Scheme.share_subst _ _)

theorem Scheme.lockAll_instance_congr {s t : Scheme} {σ τ : Substitution} {Δ : Bounds}
    (he : σ.ty s.body = τ.ty t.body)
    (hb : EntailsAll Δ (σ.bounds s.bounds) ↔ EntailsAll Δ (τ.bounds t.bounds))
    (ms : List ModExpr) (f : ModExpr → ModExpr)
    (hm : ∀ m ∈ ms, m.subst σ.mode = (f m).subst τ.mode) :
    σ.ty (s.lockAll ms).body = τ.ty (t.lockAll (ms.map f)).body ∧
      (EntailsAll Δ (σ.bounds (s.lockAll ms).bounds) ↔
        EntailsAll Δ (τ.bounds (t.lockAll (ms.map f)).bounds)) := by
  induction ms with
  | nil => exact ⟨he, hb⟩
  | cons m ms ih =>
    obtain ⟨he', hb'⟩ := ih (fun k hk => hm k (List.mem_cons_of_mem _ hk))
    simp only [List.map_cons, Scheme.lockAll, Scheme.lock_instance_body,
      Scheme.lock_instance_bounds, he', hm m List.mem_cons_self, hb']
    trivial

theorem Instantiates.mode_fixed {s : Scheme} {θ : Substitution} {m : ModExpr}
    (hi : Instantiates s θ) (hf : s.FreshForMode m) : m.subst θ.mode = m := by
  apply (m.subst_congr ?_).trans m.subst_id
  intro v hv
  cases v with
  | rigid n => rfl
  | flex n => exact θ.mode_fresh (fun hn => hf n (hi.2.mem_iff.mp hn) hv)

theorem Lookup.freshForMode {Γ : AlgorithmicContext} {i : Nat} {s : Scheme} {m : ModExpr}
    (h : Lookup Γ i s) (hf : Γ.FreshForMode m) : s.FreshForMode m := by
  induction h with
  | here => exact hf _ List.mem_cons_self
  | there _ ih | locked _ ih => exact ih (fun s hs => hf s (List.mem_cons_of_mem _ hs))

def AlgorithmicContext.LocksScoped : AlgorithmicContext → Prop
  | [] => True
  | .binding _ :: Γ => LocksScoped Γ
  | .lock m :: Γ => AlgorithmicContext.FreshForMode Γ m ∧ LocksScoped Γ

@[simp] theorem AlgorithmicContext.freshForMode_binding {Γ : AlgorithmicContext}
    {entry : Option Scheme} {m : ModExpr} :
    AlgorithmicContext.FreshForMode (.binding entry :: Γ) m ↔
      (∀ s ∈ entry, s.FreshForMode m) ∧ Γ.FreshForMode m := by
  cases entry <;> simp [FreshForMode, or_imp, forall_and]

@[simp] theorem AlgorithmicContext.freshForMode_lock {Γ : AlgorithmicContext} {m n : ModExpr} :
    AlgorithmicContext.FreshForMode (.lock n :: Γ) m ↔ Γ.FreshForMode m := by
  simp [FreshForMode]

@[simp] theorem AlgorithmicContext.freshForMode_nil (m : ModExpr) :
    AlgorithmicContext.FreshForMode [] m := by simp [FreshForMode]

theorem UsageSplit.freshForMode {Γ Γ₁ Γ₂ : AlgorithmicContext} {m : ModExpr}
    (h : UsageSplit Γ Γ₁ Γ₂) (hf : Γ.FreshForMode m) :
    Γ₁.FreshForMode m ∧ Γ₂.FreshForMode m := by
  induction h <;> simp_all [Scheme.FreshForMode]

theorem UsageSplit.locksScoped {Γ Γ₁ Γ₂ : AlgorithmicContext}
    (h : UsageSplit Γ Γ₁ Γ₂) (hf : Γ.LocksScoped) : Γ₁.LocksScoped ∧ Γ₂.LocksScoped := by
  induction h with
  | nil => exact ⟨trivial, trivial⟩
  | lock hj ih =>
    exact ⟨⟨(hj.freshForMode hf.1).1, (ih hf.2).1⟩,
      ⟨(hj.freshForMode hf.1).2, (ih hf.2).2⟩⟩
  | drop _ ih | left _ ih | right _ ih | share _ _ ih => exact ih hf

theorem Lookup.substitute_instance {Γ : AlgorithmicContext} {i : Nat} {s : Scheme}
    {θ σ : Substitution} (h : Lookup Γ i s) (hi : Instantiates s θ)
    (hΓ : Γ.LocksScoped) (hσ : (Γ.subst σ).LocksScoped) :
    ∃ t τ, Lookup (Γ.subst σ) i t ∧ Instantiates t τ ∧
      τ.ty t.body = σ.ty (θ.ty s.body) ∧
      ∀ Δ, EntailsAll Δ (τ.bounds t.bounds) ↔ EntailsAll Δ (σ.bounds (θ.bounds s.bounds)) := by
  induction h with
  | here =>
    obtain ⟨τ, hi', he, hb⟩ := hi.substitute σ
    exact ⟨_, τ, .here, hi', he, hb⟩
  | there _ ih =>
    obtain ⟨t, τ, hl, hi', he, hb⟩ := ih hi hΓ hσ
    exact ⟨t, τ, .there hl, hi', he, hb⟩
  | @locked Γ i s m hl ih =>
    obtain ⟨t, τ, hl', hi', he, hb⟩ := ih hi hΓ.2 hσ.2
    have hm := hi.mode_fixed (hl.freshForMode hΓ.1)
    have hm' := hi'.mode_fixed (hl'.freshForMode hσ.1)
    refine ⟨t.lock (m.subst σ.mode), τ, .locked hl', hi', ?_, ?_⟩
    · change TypeExpr.modal (τ.ty t.body) (.capture ((m.subst σ.mode).subst τ.mode)) =
        TypeExpr.modal (σ.ty (θ.ty s.body)) (.capture ((m.subst θ.mode).subst σ.mode))
      rw [he, hm, hm']
    · intro Δ
      change EntailsAll Δ (τ.bounds (t.lock (m.subst σ.mode)).bounds) ↔
        EntailsAll Δ (σ.bounds (θ.bounds (s.lock m).bounds))
      rw [Substitution.bounds_compose, Scheme.lock_instance_bounds, Scheme.lock_instance_bounds]
      simp only [← Substitution.ty_compose, ← ModExpr.subst_compose, hm, hm', he,
        ← Substitution.bounds_compose, hb Δ]

theorem Lookup.substituted_refined_typing {Γ : AlgorithmicContext} {i : Nat} {s : Scheme}
    {θ σ : Substitution} {Δ : Bounds} {p : Nat} (h : Lookup Γ i s) (hi : Instantiates s θ)
    (hΓ : Γ.LocksScoped) (hσ : (Γ.subst σ).LocksScoped) (hf : (Γ.subst σ).RefinementFresh p Δ)
    (hb : EntailsAll Δ (σ.bounds (θ.bounds s.bounds)))
    (hd : (σ.ty (θ.ty s.body)).DefinedUnder Δ) :
    Typing Δ ((Γ.subst σ).refinedContext p) (.var i) (σ.ty (θ.ty s.body)) := by
  obtain ⟨t, τ, hl, hi', he, hb'⟩ := h.substitute_instance hi hΓ hσ
  simpa only [Scheme.lockAll, he] using hl.refinedContext_typing hf hi' []
    (by simp) ((hb' Δ).mpr hb) (he.symm ▸ hd)

end ModalityInference
