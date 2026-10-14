import ModalityInference.Proofs.RefinedSharing

/-! Declarative usage splitting for refined contexts with enclosing symbolic locks. -/
namespace ModalityInference

/-- Refine each binding before resolving its enclosing locks. The accumulator's
head becomes the outermost capture modality. Binding positions are retained. -/
def AlgorithmicContext.refinedContext (Γ : AlgorithmicContext) (p : Nat)
    (ms : List ModExpr := []) : Context :=
  match Γ with
  | [] => []
  | .lock m :: Γ => AlgorithmicContext.refinedContext Γ p (ms ++ [m])
  | .binding s :: Γ =>
    s.map (fun s => ((s.refineMode p).lockAll ms).withAssumptions) ::
      AlgorithmicContext.refinedContext Γ p ms

/-- The new parameter avoids all old scheme support and locks; quantified names
of the refined schemes also avoid the ambient bounds. -/
def AlgorithmicContext.RefinementFresh (Γ : AlgorithmicContext) (p : Nat) (Δ : Bounds) : Prop :=
  (∀ s, .binding (some s) ∈ Γ → s.freshModeIndex ≤ p ∧ (s.refineMode p).FreshForBounds Δ) ∧
  (∀ m, .lock m ∈ Γ → .flex p ∉ m.vars)

theorem AlgorithmicContext.RefinementFresh.tail {entry : ContextEntry} {Γ : AlgorithmicContext}
    {p : Nat} {Δ : Bounds} (h : AlgorithmicContext.RefinementFresh (entry :: Γ) p Δ) :
    Γ.RefinementFresh p Δ :=
  ⟨fun s hs => h.1 s (List.mem_cons_of_mem _ hs),
    fun m hm => h.2 m (List.mem_cons_of_mem _ hm)⟩

theorem ContextJoin.append {Δ Γ Γ₁ Γ₂ Ξ Ξ₁ Ξ₂} (h : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hΞ : ContextJoin Δ Ξ₁ Ξ₂ Ξ) : ContextJoin Δ (Γ₁ ++ Ξ₁) (Γ₂ ++ Ξ₂) (Γ ++ Ξ) := by
  induction h with
  | nil => exact hΞ
  | unused _ ih => exact .unused ih
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | shared _ hf ha ih => exact .shared ih hf ha

theorem UsageSplit.declarative_refined {Γ Γ₁ Γ₂ : AlgorithmicContext} {Δ : Bounds} {p : Nat}
    (h : UsageSplit Γ Γ₁ Γ₂) (hf : Γ.RefinementFresh p Δ) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars) :
    ∃ joined, ContextLe Δ (Γ.refinedContext p ms) joined ∧
      ContextJoin Δ (Γ₁.refinedContext p ms) (Γ₂.refinedContext p ms) joined := by
  induction h generalizing ms with
  | nil => exact ⟨[], .nil, .nil⟩
  | @lock Γ Γ₁ Γ₂ m hj ih =>
    apply ih hf.tail (ms ++ [m])
    simpa [List.mem_append, or_imp, forall_and] using ⟨hm, hf.2 m List.mem_cons_self⟩
  | drop hj ih =>
    obtain ⟨joined, hc, hj'⟩ := ih hf.tail ms hm
    exact ⟨none :: joined, .drop hc, .unused hj'⟩
  | @left Γ Γ₁ Γ₂ s hj ih =>
    obtain ⟨joined, hc, hj'⟩ := ih hf.tail ms hm
    cases s with
    | none => exact ⟨none :: joined, .drop hc, .unused hj'⟩
    | some s => exact ⟨some ((s.refineMode p).lockAll ms).withAssumptions :: joined,
        .keep hc (.refl _ _), .left hj'⟩
  | @right Γ Γ₁ Γ₂ s hj ih =>
    obtain ⟨joined, hc, hj'⟩ := ih hf.tail ms hm
    cases s with
    | none => exact ⟨none :: joined, .drop hc, .unused hj'⟩
    | some s => exact ⟨some ((s.refineMode p).lockAll ms).withAssumptions :: joined,
        .keep hc (.refl _ _), .right hj'⟩
  | @share Γ Γ₁ Γ₂ s shared hj he ih =>
    obtain ⟨joined, hc, hj'⟩ := ih hf.tail ms hm
    subst shared
    exact ⟨some (((s.share.refineMode p).lockAll ms).withAssumptions.modal (.const Mode.many)) :: joined,
      .keep hc (s.refineMode_lockAll_subsumes_refined_shared
        (hf.1 s List.mem_cons_self).1 (hf.1 s List.mem_cons_self).1 hm hm Δ),
      (s.refined_shared_lockAll_join (ms := ms) (hf.1 s List.mem_cons_self).2).append hj'⟩

theorem freshFold_le_iff {α : Type} (index : α → Nat) (xs : List α) (start n : Nat) :
    xs.foldl (fun k v => max k (index v + 1)) start ≤ n ↔ start ≤ n ∧ ∀ v ∈ xs, index v < n := by
  induction xs generalizing start <;>
    simp_all [List.foldl_cons, Nat.add_one_le_iff, and_assoc]

theorem Scheme.freshModeIndex_le_iff (s : Scheme) (p : Nat) :
    s.freshModeIndex ≤ p ↔ (∀ n ∈ s.modParams, n < p) ∧
      ∀ v ∈ s.body.modVars ∪ s.bounds.modVars, v.index < p := by
  simp [freshModeIndex, freshFold_le_iff, or_imp, forall_and, and_assoc, ModVar.index]

theorem Scheme.share_freshModeIndex (s : Scheme) : s.share.freshModeIndex = s.freshModeIndex := by
  have he (p : Nat) : s.share.freshModeIndex ≤ p ↔ s.freshModeIndex ≤ p := by
    simp [freshModeIndex_le_iff, share, TypeExpr.modVars, ModExpr.vars, Constraint.modVars,
      Bounds.mem_modVars_iff, or_and_right, exists_or, or_comm]
  exact Nat.le_antisymm ((he _).mpr (Nat.le_refl _)) ((he _).mp (Nat.le_refl _))

@[simp] theorem AlgorithmicContext.refinementFresh_binding {Γ : AlgorithmicContext}
    {entry : Option Scheme} {p : Nat} {Δ : Bounds} :
    AlgorithmicContext.RefinementFresh (.binding entry :: Γ) p Δ ↔
      (∀ s ∈ entry, s.freshModeIndex ≤ p ∧ (s.refineMode p).FreshForBounds Δ) ∧
        Γ.RefinementFresh p Δ := by
  cases entry <;> simp [RefinementFresh, or_imp, forall_and, and_assoc, and_left_comm]

@[simp] theorem AlgorithmicContext.refinementFresh_lock {Γ : AlgorithmicContext}
    {m : ModExpr} {p : Nat} {Δ : Bounds} :
    AlgorithmicContext.RefinementFresh (.lock m :: Γ) p Δ ↔
      .flex p ∉ m.vars ∧ Γ.RefinementFresh p Δ := by
  simp [RefinementFresh, or_imp, forall_and, and_assoc, and_left_comm]

@[simp] theorem AlgorithmicContext.refinementFresh_nil (p : Nat) (Δ : Bounds) :
    AlgorithmicContext.RefinementFresh [] p Δ :=
  ⟨fun _ h => False.elim (List.not_mem_nil h), fun _ h => False.elim (List.not_mem_nil h)⟩

theorem UsageSplit.refinementFresh {Γ Γ₁ Γ₂ : AlgorithmicContext} {p : Nat} {Δ : Bounds}
    (h : UsageSplit Γ Γ₁ Γ₂) (hf : Γ.RefinementFresh p Δ) :
    Γ₁.RefinementFresh p Δ ∧ Γ₂.RefinementFresh p Δ := by
  induction h <;> simp_all
  exact ⟨(Scheme.share_freshModeIndex _).le.trans hf.1.1, hf.1.2⟩

theorem Scheme.lockAll_append (s : Scheme) (ms ns : List ModExpr) :
    (s.lockAll ns).lockAll ms = s.lockAll (ms ++ ns) := by
  induction ms <;> simp_all [lockAll]

theorem Lookup.refinedContext_instance {Γ : AlgorithmicContext} {i : Nat} {s : Scheme}
    {σ : Substitution} {p : Nat} {Δ : Bounds} (h : Lookup Γ i s)
    (hf : Γ.RefinementFresh p Δ) (hi : Instantiates s σ) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars)
    (hb : EntailsAll Δ (σ.bounds (s.lockAll ms).bounds)) (hd : (σ.ty s.body).DefinedUnder Δ) :
    ∃ t τ, (Γ.refinedContext p ms)[i]? = some (some t) ∧ Instantiates t τ ∧
      EntailsAll Δ (τ.bounds t.bounds) ∧ (τ.ty t.body).DefinedUnder Δ ∧
      Subtype Δ (τ.ty t.body) (σ.ty (s.lockAll ms).body) ∧
      Subtype Δ (σ.ty (s.lockAll ms).body) (τ.ty t.body) := by
  induction h generalizing ms with
  | @here Γ s =>
    obtain ⟨hτ, hbounds, hdefined, hst, hts⟩ :=
      hi.refineMode_lockAll (hf.1 s List.mem_cons_self).1 hm hb hd
    exact ⟨((s.refineMode p).lockAll ms).withAssumptions, σ.extendMode p .epsilon, rfl,
      hτ, hbounds.subst_assumptions, hdefined, hst, hts⟩
  | there h ih => exact ih hf.tail hi ms hm hb hd
  | @locked Γ i s m h ih =>
    have he : (s.lock m).lockAll ms = s.lockAll (ms ++ [m]) := s.lockAll_append ms [m]
    have hm' : ∀ n ∈ ms ++ [m], .flex p ∉ n.vars := by
      simpa [List.mem_append, or_imp, forall_and] using ⟨hm, hf.2 m List.mem_cons_self⟩
    simpa only [← he] using ih hf.tail hi (ms ++ [m]) hm' (he ▸ hb)
      (TypeExpr.definedUnder_modal.mp hd).1

end ModalityInference
