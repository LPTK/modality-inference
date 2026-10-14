import ModalityInference.Proofs.RefinedContexts
import ModalityInference.Proofs.GenerationContextTyping
import ModalityInference.Proofs.GenerationHygiene

/-! Lambda locking and lookup in contexts refined before their enclosing locks. -/
namespace ModalityInference

theorem Scheme.lockAll_freshForBounds (s : Scheme) (ms : List ModExpr) (Δ : Bounds) :
    (s.lockAll ms).FreshForBounds Δ ↔ s.FreshForBounds Δ := by
  simp only [FreshForBounds, (s.lockAll_params ms).1, (s.lockAll_params ms).2]

theorem Scheme.lockAll_freshForMode (s : Scheme) (ms : List ModExpr) (m : ModExpr) :
    (s.lockAll ms).FreshForMode m ↔ s.FreshForMode m := by
  simp only [FreshForMode, (s.lockAll_params ms).2]

theorem Scheme.withAssumptions_lock {s : Scheme} {Δ : Bounds} {m : ModExpr}
    (hb : s.FreshForBounds Δ) (hm : s.FreshForMode m) :
    ∃ source, Subsumes Δ s.withAssumptions source ∧
      Lock Δ m [some source] [some (s.lock m).withAssumptions] := by
  refine ⟨{s with bounds := (s.lock m).bounds.assumptions}, ?_,
    .keep .nil hb hm (.bound (by simp [Scheme.lock, Bounds.assumptions, Constraint.assumptions]))⟩
  refine Subsumes.of_instances (fun Ξ θ hi hbounds => ⟨θ, hi, ?_, .refl⟩)
  exact ((s.lock_instance_bounds θ m Ξ).mp hbounds.of_subst_assumptions).1.subst_assumptions

theorem AlgorithmicContext.refinedContext_lock {Γ : AlgorithmicContext} {p : Nat}
    {Δ : Bounds} {m : ModExpr} (hf : Γ.RefinementFresh p Δ)
    (hm : Γ.FreshForMode m) (hp : .flex p ∉ m.vars) (ms : List ModExpr) :
    ∃ source, ContextLe Δ (Γ.refinedContext p ms) source ∧
      Lock Δ m source (Γ.refinedContext p (m :: ms)) := by
  induction Γ generalizing ms with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons entry Γ ih =>
    cases entry with
    | lock n => exact ih hf.tail (fun s hs => hm s (List.mem_cons_of_mem _ hs)) (ms ++ [n])
    | binding entry =>
      obtain ⟨source, hc, hl⟩ := ih hf.tail (fun s hs => hm s (List.mem_cons_of_mem _ hs)) ms
      cases entry with
      | none => exact ⟨none :: source, .drop hc, .unused hl⟩
      | some s =>
        obtain ⟨head, hs, hlock⟩ := Scheme.withAssumptions_lock
          (((s.refineMode p).lockAll_freshForBounds ms Δ).mpr (hf.1 s List.mem_cons_self).2)
          (((s.refineMode p).lockAll_freshForMode ms m).mpr
            ((s.refineMode_freshForMode p m).mpr ⟨hm s List.mem_cons_self, hp⟩))
        exact ⟨some head :: source, .keep hc hs, hlock.append hl⟩

theorem Lookup.refinedContext_typing {Γ : AlgorithmicContext} {i : Nat} {s : Scheme}
    {σ : Substitution} {p : Nat} {Δ : Bounds} (h : Lookup Γ i s)
    (hf : Γ.RefinementFresh p Δ) (hi : Instantiates s σ) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars)
    (hb : EntailsAll Δ (σ.bounds (s.lockAll ms).bounds)) (hd : (σ.ty s.body).DefinedUnder Δ) :
    Typing Δ (Γ.refinedContext p ms) (.var i) (σ.ty (s.lockAll ms).body) := by
  obtain ⟨t, τ, ht, hi', hb', hd', hsub, _⟩ := h.refinedContext_instance hf hi ms hm hb hd
  exact (Typing.var ht hi' hb' ((τ.ty t.body).definedUnder_iff_entails_wellFormed Δ |>.mp hd')).subs
    (.refl _ _) hsub

theorem Scheme.subsumes_refineMode_withAssumptions {s : Scheme} {p : Nat}
    (hp : s.freshModeIndex ≤ p) (Δ : Bounds) :
    Subsumes Δ s (s.refineMode p).withAssumptions := by
  simpa [withAssumptions] using s.subsumes_refineMode_addAssumptions hp [] Δ

theorem Context.refinedContext_le {Γ : Context} {p : Nat} (Δ : Bounds)
    (hf : ∀ s, some s ∈ Γ → s.freshModeIndex ≤ p) :
    ContextLe Δ Γ (AlgorithmicContext.refinedContext (Γ.map ContextEntry.binding) p) := by
  induction Γ with
  | nil => exact .nil
  | cons entry Γ ih =>
    cases entry with
    | none => exact .drop (ih (fun s hs => hf s (List.mem_cons_of_mem _ hs)))
    | some s =>
      exact .keep (ih (fun s hs => hf s (List.mem_cons_of_mem _ hs)))
        (s.subsumes_refineMode_withAssumptions (hf s List.mem_cons_self) Δ)

theorem Typing.lam_refined {Γ : AlgorithmicContext} {p : Nat} {Δ : Bounds}
    {m : ModExpr} {a b : Ty} {t : AnnotatedTerm}
    (hf : Γ.RefinementFresh p Δ) (hscope : Γ.FreshForMode m) (hp : .flex p ∉ m.vars)
    (ha : (Scheme.mono a).freshModeIndex ≤ p)
    (hd : EntailsAll Δ a.wellFormedBounds) (hm : Entails Δ (.defined m))
    (ht : Typing Δ
      (AlgorithmicContext.refinedContext (.binding (some (.mono a)) :: .lock m :: Γ) p) t b) :
    Typing Δ (Γ.refinedContext p)
      (.lam ((Γ.refinedContext p [m]).restrict (t.freeVars 1)) t) (.modal (.fn a b) m) := by
  obtain ⟨source, hc, hl⟩ := AlgorithmicContext.refinedContext_lock hf hscope hp []
  exact (Typing.lam hd hm hl
    (ht.subs (.keep (.refl _ _) (Scheme.subsumes_refineMode_withAssumptions ha Δ)) .refl)).subs hc .refl

end ModalityInference
