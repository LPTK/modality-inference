import ModalityInference.Proofs.SchemeBounds

/-! Declarative witnesses for symbolic context splitting and locking, with the
scheme assumptions made explicit. Quantifier freshness remains a premise. -/
namespace ModalityInference

theorem Lock.append {Δ m Γ Γ' Ξ Ξ'} (h : Lock Δ m Γ Γ') (hΞ : Lock Δ m Ξ Ξ') :
    Lock Δ m (Γ ++ Ξ) (Γ' ++ Ξ') := by
  induction h with
  | nil => exact hΞ
  | unused _ ih => exact .unused ih
  | keep _ hb hm ht ih => exact .keep ih hb hm ht
  | unavailable _ ht ih => exact .unavailable ih ht

theorem Context.lock_withAssumptions (Γ : Context) (Δ : Bounds) (m : ModExpr)
    (hf : ∀ s, some s ∈ Γ → s.FreshForBounds Δ)
    (hm : ∀ s, some s ∈ Γ → s.FreshForMode m) :
    ∃ source, ContextLe Δ Γ source ∧
      Lock Δ m source (Γ.map (Option.map (fun s => (s.lock m).withAssumptions))) := by
  induction Γ with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons entry Γ ih =>
    obtain ⟨source, hc, hl⟩ := ih
      (fun s hs => hf s (List.mem_cons_of_mem _ hs))
      (fun s hs => hm s (List.mem_cons_of_mem _ hs))
    cases entry with
    | none => exact ⟨none :: source, .drop hc, .unused hl⟩
    | some s =>
      obtain ⟨head, hs, hlock⟩ := Scheme.lock_withAssumptions (hf s (by simp)) (hm s (by simp))
      exact ⟨some head :: source, .keep hc hs, hlock.append hl⟩

theorem UsageSplit.declarative_bindings {Γ : Context} {Γ₁ Γ₂ : AlgorithmicContext} {Δ : Bounds}
    (h : UsageSplit (Γ.map ContextEntry.binding) Γ₁ Γ₂)
    (hf : ∀ s, some s ∈ Γ → s.FreshForBounds Δ) :
    ∃ left right joined : Context,
      Γ₁ = left.map ContextEntry.binding ∧ Γ₂ = right.map ContextEntry.binding ∧
      ContextLe Δ Γ joined ∧ ContextJoin Δ left.withAssumptions right.withAssumptions joined := by
  induction Γ generalizing Γ₁ Γ₂ with
  | nil => cases h; exact ⟨[], [], [], rfl, rfl, .nil, .nil⟩
  | cons entry Γ ih =>
    cases h with
    | share hj he =>
      rename_i Γ₁ Γ₂ s shared
      obtain ⟨left, right, joined, hl, hr, hc, hj'⟩ :=
        ih hj (fun s hs => hf s (List.mem_cons_of_mem _ hs))
      subst shared
      exact ⟨some s.share :: left, some s.share :: right,
        some (s.share.withAssumptions.modal (.const Mode.many)) :: joined,
        congrArg (ContextEntry.binding (some s.share) :: ·) hl,
        congrArg (ContextEntry.binding (some s.share) :: ·) hr,
        .keep hc (s.subsumes_share_withAssumptions Δ),
        .shared hj' (hf s (by simp)) (Subtype.aliased_idempotent _ _)⟩
    | drop hj =>
      obtain ⟨left, right, joined, hl, hr, hc, hj'⟩ :=
        ih hj (fun s hs => hf s (List.mem_cons_of_mem _ hs))
      exact ⟨none :: left, none :: right, none :: joined,
        congrArg (ContextEntry.binding none :: ·) hl,
        congrArg (ContextEntry.binding none :: ·) hr, .drop hc, .unused hj'⟩
    | left hj =>
      obtain ⟨left, right, joined, hl, hr, hc, hj'⟩ :=
        ih hj (fun s hs => hf s (List.mem_cons_of_mem _ hs))
      refine ⟨entry :: left, none :: right, entry.map Scheme.withAssumptions :: joined,
        congrArg (ContextEntry.binding entry :: ·) hl,
        congrArg (ContextEntry.binding none :: ·) hr, ?_, ?_⟩
      · cases entry with
        | none => exact .drop hc
        | some s => exact .keep hc (s.subsumes_withAssumptions Δ)
      · cases entry with
        | none => exact .unused hj'
        | some s => exact .left hj'
    | right hj =>
      obtain ⟨left, right, joined, hl, hr, hc, hj'⟩ :=
        ih hj (fun s hs => hf s (List.mem_cons_of_mem _ hs))
      refine ⟨none :: left, entry :: right, entry.map Scheme.withAssumptions :: joined,
        congrArg (ContextEntry.binding none :: ·) hl,
        congrArg (ContextEntry.binding entry :: ·) hr, ?_, ?_⟩
      · cases entry with
        | none => exact .drop hc
        | some s => exact .keep hc (s.subsumes_withAssumptions Δ)
      · cases entry with
        | none => exact .unused hj'
        | some s => exact .right hj'

end ModalityInference
