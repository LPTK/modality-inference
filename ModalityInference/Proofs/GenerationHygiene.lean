import ModalityInference.GenerationHygiene
import ModalityInference.Proofs.GenerationSupplies

/-! Quantifier names remain below the generator's modality supply, so fresh
symbolic locks cannot be captured by scheme instantiation. -/
namespace ModalityInference

theorem Generates.Hygienic.lam_fresh {Γ t a cs} {hg : Generates Γ (.lam () t) a cs}
    (h : hg.Hygienic) : ∃ domain codomain m,
      a = .modal (.fn domain codomain) m ∧ AlgorithmicContext.FreshForMode Γ m := by
  cases h with
  | lam hf _ => exact ⟨_, _, _, rfl, hf⟩

def Scheme.ModParamsBounded (nm : Nat) (s : Scheme) : Prop := ∀ n ∈ s.modParams, n < nm

def AlgorithmicContext.ModParamsBounded (nm : Nat) (Γ : AlgorithmicContext) : Prop :=
  ∀ s, .binding (some s) ∈ Γ → s.ModParamsBounded nm

@[simp] theorem AlgorithmicContext.modParamsBounded_nil (nm : Nat) :
    AlgorithmicContext.ModParamsBounded nm [] := by simp [ModParamsBounded]

@[simp] theorem AlgorithmicContext.modParamsBounded_binding {Γ : AlgorithmicContext} {s nm} :
    AlgorithmicContext.ModParamsBounded nm (.binding s :: Γ) ↔
      (∀ a ∈ s, a.ModParamsBounded nm) ∧ Γ.ModParamsBounded nm := by
  simp [ModParamsBounded, or_imp, forall_and, Option.mem_def, eq_comm]

@[simp] theorem AlgorithmicContext.modParamsBounded_lock {Γ : AlgorithmicContext} {m nm} :
    AlgorithmicContext.ModParamsBounded nm (.lock m :: Γ) ↔ Γ.ModParamsBounded nm := by
  simp [ModParamsBounded]

theorem AlgorithmicContext.ModParamsBounded.mono {Γ : AlgorithmicContext} {nm nm'}
    (h : Γ.ModParamsBounded nm) (hh : nm ≤ nm') : Γ.ModParamsBounded nm' :=
  fun s hs n hn => (h s hs n hn).trans_le hh

theorem AlgorithmicContext.ModParamsBounded.fresh {Γ : AlgorithmicContext} {nm}
    (h : Γ.ModParamsBounded nm) : Γ.FreshForMode (.var (.flex nm)) := by
  intro s hs n hn he
  have := h s hs n hn
  simp only [ModExpr.vars, Finset.mem_singleton, ModVar.flex.injEq] at he
  omega

theorem UsageSplit.modParamsBounded {Γ Γ₁ Γ₂ nm} (h : UsageSplit Γ Γ₁ Γ₂)
    (hh : AlgorithmicContext.ModParamsBounded nm Γ) :
    AlgorithmicContext.ModParamsBounded nm Γ₁ ∧ AlgorithmicContext.ModParamsBounded nm Γ₂ := by
  induction h <;> simp_all [Scheme.ModParamsBounded]

theorem splitContext_modParamsBounded {Γ : AlgorithmicContext} {nm}
    (h : Γ.ModParamsBounded nm) (X Y : Finset Nat) :
    (splitContext X Y Γ).1.ModParamsBounded nm ∧
      (splitContext X Y Γ).2.ModParamsBounded nm := (splitContext_spec Γ X Y).modParamsBounded h

theorem Scheme.generalize_modParamsBounded {cs a nt nm}
    (hc : Bounds.Bounded nt nm cs) (ha : TypeExpr.Bounded nt nm a) :
    (Scheme.generalize cs a).ModParamsBounded nm := by
  intro n hn
  simp only [generalize, List.mem_filterMap, List.mem_dedup, List.mem_append,
    TypeExpr.mem_modeVariables, Bounds.mem_modeVariables] at hn
  obtain ⟨v, hv, he⟩ := hn
  cases v <;> simp only [Option.some.injEq, reduceCtorEq] at he
  subst n
  exact hv.elim (((a.bounded_iff nt nm).mp ha).2 _) (((cs.bounded_iff nt nm).mp hc).2 _)

theorem generate_closed_modParamsBounded {fuel rhs nt nm r solveFuel result}
    (hg : generate fuel [] rhs {nextType := nt, nextMode := nm} = .success r)
    (hs : solveFrom solveFuel r.state.nextType r.state.nextMode r.state.constraints = .success result) :
    (Scheme.generalize result.bounds (result.substitution.ty r.type)).ModParamsBounded result.nextMode := by
  have hb := generate_bounded hg (AlgorithmicContext.bounded_nil _ _) (Bounds.bounded_nil _ _)
  have hf := solveFrom_fresh hb.2 hs
  have hn := solveFrom_counters hs
  exact Scheme.generalize_modParamsBounded hf.1 (hf.2.ty (hb.1.mono hn.1 hn.2))

private theorem contextFreshMode_bounds (Γ : Context) (nm : Nat) :
    let bound := Γ.foldl (fun n s => max n (s.map Scheme.freshModeIndex |>.getD 0)) nm
    nm ≤ bound ∧ AlgorithmicContext.ModParamsBounded bound (Γ.map ContextEntry.binding) := by
  induction Γ generalizing nm with
  | nil => simp
  | cons s Γ ih =>
    have hh := ih (max nm (s.map Scheme.freshModeIndex |>.getD 0))
    refine ⟨(Nat.le_max_left _ _).trans hh.1, ?_⟩
    refine AlgorithmicContext.modParamsBounded_binding.mpr ⟨?_, hh.2⟩
    intro a ha
    cases ha
    exact fun n hn => (Scheme.modeParam_lt_freshModeIndex hn).trans_le
      ((Nat.le_max_right _ _).trans hh.1)

theorem initialInferenceState_modParamsBounded (Γ : Context) :
    AlgorithmicContext.ModParamsBounded (initialInferenceState Γ).nextMode (Γ.map ContextEntry.binding) :=
  (contextFreshMode_bounds Γ 0).2

end ModalityInference
