import ModalityInference.Evaluation

/-! Kernel-checked correspondence between the executable evaluator and the
independent big-step semantics. This module does not import deferred results. -/
namespace ModalityInference

theorem evalFuel_sound {fuel supplies γ t v}
    (h : evalFuel fuel supplies γ t = .success v) : Eval supplies γ t v := by
  induction fuel generalizing supplies γ t v
  case zero => simp [evalFuel] at h
  case succ n ih =>
    cases t
    all_goals simp only [evalFuel, Bind.bind, Pure.pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals try simp_all only [RunResult.success.injEq]
    all_goals try subst v
    all_goals solve_by_elim (config := {maxDepth := 8}) [Eval.var, Eval.unit, Eval.lam, Eval.app, Eval.pair, Eval.stackPair,
      Eval.inl, Eval.inr, Eval.defn, Eval.split, Eval.caseLeft, Eval.caseRight, Eval.reuse,
      Eval.region, ih]

theorem Eval.fuel_complete {supplies γ t v} (h : Eval supplies γ t v) :
    ∃ n, ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := by
  induction h
  case app hf hx hb ihf ihx ihb | reuse hf hx hb ihf ihx ihb =>
    rcases And.intro ihf (And.intro ihx ihb) with ⟨⟨nf, hf⟩, ⟨nx, hx⟩, ⟨nb, hb⟩⟩
    refine ⟨nf + nx + nb + 1, ?_⟩
    rintro (_ | fuel) hFuel
    · omega
    · simp only [evalFuel, hf fuel (by omega), hx fuel (by omega), hb fuel (by omega),
        Bind.bind, Pure.pure, RunResult.bind]
  case pair h₁ h₂ ih₁ ih₂ | stackPair h₁ h₂ ih₁ ih₂ | defn h₁ h₂ ih₁ ih₂ |
      split h₁ h₂ ih₁ ih₂ | caseLeft h₁ h₂ ih₁ ih₂ | caseRight h₁ h₂ ih₁ ih₂ =>
    rcases And.intro ih₁ ih₂ with ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩⟩
    refine ⟨n₁ + n₂ + 1, ?_⟩
    rintro (_ | fuel) hFuel
    · omega
    · simp only [evalFuel, h₁ fuel (by omega), h₂ fuel (by omega),
        Bind.bind, Pure.pure, RunResult.bind]
  case inl h ih | inr h ih | region h ih =>
    rcases ih with ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rintro (_ | fuel) hFuel
    · omega
    · simp only [evalFuel, hn fuel (by omega), Bind.bind, Pure.pure, RunResult.bind]
  all_goals refine ⟨1, ?_⟩
  all_goals rintro (_ | fuel) hFuel
  all_goals simp_all [evalFuel]

theorem Eval.deterministic {supplies γ t v u}
    (hv : Eval supplies γ t v) (hu : Eval supplies γ t u) : v = u := by
  rcases And.intro hv.fuel_complete hu.fuel_complete with ⟨⟨n, hn⟩, ⟨m, hm⟩⟩
  exact RunResult.success.inj ((hn (max n m) (le_max_left _ _)).symm.trans
    (hm (max n m) (le_max_right _ _)))

/-- Increasing fuel preserves both successful results and genuine diagnostics.
Exhaustion is the only result that may change. -/
theorem evalFuel_stable {n supplies γ t r}
    (hr : r ≠ .exhausted) (h : evalFuel n supplies γ t = r) :
    ∀ fuel ≥ n, evalFuel fuel supplies γ t = r := by
  induction n generalizing supplies γ t r
  case zero => exact False.elim (hr h.symm)
  case succ n ih =>
    rintro (_ | fuel) hFuel
    · omega
    have step (s γ t r) (hs : evalFuel n s γ t = r) (hne : r ≠ .exhausted) :
        evalFuel fuel s γ t = r := ih hne hs fuel (Nat.le_of_succ_le_succ hFuel)
    cases t
    all_goals simp only [evalFuel, Bind.bind, Pure.pure, RunResult.bind] at h ⊢
    all_goals repeat' (split at h <;> try exact False.elim (hr h.symm))
    all_goals simp_all
    all_goals cases h
    all_goals rfl

theorem evalFuel_monotone {n supplies γ t v}
    (h : evalFuel n supplies γ t = .success v) :
    ∀ fuel ≥ n, evalFuel fuel supplies γ t = .success v := by
  exact evalFuel_stable (by simp) h

theorem Eval.no_rejection {supplies γ t v} (h : Eval supplies γ t v)
    (fuel : Nat) (diagnostic : String) : evalFuel fuel supplies γ t ≠ .rejected diagnostic := by
  rcases h.fuel_complete with ⟨n, hn⟩
  intro reject
  have stable := evalFuel_stable (by simp) reject (max n fuel) (le_max_right _ _)
  simp [hn (max n fuel) (le_max_left _ _)] at stable

end ModalityInference
