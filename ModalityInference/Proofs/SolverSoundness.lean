import ModalityInference.Proofs.SolverExtension

/-! Backward reconstruction of all input obligations under the final substitution. -/
namespace ModalityInference

theorem solverStep_substituted_entails {s t : SolverState} {τ : Substitution} {Δ}
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound)
    (hσ : s.substitution.Acyclic) (h : solverStep s = .success t)
    (hτ : τ.modes = []) (hext : τ.ExtendsTypes t.substitution)
    (hi : ∀ v, (τ.type v).DefinedUnder Δ)
    (hΔ : EntailsAll Δ (τ.bounds (t.pending ++ t.bounds))) :
    EntailsAll Δ (τ.bounds (s.pending ++ s.bounds)) := by
  rcases solverStep_substitution_cases h with heq | ⟨c, rest, n, a, hp, he, hn, hsub, ht, hb⟩
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact Entails.consequence_substitute_types
      (fun Γ hΓ => solverStep_entails_of_same_substitution hs hm hu hσ h heq hΓ c hc)
      hτ hΔ (fun v _ => hi v)
  · rw [hsub] at hext
    have hone := hext.extendType_single
    have hpost : EntailsAll Δ (τ.bounds (({types := [(n, a)]} : Substitution).bounds
        (rest ++ s.bounds ++ a.wellFormedBounds))) := by
      simpa only [ht, hb, List.append_nil] using hΔ
    have hraw := (hone.bounds_entails rfl _ Δ).mp hpost
    have hec : c.normalize = .equal (.flex n) a := by
      simpa only [(hu.pending c (by simp [hp])).fixed hu.modes] using he
    rw [hp]
    change EntailsAll Δ (τ.constraint c :: τ.bounds (rest ++ s.bounds))
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · apply (c.normalize_substitute_entails Δ hτ).mp
      rw [hec]
      exact hone.singleType_entails (hi (.flex n))
    · apply hraw d
      simpa only [Substitution.bounds, List.map_append] using
        List.mem_append_left (τ.bounds a.wellFormedBounds) hd

theorem runWorklist_substituted_entails {fuel s t} {τ : Substitution} {Δ}
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (hσ : s.substitution.Acyclic) (h : runWorklist fuel s = .success t)
    (hτ : τ.modes = []) (hext : τ.ExtendsTypes t.substitution)
    (hi : ∀ v, (τ.type v).DefinedUnder Δ)
    (hΔ : EntailsAll Δ (τ.bounds (t.pending ++ t.bounds))) :
    EntailsAll Δ (τ.bounds (s.pending ++ s.bounds)) := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h
      exact hΔ
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      have hnextσ := solverStep_acyclic hσ ht
      have hnext := ih (solverStep_typeReady hs hm hu hf hσ ht) (solverStep_modeInvariant hm ht)
        (solverStep_unbound hu hf hσ ht) (solverStep_fresh hf ht) hnextσ h
      exact solverStep_substituted_entails hs hm hu hσ ht hτ
        (runWorklist_extendsTypes_previous hnextσ h hext) hi hnext

theorem runSolver_substituted_entails {fuel s t} {τ : Substitution} {Δ}
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (h : runSolver fuel s = .success t) (hτ : τ.modes = [])
    (hext : τ.ExtendsTypes t.substitution) (hi : ∀ v, (τ.type v).DefinedUnder Δ)
    (hΔ : EntailsAll Δ (τ.bounds (t.pending ++ t.bounds))) :
    EntailsAll Δ (τ.bounds (s.pending ++ s.bounds)) :=
  runWorklist_substituted_entails hs hm hu hf (runSolver_input_acyclic h) (runSolver_worklist h)
    hτ hext hi hΔ

theorem runSolver_entails {fuel s t Δ}
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (h : runSolver fuel s = .success t)
    (hi : ∀ v, (t.substitution.type v).DefinedUnder Δ)
    (hΔ : EntailsAll Δ (t.pending ++ t.bounds)) :
    EntailsAll Δ (t.substitution.bounds (s.pending ++ s.bounds)) := by
  have ht := runSolver_unbound hu hf h
  apply runSolver_substituted_entails hs hm hu hf h ht.modes
    (Substitution.extendsTypes_self ht.modes (runSolver_output_acyclic h)) hi
  change EntailsAll Δ ((t.pending ++ t.bounds).map t.substitution.constraint)
  rw [List.map_append]
  change EntailsAll Δ (t.substitution.bounds t.pending ++ t.substitution.bounds t.bounds)
  rw [ht.fixed.1, ht.fixed.2.1]
  exact hΔ

theorem solveFrom_solution {fuel nt nm cs result} (hc : cs.Bounded nt nm)
    (h : solveFrom fuel nt nm cs = .success result) :
    Solution cs result.bounds result.substitution := by
  have hi := solveFrom_images_defined hc h
  unfold solveFrom at h
  cases hr : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hr, bind, RunResult.bind] at h
  split at h <;> cases h
  have hf : ({pending := cs, nextType := nt, nextMode := nm} : SolverState).Fresh :=
    ⟨hc, Bounds.bounded_nil _ _, Bounds.bounded_nil _ _, Substitution.bounded_empty _ _⟩
  obtain ⟨hd, hp⟩ := runSolver_definedInvariant ⟨rfl, by simp [DefinedConstraints], by simp⟩ hr
  have hres := runSolver_residual (s := {pending := cs, nextType := nt, nextMode := nm}) (by trivial) hr
  have hinput := runSolver_entails (s := {pending := cs, nextType := nt, nextMode := nm})
    (Or.inl (SolverState.TypeInvariant.empty rfl)) ⟨rfl, by simp⟩
    ⟨rfl, fun c _ => c.unbound_empty, by simp, by simp⟩ hf hr hi
    (by simpa only [hp, List.nil_append] using hd.bounds_entails hp hres)
  simpa only [List.append_nil] using hinput

theorem solve_solution {fuel cs result} (h : solve fuel cs = .success result) :
    Solution cs result.bounds result.substitution :=
  solveFrom_solution cs.bounded_freshIndices h

end ModalityInference
