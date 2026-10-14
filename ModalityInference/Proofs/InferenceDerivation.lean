import ModalityInference.Proofs.GenerationCorrespondence
import ModalityInference.Proofs.SolverSoundness

/-! Successful inference supplies a hygienic generation derivation and a solution
for exactly its constraints and returned result type. -/
namespace ModalityInference

theorem Scheme.bounded_freshIndices (s : Scheme) :
    s.Bounded s.freshTypeIndex s.freshModeIndex := by
  exact ⟨(s.body.bounded_iff _ _).mpr
    ⟨fun _ h => Scheme.lt_freshTypeIndex (Finset.mem_union_left _ h),
      fun _ h => Scheme.lt_freshModeIndex (Finset.mem_union_left _ h)⟩,
    (s.bounds.bounded_iff _ _).mpr
    ⟨fun _ h => Scheme.lt_freshTypeIndex (Finset.mem_union_right _ h),
      fun _ h => Scheme.lt_freshModeIndex (Finset.mem_union_right _ h)⟩⟩

private theorem contextFreshIndices_bounds (Γ : Context) (nt nm : Nat) :
    let bt := Γ.foldl (fun n s => max n (s.map Scheme.freshTypeIndex |>.getD 0)) nt
    let bm := Γ.foldl (fun n s => max n (s.map Scheme.freshModeIndex |>.getD 0)) nm
    nt ≤ bt ∧ nm ≤ bm ∧ AlgorithmicContext.Bounded bt bm (Γ.map ContextEntry.binding) := by
  induction Γ generalizing nt nm with
  | nil => simp
  | cons s Γ ih =>
    have hh := ih (max nt (s.map Scheme.freshTypeIndex |>.getD 0))
      (max nm (s.map Scheme.freshModeIndex |>.getD 0))
    refine ⟨(Nat.le_max_left _ _).trans hh.1, (Nat.le_max_left _ _).trans hh.2.1,
      AlgorithmicContext.bounded_cons.mpr ⟨?_, hh.2.2⟩⟩
    intro a ha
    cases ha
    exact a.bounded_freshIndices.mono ((Nat.le_max_right _ _).trans hh.1)
      ((Nat.le_max_right _ _).trans hh.2.1)

theorem initialInferenceState_bounded (Γ : Context) :
    AlgorithmicContext.Bounded (initialInferenceState Γ).nextType (initialInferenceState Γ).nextMode
      (Γ.map ContextEntry.binding) :=
  (contextFreshIndices_bounds Γ 0 0).2.2

theorem infer_derivation {fuel Γ t result} (h : infer fuel Γ t = .success result) :
    ∃ a cs, ∃ hg : Generates (Γ.map ContextEntry.binding) t a cs,
      hg.Hygienic ∧ Solution cs result.residual result.substitution ∧
        result.substitution.WellFormedUnder result.residual ∧
          result.scheme.body = result.substitution.ty a := by
  simp only [infer, bind, pure, RunResult.bind] at h
  repeat' (split at h <;> try contradiction)
  cases h
  rename_i _ generated hg _ solved hs
  obtain ⟨cs, hd, hp, hh⟩ := generate_initial_hygienic hg
  have hsol := solveFrom_solution
    (generate_bounded hg (initialInferenceState_bounded Γ) (Bounds.bounded_nil _ _)).2 hs
  exact ⟨generated.type, cs, hd, hh,
    fun c hc => hsol c ((hp.map solved.substitution.constraint).mem_iff.mpr hc),
    solveFrom_substitution_wellFormed
      (generate_bounded hg (initialInferenceState_bounded Γ) (Bounds.bounded_nil _ _)).2 hs, rfl⟩

end ModalityInference
