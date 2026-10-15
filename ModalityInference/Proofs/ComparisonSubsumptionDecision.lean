import ModalityInference.Proofs.ComparisonSubsumptionCompleteness
import ModalityInference.Proofs.ComparisonSoundness

/-! Completed public comparisons decide admissible subsumption under residual
declared bounds; exhaustion remains a separate outcome at smaller budgets. -/
namespace ModalityInference

theorem checkSubsumption_rejected {fuel : Nat} {source target : Scheme} {reason : String}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds)
    (hr : checkSubsumption fuel source target = .rejected reason) :
    ¬ AlgebraSubsumesUnder [] source target := by
  intro h
  obtain ⟨n, hn⟩ := checkSubsumption_complete ht hm hR h
  obtain ⟨evidence, he⟩ := hn (max fuel n) (Nat.le_max_right _ _)
  have hs := checkSubsumption_stable hr (by simp) (Nat.le_max_left fuel n)
  rw [he] at hs
  cases hs

theorem checkSubsumption_decides {source target : Scheme}
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (hR : Residual target.bounds) :
    ∃ n, ∀ fuel ≥ n,
      ((∃ evidence, checkSubsumption fuel source target = .success evidence) ↔
        AlgebraSubsumesUnder [] source target) ∧
      ((∃ reason, checkSubsumption fuel source target = .rejected reason) ↔
        ¬ AlgebraSubsumesUnder [] source target) ∧
      checkSubsumption fuel source target ≠ .exhausted := by
  obtain ⟨n, result, hr, hn⟩ := checkSubsumption_terminates source target
  refine ⟨n, fun fuel hf => ?_⟩
  have he := hn fuel hf
  cases result with
  | exhausted => exact False.elim (hr rfl)
  | success evidence =>
      have h := checkSubsumption_defined_subsumes he
      refine ⟨⟨fun _ => h, fun _ => ⟨evidence, he⟩⟩, ?_, ?_⟩
      · constructor
        · rintro ⟨reason, hreason⟩
          rw [he] at hreason
          cases hreason
        · intro hnot
          exact False.elim (hnot h)
      · simp [he]
  | rejected reason =>
      have h := checkSubsumption_rejected ht hm hR he
      refine ⟨?_, ⟨fun _ => h, fun _ => ⟨reason, he⟩⟩, ?_⟩
      · constructor
        · rintro ⟨evidence, hevidence⟩
          rw [he] at hevidence
          cases hevidence
        · intro hw
          exact False.elim (h hw)
      · simp [he]

end ModalityInference
