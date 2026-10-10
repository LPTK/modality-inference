import ModalityInference.Generation
import ModalityInference.Inference

/-! Established correspondence for symbolic lookup and usage-context routing. -/
namespace ModalityInference

theorem splitContext_spec (Γ : AlgorithmicContext) (X Y : Finset Nat) :
    UsageSplit Γ (splitContext X Y Γ).1 (splitContext X Y Γ).2 := by
  induction Γ generalizing X Y with
  | nil => exact .nil
  | cons entry Γ ih =>
    cases entry with
    | lock m => exact .lock (ih X Y)
    | binding s =>
      simp only [splitContext]
      by_cases hx : 0 ∈ X <;> by_cases hy : 0 ∈ Y <;> cases s <;>
        simp only [hx, hy, ↓reduceIte, and_self, true_and, false_and, Option.map,
          Scheme.share] <;>
        solve_by_elim [UsageSplit.drop, UsageSplit.left, UsageSplit.right, UsageSplit.share]

theorem lookupScheme_sound {Γ i s} (h : lookupScheme Γ i = .success s) :
    Lookup Γ i s := by
  induction Γ generalizing i s with
  | nil => cases h
  | cons entry Γ ih =>
    cases entry with
    | binding b =>
      cases i with
      | zero => cases b <;> cases h; exact .here
      | succ i => exact .there (ih h)
    | lock m =>
      simp only [lookupScheme] at h
      cases he : lookupScheme Γ i <;> simp [he, bind, pure, RunResult.bind] at h
      exact h ▸ Lookup.locked (ih he)

theorem Lookup.lookupScheme {Γ i s} (h : Lookup Γ i s) :
    lookupScheme Γ i = .success s := by
  induction h <;> simp_all [ModalityInference.lookupScheme, Scheme.lock, bind, pure, RunResult.bind]

end ModalityInference
