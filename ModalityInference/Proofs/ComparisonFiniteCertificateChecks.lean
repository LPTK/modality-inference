import ModalityInference.ComparisonFiniteCertificate
import ModalityInference.Proofs.ComparisonExecutableAgreement

/-! The final finite boundary checks retain original whole raw assumptions and
compare the actual executable endpoint values. -/
namespace ModalityInference.ComparisonFiniteCertificate.Candidate

open ComparisonExecutableAgreement

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)

theorem vectorBelow_iff (x y : Coordinates Δ names C.observations) :
    vectorBelow (indices Δ names) C.obs x y = true ↔ x ≤ y :=
  vectorBelow_correct _ _ (fun m => List.mem_map.mpr ⟨m.index,by simp,rfl⟩) (by simp [obs]) x y

theorem boundsCheck_correct : C.boundsCheck = true ↔
    ∀ a b, Constraint.sub a b ∈ Δ → C.data.evalRaw a ≤ C.data.evalRaw b := by
  simp only [boundsCheck,List.all_eq_true]
  constructor
  · intro h a b hab
    exact (C.vectorBelow_iff _ _).mp (h (.sub a b) hab)
  · intro h c hc
    cases c with
    | sub a b => exact (C.vectorBelow_iff _ _).mpr (h a b hc)
    | _ => rfl

theorem check_correct : C.check = true ↔ C.structureCheck = true ∧
    ∀ a b, Constraint.sub a b ∈ Δ → C.data.evalRaw a ≤ C.data.evalRaw b := by
  simp only [check,Bool.and_eq_true,boundsCheck_correct]

theorem separates_correct (a b : CompareTy) : C.separates a b = true ↔
    C.check = true ∧ ¬ C.data.eval a none ≤ C.data.eval b none := by
  simp only [separates,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,C.vectorBelow_iff]

end ModalityInference.ComparisonFiniteCertificate.Candidate
