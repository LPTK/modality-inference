import ModalityInference.Proofs.ComparisonFiniteCertificateInterpretation
import ModalityInference.Proofs.ComparisonFiniteCertificateChecks
import ModalityInference.Proofs.ComparisonExecutableDefinedAgreement

/-! Accepted finite certificates validate every original algebra rule. Their
separating query therefore refutes the original comparison, including contexts
with partial raw subtype assumptions. -/
namespace ModalityInference.ComparisonFiniteCertificate.Candidate

open ComparisonFiniteControlEncoding ComparisonExecutableControls
  ComparisonRelativeCoordinates ComparisonExecutableDefinedAgreement

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)

theorem codeAgreement (h : C.structureCheck = true) :
    CodeDefinedAgreement (C.codeModel h) (C.modal h) (C.range h) (C.embedding h) where
  controls _ _ := rfl
  reflect := C.embedding_reflect h
  atom _ := rfl
  unit := rfl
  credit := rfl
  action := C.embedding_shift h
  prod x y := by
    ext m o
    exact (congrFun (ComparisonExecutableTables.extend_eq C.obs C.obs_mem C.embed order false false
      (C.prodAt none) order_refl order_trans (C.prodAt_valid h none) m
      (C.embedding h x m) (C.embedding h y m)) o).symm.trans
        (congrFun (congrFun ((C.embedding_valid h).prod x y) m) o)
  sum x y := by
    ext m o
    exact (congrFun (ComparisonExecutableTables.extend_eq C.obs C.obs_mem C.embed order false false
      (C.sumAt none) order_refl order_trans (C.sumAt_valid h none) m
      (C.embedding h x m) (C.embedding h y m)) o).symm.trans
        (congrFun (congrFun ((C.embedding_valid h).sum x y) m) o)
  fn x y := by
    ext m o
    exact (congrFun (ComparisonExecutableTables.extend_eq C.obs C.obs_mem C.embed future true false
      C.fnRows future_refl future_trans (C.fn_valid h) m
      (C.embedding h x 1) (C.embedding h y 1)) o).symm.trans
        (congrFun (congrFun ((C.embedding_valid h).fn x y) m) o)

theorem algebra_sound (hc : C.check = true) {a b : CompareTy} (hab : AlgebraSubtype Δ a b) :
    C.data.eval a none ≤ C.data.eval b none := by
  obtain ⟨hs,hbounds⟩ := C.check_correct.mp hc
  have hb : ∀ a b, Constraint.sub a b ∈ Δ → (C.codeModel hs).Related (.ofTy a) (.ofTy b) := by
    intro a b hab
    have hh := hbounds a b hab
    rw [C.evalRaw_eq hs a,C.evalRaw_eq hs b] at hh
    exact hh
  rw [C.eval_eq hs a none,C.eval_eq hs b none]
  exact CodeDefinedAgreement.algebra_sound (C.codeModel hs) (C.modal hs) (C.range hs)
    (C.names_valid hs) (C.embedding hs) (C.codeAgreement hs) hb hab

theorem separates_sound {a b : CompareTy} (hc : C.separates a b = true) :
    ¬ AlgebraSubtype Δ a b := by
  obtain ⟨hcheck,hnot⟩ := (C.separates_correct a b).mp hc
  exact fun hab => hnot (C.algebra_sound hcheck hab)

end ModalityInference.ComparisonFiniteCertificate.Candidate
