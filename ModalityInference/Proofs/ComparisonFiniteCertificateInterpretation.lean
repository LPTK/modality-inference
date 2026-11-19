import ModalityInference.Proofs.ComparisonFiniteCertificateEmbedding
import ModalityInference.Proofs.ComparisonFiniteCertificateTables
import ModalityInference.Proofs.ComparisonExecutableSyntaxMap
import ModalityInference.Proofs.ComparisonExecutableScalarSyntax

/-! A checked certificate evaluates through invariant-preserving coordinates.
Forgetting those coordinates gives the actual executable array evaluator, so
no monotonicity assumption is imposed on arbitrary input arrays. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonFiniteControlEncoding ComparisonRelativeCoordinates ComparisonRelativeSyntax
  ComparisonExecutableControls ComparisonExecutableSyntax

namespace Candidate

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names)

def codeModel (h : C.structureCheck = true) :=
  C.model h (fun v => C.embedding h (ComparisonObserverFiniteRange.atom (C.range h) v))
    (C.embedding h (ComparisonObserverFiniteRange.unit (C.range h)))
    (C.embedding h (ComparisonObserverFiniteRange.credit (C.range h)))

def orderedData (h : C.structureCheck = true) : Data (Code Δ names) C.OrderedCoordinates where
  total := ScalarDecision.defined Δ
  control := project Δ names
  shift m x := shift ComparisonExecutableControls.mul_mono m x
  prod p := ComparisonExecutableTables.pair C.obs C.obs_mem C.embed order (C.prodAt p)
    order_refl order_trans (fun h => h) (C.prodAt_valid h p)
  sum p := ComparisonExecutableTables.pair C.obs C.obs_mem C.embed order (C.sumAt p)
    order_refl order_trans (fun h => h) (C.sumAt_valid h p)
  fn := ComparisonExecutableTables.fn C.obs C.obs_mem C.embed future C.fnRows
    future_refl future_trans order_future (C.fn_valid h)
  join := (· ⊔ ·)
  meet := (· ⊓ ·)
  atom v := C.embedding h (ComparisonObserverFiniteRange.atom (C.range h) v)
  unit := C.embedding h (ComparisonObserverFiniteRange.unit (C.range h))
  credit := C.embedding h (ComparisonObserverFiniteRange.credit (C.range h))
  bottom := ⊥
  frozen := C.frozenValues h

def orderedAgreement (h : C.structureCheck = true) :
    Agreement (C.orderedData h) (C.codeModel h) id id where
  shift _ _ := rfl
  prod p x y := ComparisonExecutableTables.pair_eq C.obs C.obs_mem C.embed order (C.prodAt p)
    order_refl order_trans (fun h => h) (C.prodAt_valid h p) x y
  sum p x y := ComparisonExecutableTables.pair_eq C.obs C.obs_mem C.embed order (C.sumAt p)
    order_refl order_trans (fun h => h) (C.sumAt_valid h p) x y
  fn x y := ComparisonExecutableTables.fn_eq C.obs C.obs_mem C.embed future C.fnRows
    future_refl future_trans order_future (C.fn_valid h) x y
  join _ _ := rfl
  meet _ _ := rfl
  atom _ := rfl
  unit := rfl
  credit := rfl
  bottom := rfl
  frozen := List.map_id _

def orderedDataMap (h : C.structureCheck = true) :
    DataMap (C.orderedData h) C.data (fun x => fun m => x m) id where
  total := rfl
  control _ := rfl
  shift _ _ := rfl
  prod _ _ _ := rfl
  sum _ _ _ := rfl
  fn _ _ := rfl
  join _ _ := rfl
  meet _ _ := rfl
  atom _ := rfl
  unit := rfl
  credit := rfl
  bottom := rfl
  frozen := C.frozenValues_map h

theorem ordered_eval_eq (h : C.structureCheck = true) (a : CompareTy) (p : Option ModExpr) :
    (C.orderedData h).eval a p = (C.codeModel h).denote a p :=
  (C.orderedAgreement h).eval_eq_scalar rfl (fun _ _ _ => rfl) p

theorem eval_eq (h : C.structureCheck = true) (a : CompareTy) (p : Option ModExpr) :
    C.data.eval a p = (fun m => (C.codeModel h).denote a p m) := by
  rw [← (C.orderedDataMap h).eval_eq a p,C.ordered_eval_eq h a p]

theorem evalRaw_eq (h : C.structureCheck = true) (a : Ty) :
    C.data.evalRaw a = (fun m => (C.codeModel h).denote (.ofTy a) none m) :=
  C.eval_eq h (.ofTy a) none

end Candidate
end ModalityInference.ComparisonFiniteCertificate
