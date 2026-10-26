import ModalityInference.ComparisonExecutableRangeAgreement
import ModalityInference.Proofs.ComparisonExecutableAgreementDomain
import ModalityInference.Proofs.ComparisonFiniteControlRange
import ModalityInference.Proofs.ComparisonFiniteControlEncoding

/-! Validation on raw admitted bit vectors is exactly validation on the full
semantic range algebra. No assertion is made about excluded bit vectors. -/
namespace ModalityInference.ComparisonExecutableRangeAgreement

open ComparisonExecutableAgreement ComparisonObserverRangeEncoding ComparisonObserverMachineCheck
  ComparisonObserverMachine

variable {count : Nat} {M O : Type*} {Δ : Bounds}
  {data : Fin count → Description (Fin count)} {types : List TypeVar} {modes : List ModVar}
  (hr : RangeClosed Δ (nodes types modes data))
  (indexLe : M → M → Bool) (mul : M → M → M) (labels : M → ModExpr)
  (hlabels : ∀ m, Entails Δ (.defined (labels m)))
  (vectorProd vectorSum vectorFn : Vector M O → Vector M O → Vector M O)

def semanticOperations : Operations (ComparisonObserverFiniteRange.Value (nodes types modes data)) M O where
  domainLe x y := ComparisonObserverRangeEncoding.le (pack x) (pack y)
  indexLe := indexLe
  join := (· ⊔ ·)
  meet := (· ⊓ ·)
  mul := mul
  action m := ComparisonObserverFiniteRange.modal hr (labels m) (hlabels m)
  prod := ComparisonObserverFiniteRange.op hr .prod
  sum := ComparisonObserverFiniteRange.op hr .sum
  fn := ComparisonObserverFiniteRange.op hr .fn
  vectorProd := vectorProd
  vectorSum := vectorSum
  vectorFn := vectorFn

theorem operations_domainMap : DomainMap pack
    (semanticOperations hr indexLe mul labels hlabels vectorProd vectorSum vectorFn)
    (rawOperations data modes indexLe mul labels vectorProd vectorSum vectorFn) where
  domainLe _ _ := rfl
  indexLe := rfl
  join x y := (pack_sup x y).symm
  meet x y := (pack_inf x y).symm
  mul := rfl
  action _ _ := rfl
  prod x y := (pack_op hr .prod x y).symm
  sum x y := (pack_op hr .sum x y).symm
  fn x y := (pack_op hr .fn x y).symm
  vectorProd := rfl
  vectorSum := rfl
  vectorFn := rfl

theorem check_eq (indices : List M) (observations : List O) (j : Bits count → Vector M O) :
    check (vectors data) indices observations
      (rawOperations data modes indexLe mul labels vectorProd vectorSum vectorFn) j =
    check (values (types := types) (modes := modes) (data := data)) indices observations
      (semanticOperations hr indexLe mul labels hlabels vectorProd vectorSum vectorFn)
      (fun x => j (pack x)) := by
  rw [← map_values_pack (types := types) (modes := modes)]
  exact check_map pack _ _
    (operations_domainMap hr indexLe mul labels hlabels vectorProd vectorSum vectorFn) _ _ _ _

theorem check_correct (indices : List M) (observations : List O)
    (hm : ∀ m, m ∈ indices) (ho : ∀ o, o ∈ observations) (j : Bits count → Vector M O) :
    check (vectors data) indices observations
      (rawOperations data modes indexLe mul labels vectorProd vectorSum vectorFn) j = true ↔
    Valid (semanticOperations hr indexLe mul labels hlabels vectorProd vectorSum vectorFn)
      (fun x => j (pack x)) := by
  rw [check_eq hr indexLe mul labels hlabels vectorProd vectorSum vectorFn]
  exact ComparisonExecutableAgreement.check_correct _ _ _ mem_values hm ho _ _

theorem semantic_domainLe (x y : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    (semanticOperations hr indexLe mul labels hlabels vectorProd vectorSum vectorFn).domainLe x y = true ↔
      x ≤ y :=
  (ComparisonObserverRangeEncoding.le_correct (pack x) (pack y)).trans (pack_le x y)

theorem modal_decode {names : List ModVar} (hv : ModalValid Δ (nodes types modes data))
    (c : ComparisonFiniteControlEncoding.Code Δ names)
    (x : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    ComparisonObserverFiniteRange.modal hr (ComparisonFiniteControlEncoding.expression c)
      (ComparisonFiniteControlEncoding.expression_defined c) x =
      ComparisonFiniteControlRange.action hv hr (ComparisonFiniteControlEncoding.decode c) x :=
  (ComparisonFiniteControlRange.action_encode hv hr _ _ _ x).symm

end ModalityInference.ComparisonExecutableRangeAgreement
