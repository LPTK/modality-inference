import ModalityInference.ComparisonExecutableAgreement
import ModalityInference.ComparisonObserverRangeEncoding

/-! Primitive operations for checking a defined embedding on the admitted
Boolean vectors of a described observer machine. -/
namespace ModalityInference.ComparisonExecutableRangeAgreement

open ComparisonExecutableAgreement ComparisonObserverRangeEncoding ComparisonObserverMachineCheck

variable {count : Nat} {M O : Type*}

def rawOperations (data : Fin count → Description (Fin count)) (modes : List ModVar)
    (indexLe : M → M → Bool) (mul : M → M → M) (labels : M → ModExpr)
    (vectorProd vectorSum vectorFn : Vector M O → Vector M O → Vector M O) :
    Operations (Bits count) M O where
  domainLe := ComparisonObserverRangeEncoding.le
  indexLe := indexLe
  join := ComparisonObserverRangeEncoding.join
  meet := ComparisonObserverRangeEncoding.meet
  mul := mul
  action m := modal data modes (labels m)
  prod := op data .prod
  sum := op data .sum
  fn := op data .fn
  vectorProd := vectorProd
  vectorSum := vectorSum
  vectorFn := vectorFn

end ModalityInference.ComparisonExecutableRangeAgreement
