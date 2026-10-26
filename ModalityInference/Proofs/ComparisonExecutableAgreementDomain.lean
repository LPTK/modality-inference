import ModalityInference.Proofs.ComparisonExecutableAgreement
import ModalityInference.Proofs.ComparisonObserverRangeEncoding

/-! Domain representations can be changed before finite embedding validation.
The encoding need not cover every target value: the checked target list is
exactly the image of the source enumeration. -/
namespace ModalityInference.ComparisonExecutableAgreement

variable {D E M O : Type*}

structure DomainMap (f : D → E) (source : Operations D M O) (target : Operations E M O) : Prop where
  domainLe : ∀ x y, target.domainLe (f x) (f y) = source.domainLe x y
  indexLe : target.indexLe = source.indexLe
  join : ∀ x y, target.join (f x) (f y) = f (source.join x y)
  meet : ∀ x y, target.meet (f x) (f y) = f (source.meet x y)
  mul : target.mul = source.mul
  action : ∀ m x, target.action m (f x) = f (source.action m x)
  prod : ∀ x y, target.prod (f x) (f y) = f (source.prod x y)
  sum : ∀ x y, target.sum (f x) (f y) = f (source.sum x y)
  fn : ∀ x y, target.fn (f x) (f y) = f (source.fn x y)
  vectorProd : target.vectorProd = source.vectorProd
  vectorSum : target.vectorSum = source.vectorSum
  vectorFn : target.vectorFn = source.vectorFn

theorem check_map (f : D → E) (source : Operations D M O) (target : Operations E M O)
    (h : DomainMap f source target) (values : List D) (indices : List M) (observations : List O)
    (j : E → Vector M O) :
    check (values.map f) indices observations target j =
      check values indices observations source (fun x => j (f x)) := by
  simp only [check,indexCheck,latticeCheck,reflectCheck,actionCheck,constructorCheck,
    List.all_map,Function.comp_def,h.domainLe,h.indexLe,h.join,h.meet,h.mul,h.action,
    h.prod,h.sum,h.fn,h.vectorProd,h.vectorSum,h.vectorFn]

end ModalityInference.ComparisonExecutableAgreement

namespace ModalityInference.ComparisonObserverRangeEncoding

open ComparisonObserverMachineCheck

variable {count : Nat} {data : Fin count → Description (Fin count)}
  {types : List TypeVar} {modes : List ModVar}

theorem map_values_pack :
    (values (types := types) (modes := modes) (data := data)).map pack = vectors data := by
  simp [values,List.map_map]

end ModalityInference.ComparisonObserverRangeEncoding
