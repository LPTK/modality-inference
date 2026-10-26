import ModalityInference.ComparisonExecutableSuffix

/-! Syntax evaluation over supplied executable finite operations. Literal
partial prefixes and first-key frozen lookup retain their exact syntax. -/
namespace ModalityInference.ComparisonExecutableSyntax

structure Data (M V : Type*) where
  total : ModExpr → Bool
  control : ModExpr → M
  shift : M → V → V
  prod : Option ModExpr → V → V → V
  sum : Option ModExpr → V → V → V
  fn : V → V → V
  join : V → V → V
  meet : V → V → V
  atom : TypeVar → V
  unit : V
  credit : V
  bottom : V
  frozen : List (CompareTy × V)

namespace Data

variable {M V : Type*} (E : Data M V)

def frozenValue (a : CompareTy) : V :=
  ((E.frozen.find? (fun row => decide (row.1 = a))).map Prod.snd).getD E.bottom

def eval (E : Data M V) : CompareTy → Option ModExpr → V
  | .modal a m, none =>
      let s := ComparisonExecutableSuffix.normalize E.total m
      E.shift (E.control s.control) (E.eval a s.literal)
  | .modal a m, some p => E.eval a (some (.compose m p))
  | .prod a b, p => E.prod p (E.eval a p) (E.eval b p)
  | .sum a b, p => E.sum p (E.eval a p) (E.eval b p)
  | .fn a b, none => E.fn (E.eval a none) (E.eval b none)
  | .fn a b, some p => E.frozenValue (.modal (.fn a b) p)
  | .join a b, none => E.join (E.eval a none) (E.eval b none)
  | .join a b, some p => E.frozenValue (.modal (.join a b) p)
  | .meet a b, none => E.meet (E.eval a none) (E.eval b none)
  | .meet a b, some p => E.frozenValue (.modal (.meet a b) p)
  | .var v, none => E.atom v
  | .unit, none => E.unit
  | .credit, none => E.credit
  | .var v, some p => E.frozenValue (.modal (.var v) p)
  | .unit, some p => E.frozenValue (.modal .unit p)
  | .credit, some p => E.frozenValue (.modal .credit p)

def evalRaw (a : Ty) : V := E.eval (.ofTy a) none

end Data

def annotations : CompareTy → List ModExpr
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => annotations a ++ annotations b
  | .modal a m => m :: annotations a

def totalTests (a : CompareTy) : List ModExpr := annotations a |>.flatMap ComparisonExecutableSuffix.tests

def controlLabels (total : ModExpr → Bool) (a : CompareTy) : List ModExpr :=
  annotations a |>.map fun m => (ComparisonExecutableSuffix.normalize total m).control

end ModalityInference.ComparisonExecutableSyntax
