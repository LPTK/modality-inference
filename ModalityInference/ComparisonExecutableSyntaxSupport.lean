import ModalityInference.ComparisonExecutableSyntax

/-! Finite lookup support follows the executable interpreter, including exact
literal prefixes after suffix normalization and frozen lookups. -/
namespace ModalityInference.ComparisonExecutableSyntax

inductive Access where
  | prod : Option ModExpr → Access
  | sum : Option ModExpr → Access
  | frozen : CompareTy → Access
  deriving DecidableEq

def accesses (total : ModExpr → Bool) : CompareTy → Option ModExpr → List Access
  | .modal a m, none => accesses total a (ComparisonExecutableSuffix.normalize total m).literal
  | .modal a m, some p => accesses total a (some (.compose m p))
  | .prod a b, p => .prod p :: (accesses total a p ++ accesses total b p)
  | .sum a b, p => .sum p :: (accesses total a p ++ accesses total b p)
  | .fn a b, none | .join a b, none | .meet a b, none =>
      accesses total a none ++ accesses total b none
  | .fn a b, some p => [.frozen (.modal (.fn a b) p)]
  | .join a b, some p => [.frozen (.modal (.join a b) p)]
  | .meet a b, some p => [.frozen (.modal (.meet a b) p)]
  | .var _, none | .unit, none | .credit, none => []
  | .var v, some p => [.frozen (.modal (.var v) p)]
  | .unit, some p => [.frozen (.modal .unit p)]
  | .credit, some p => [.frozen (.modal .credit p)]

def accessList (total : ModExpr → Bool) (queries : List (CompareTy × Option ModExpr)) :
    List Access := queries.flatMap fun query => accesses total query.1 query.2

def literalPrefixes (keys : List Access) : List ModExpr := keys.filterMap fun key => match key with
  | .prod p | .sum p => p
  | .frozen _ => none

def frozenKeys (keys : List Access) : List CompareTy := keys.filterMap fun key => match key with
  | .frozen a => some a
  | _ => none

def selectRows {α β : Type*} [DecidableEq α] (keys : List α) (rows : List (α × β)) : List (α × β) :=
  keys.filterMap fun key =>
    (rows.find? (fun row => decide (row.1 = key))).map fun row => (key, row.2)

end ModalityInference.ComparisonExecutableSyntax
