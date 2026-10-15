import ModalityInference.ComparisonJointHorn

/-! Linear state clauses for the existing propagation obligations. State atoms
occupy a finite prefix; all guard atoms are shifted beyond it. This encoding
retains the symbolic guard CNFs without enumerating their interpretations. -/
namespace ModalityInference.ComparisonJointEncoding

open ComparisonPropagation

def prepend (state : Clause) (guards : CNF) : CNF :=
  guards.map (state ++ ·)

def encode (obligation : Obligation count) : CNF :=
  match obligation with
  | .lower i condition =>
      prepend [(i.val, true)] (rename (count + ·) (negate condition))
  | .edge i j condition =>
      prepend [(i.val, false), (j.val, true)] (rename (count + ·) (negate condition))
  | .upper i condition =>
      prepend [(i.val, false)] (rename (count + ·) condition)
  | .check condition => rename (count + ·) condition

def encodeAll (obligations : List (Obligation count)) : CNF :=
  obligations.flatMap encode

end ModalityInference.ComparisonJointEncoding
