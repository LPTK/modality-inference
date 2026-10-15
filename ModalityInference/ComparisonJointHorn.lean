import ModalityInference.ComparisonPropagation

/-! Symbolic compilation of unary state clauses into propagation obligations.
The clauses may contain unrestricted guard atoms alongside one state atom of
each polarity. State selection scans clause syntax; it does not choose witnesses.
-/
namespace ModalityInference.ComparisonJointHorn

/-- Select the single state of a polarity; duplicate occurrences have the same index. -/
def stateIndex (decode : Nat → Option (Fin count)) (polarity : Bool) (c : Clause) :
    Option (Fin count) :=
  (c.find? fun literal => (decode literal.1).isSome && literal.2 == polarity).bind
    (fun literal => decode literal.1)

def guards (decode : Nat → Option (Fin count)) (c : Clause) : Clause :=
  c.filter fun literal => (decode literal.1).isNone

/-- A linear state clause is a lower bound, an edge, an upper bound, or a fixed check. -/
def compileClause (decode : Nat → Option (Fin count)) (c : Clause) :
    ComparisonPropagation.Obligation count :=
  let condition : CNF := [guards decode c]
  match stateIndex decode false c, stateIndex decode true c with
  | none, none => .check condition
  | none, some target => .lower target (ComparisonPropagation.negate condition)
  | some source, none => .upper source condition
  | some source, some target => .edge source target (ComparisonPropagation.negate condition)

end ModalityInference.ComparisonJointHorn
