import ModalityInference.ComparisonAlgebra
import ModalityInference.ComparisonPropagation

/-! Finite constructor observations and their linear coordinate interpretation.
The compiler emits whole-parent rectangular equations; factorization inspects
finite basis entries and never enumerates Boolean valuations. -/
namespace ModalityInference.ComparisonStructuralMatrix

abbrev Table (rows cols : Nat) := Fin rows → Fin cols → Bool

inductive Projection (rows cols : Nat) where
  | left (values : Vector Bool rows)
  | right (values : Vector Bool cols)

def Projection.eval (projection : Projection rows cols) (i : Fin rows) (j : Fin cols) : Bool :=
  match projection with
  | .left values => values[i]
  | .right values => values[j]

/-- Inspect finite basis entries, selecting a varying row if there is one. -/
def factor (table : Table rows cols) : Projection rows cols :=
  if hc : 0 < cols then
    match (List.finRange rows).find? (fun i =>
      !((List.finRange cols).all fun j => table i j == table i ⟨0, hc⟩)) with
    | some i => .right (Vector.ofFn (table i))
    | none => .left (Vector.ofFn fun i => table i ⟨0, hc⟩)
  else .left (Vector.replicate rows false)

def Rectangular (table : Table rows cols) : Prop :=
  ∀ i i' j j',
    ((table i j || table i' j') = (table i j' || table i' j)) ∧
    ((table i j && table i' j') = (table i j' && table i' j))

/-- Constructor equations constrain whole parent observations at the finite
Cartesian product of child bases. Declared parent bounds use the same atoms. -/
def theory (atom : Fin rows → Fin cols → Nat) : BoolExpr :=
  .all ((List.finRange rows).flatMap fun i => (List.finRange rows).flatMap fun i' =>
    (List.finRange cols).flatMap fun j => (List.finRange cols).map fun j' =>
      .and
        (.equal (.or (.atom (atom i j)) (.atom (atom i' j')))
          (.or (.atom (atom i j')) (.atom (atom i' j))))
        (.equal (.and (.atom (atom i j)) (.atom (atom i' j')))
          (.and (.atom (atom i j')) (.atom (atom i' j)))))

def compile (fuel : Nat) (atom : Fin rows → Fin cols → Nat) : RunResult CNF :=
  CompactCNF.toCNF fuel true (theory atom)

/-- A contravariant child exchanges the meet and join layers of a positive CNF. -/
def clauseValue (dual : Bool) (values : Nat → Bool) (clause : Clause) : Bool :=
  if dual then clause.all (fun literal => values literal.1 == literal.2)
  else clause.any (fun literal => values literal.1 == literal.2)

def cnfValue (dual : Bool) (values : Nat → Bool) (clauses : CNF) : Bool :=
  if dual then clauses.any (clauseValue dual values)
  else clauses.all (clauseValue dual values)

def vectorValue (values : Vector Bool size) (i : Nat) : Bool :=
  (values.toList[i]?).getD false

/-- Interpret normalized child polynomials using the selected single coordinate. -/
def Projection.apply (projection : Projection rows cols) (leftDual : Bool)
    (left right : CNF) : Bool :=
  match projection with
  | .left values => cnfValue leftDual (vectorValue values) left
  | .right values => cnfValue false (vectorValue values) right

end ModalityInference.ComparisonStructuralMatrix
