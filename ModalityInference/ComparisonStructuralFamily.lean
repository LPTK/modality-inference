import ModalityInference.ComparisonStructuralMatrix
import ModalityInference.ComparisonControls

/-! Finite constructor families share one parent observation and one modality
assignment. Child action polynomials are interpreted directly against the
parent matrix; no independent child modality assignments are introduced. -/
namespace ModalityInference.ComparisonStructuralFamily

open ComparisonControls

def literalFormula (value : Nat → BoolExpr) (literal : Literal) : BoolExpr :=
  if literal.2 then value literal.1 else .imp (value literal.1) (.const false)

def clauseFormula (dual : Bool) (value : Nat → BoolExpr) (clause : Clause) : BoolExpr :=
  if dual then .all (clause.map (literalFormula value))
  else .any (clause.map (literalFormula value))

def cnfFormula (dual : Bool) (value : Nat → BoolExpr) (clauses : CNF) : BoolExpr :=
  if dual then .any (clauses.map (clauseFormula dual value))
  else .all (clauses.map (clauseFormula dual value))

/-- The function domain uses the dual outer and inner lattice operations. -/
def matrixFormula (atom : Fin rows → Fin cols → Nat) (leftDual : Bool)
    (left right : CNF) : BoolExpr :=
  cnfFormula leftDual (fun i =>
    if hi : i < rows then
      cnfFormula false (fun j =>
        if hj : j < cols then .atom (atom ⟨i, hi⟩ ⟨j, hj⟩) else .const false) right
    else .const false) left

/-- Each acted matrix is observed through the same parent coordinate and the
same symbolic modality atoms. -/
def familyTheory (coordinate : Coordinate) (modeAtom : Nat → Nat)
    (base : Fin rows → Fin cols → Nat) (labels : Vector ModExpr count)
    (acted : Fin count → Fin rows → Fin cols → Nat) : BoolExpr :=
  .and (ComparisonStructuralMatrix.theory base)
    (.all ((List.finRange count).flatMap fun k =>
      (List.finRange rows).flatMap fun i =>
        (List.finRange cols).map fun j =>
          .equal (.atom (acted k i j))
            (coordinate.modalWith modeAtom (.atom (base i j)) labels[k])))

/-- Certificates for the finite child polynomials obtained by applying one
outer action to each child basis entry. -/
structure Absorption (rows cols : Nat) where
  mode : ModExpr
  left : Vector CNF rows
  right : Vector CNF cols
  deriving Repr

def Absorption.formula (a : Absorption rows cols) (coordinate : Coordinate)
    (modeAtom : Nat → Nat) (base : Fin rows → Fin cols → Nat) : BoolExpr :=
  .all ((List.finRange rows).flatMap fun i =>
    (List.finRange cols).map fun j =>
      .equal (coordinate.modalWith modeAtom (.atom (base i j)) a.mode)
        (coordinate.modalWith modeAtom (matrixFormula base false a.left[i] a.right[j]) a.mode))

def compileFamily (fuel : Nat) (coordinate : Coordinate) (modeAtom : Nat → Nat)
    (base : Fin rows → Fin cols → Nat) (labels : Vector ModExpr count)
    (acted : Fin count → Fin rows → Fin cols → Nat) : RunResult CNF :=
  CompactCNF.toCNF fuel true (familyTheory coordinate modeAtom base labels acted)

def compileAbsorption (fuel : Nat) (a : Absorption rows cols) (coordinate : Coordinate)
    (modeAtom : Nat → Nat) (base : Fin rows → Fin cols → Nat) : RunResult CNF :=
  CompactCNF.toCNF fuel true (a.formula coordinate modeAtom base)

end ModalityInference.ComparisonStructuralFamily
