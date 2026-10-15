import ModalityInference.ComparisonPropagation

/-! Normalize complementary parameter coordinates before Boolean negation.
Point clauses use one signed literal per parameter; relational clauses use the
same source parameter at both observations. Head coordinates remain distinct. -/
namespace ModalityInference.ComparisonSliceCNF

def pointLiteral (heads parameters : Nat) (literal : Literal) : Literal :=
  if heads ≤ literal.1 ∧ literal.1 < heads + 2 * parameters then
    (heads + 2 * ((literal.1 - heads) / 2),
      if (literal.1 - heads) % 2 = 0 then literal.2 else !literal.2)
  else literal

def relationLiteral (heads parameters : Nat) (literal : Literal) : Literal :=
  if heads ≤ literal.1 / 2 ∧ literal.1 / 2 < heads + 2 * parameters then
    (2 * (heads + 2 * ((literal.1 / 2 - heads) / 2)),
      if (literal.1 / 2 - heads) % 2 = 0 then literal.2 else !literal.2)
  else literal

def point (heads parameters : Nat) (clauses : CNF) : CNF :=
  CompactCNF.clean (clauses.map (List.map (pointLiteral heads parameters)))

def relation (heads parameters : Nat) (clauses : CNF) : CNF :=
  CompactCNF.clean (clauses.map (List.map (relationLiteral heads parameters)))

/-- A finite normalization budget covering all input atoms. -/
def budget (clauses : CNF) : Nat := (CNFPropagation.atoms clauses).foldl max 0 + 1

/-- Normalize the residual's premises before distributing their negation. -/
def residual (heads parameters : Nat) (program : ComparisonPropagation.Program count)
    (store : ComparisonPropagation.Store count) : CNF :=
  ComparisonPropagation.residual
    { program with
      upper := Vector.ofFn fun v => point heads parameters program.upper[v]
      checks := point heads parameters program.checks }
    (Vector.ofFn fun v => point heads parameters store[v])

end ModalityInference.ComparisonSliceCNF
