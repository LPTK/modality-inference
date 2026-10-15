import ModalityInference.ComparisonJointClauses
import ModalityInference.ComparisonJointModes

/-! Joint synthesis of nominal head polynomials and axis-respecting scalar
strategies. One ordered Boolean elimination chooses shared clause selectors;
the nominal and scalar witnesses are reconstructed from their symbolic closures. -/
namespace ModalityInference.ComparisonJointSolver

open ComparisonPropagation ComparisonJointClauses

def choices (selectors : Nat → Bool) (i : Nat) : Bool := selectors (2 * i + 1)

/-- Complementary nominal selector coordinates share one scalar selector atom. -/
def decodeLiteral (heads : Nat) (literal : Literal) : Literal :=
  (2 * ((literal.1 - heads) / 2) + 1,
    if (literal.1 - heads) % 2 == 0 then literal.2 else !literal.2)

def decodeCNF (heads : Nat) (clauses : CNF) : CNF :=
  clauses.map (List.map (decodeLiteral heads))

def scalarPreparation (side : Nat → Bool) (flex : List Nat)
    (clauses : List (JointClause heads count)) : ModalSynthesis.Prepared :=
  ComparisonJointModes.prepare side flex (modeClauses side true clauses) (modeClauses side false clauses)

def query (side : Nat → Bool) (flex : List Nat) (clauses : List (JointClause heads count)) : CNF :=
  decodeCNF heads (ComparisonSelectorPropagation.query heads (2 * clauses.length) (nominalProgram clauses)) ++
    (scalarPreparation side flex clauses).query

structure Result (count : Nat) (flex : List Nat) where
  types : Store count
  modes : SymbolicModes.Elimination flex

def witness (side : Nat → Bool) (flex : List Nat) (clauses : List (JointClause heads count))
    (selectors : Nat → Bool) : Result count flex where
  types := ComparisonSelectorPropagation.witness heads (2 * clauses.length) (choices selectors)
    (nominalProgram clauses)
  modes := ModalSynthesis.witness side flex (scalarPreparation side flex clauses) selectors

/-- The Boolean solve chooses constants only; the output retains symbolic type
polynomials and modality expressions over their permitted rigid inputs. -/
def run (fuel : Nat) (side : Nat → Bool) (flex : List Nat) (clauses : List (JointClause heads count)) :
    RunResult (Result count flex) := do
  let selectors ← CNFPropagation.solve fuel (query side flex clauses)
  return witness side flex clauses (CNFPropagation.valuation selectors)

end ModalityInference.ComparisonJointSolver
