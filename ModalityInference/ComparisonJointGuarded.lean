import ModalityInference.ComparisonJointSolver

/-! Shared constant guards in joint type and modality synthesis. Constants chosen
by earlier dependency separation remain in the same Boolean solve as the new
clause selectors, rather than becoming modality inputs. -/
namespace ModalityInference.ComparisonJointGuarded

open ComparisonPropagation ComparisonJointClauses

structure GuardedClause (heads count constants : Nat) where
  constants : List (Fin constants × Bool)
  head : HeadClause heads count
  modes : ModalityInference.Clause

def plain (clauses : List (GuardedClause heads count constants)) : List (JointClause heads count) :=
  clauses.map fun c => ⟨c.head, c.modes⟩

def constantAtom (length : Nat) (i : Fin constants) : Nat := 4 * length + 2 * i.val + 1

def modeClauses (side : Nat → Bool) (component : Bool)
    (clauses : List (GuardedClause heads count constants)) : CNF :=
  clauses.zipIdx.map fun (c, i) =>
    (c.constants.map fun literal => (constantAtom clauses.length literal.1, literal.2)) ++
    [(4 * i + 1, true), (4 * i + 3, !component)] ++
      (c.modes.filter fun literal => side literal.1 == component).map
        (fun literal => (2 * literal.1, literal.2))

def scalarPreparation (side : Nat → Bool) (flex : List Nat)
    (clauses : List (GuardedClause heads count constants)) : ModalSynthesis.Prepared :=
  ComparisonJointModes.prepare side flex (modeClauses side true clauses) (modeClauses side false clauses)

def query (side : Nat → Bool) (flex : List Nat)
    (clauses : List (GuardedClause heads count constants)) : CNF :=
  ComparisonJointSolver.decodeCNF heads
      (ComparisonSelectorPropagation.query heads (2 * clauses.length) (nominalProgram (plain clauses))) ++
    (scalarPreparation side flex clauses).query

structure Result (count constants : Nat) (flex : List Nat) where
  constants : Vector Bool constants
  types : Store count
  modes : SymbolicModes.Elimination flex

def witness (side : Nat → Bool) (flex : List Nat)
    (clauses : List (GuardedClause heads count constants)) (selectors : Nat → Bool) : Result count constants flex where
  constants := Vector.ofFn fun i => selectors (constantAtom clauses.length i)
  types := ComparisonSelectorPropagation.witness heads (2 * clauses.length)
    (ComparisonJointSolver.choices selectors) (nominalProgram (plain clauses))
  modes := ModalSynthesis.witness side flex (scalarPreparation side flex clauses) selectors

def run (fuel : Nat) (side : Nat → Bool) (flex : List Nat)
    (clauses : List (GuardedClause heads count constants)) : RunResult (Result count constants flex) := do
  let selectors ← CNFPropagation.solve fuel (query side flex clauses)
  return witness side flex clauses (CNFPropagation.valuation selectors)

end ModalityInference.ComparisonJointGuarded
