import ModalityInference.ComparisonGroups
import ModalityInference.ComparisonControls

/-! Symbolic opaque-leaf elimination. Coordinate selectors encode the four
modal actions; they are universally removed with type coordinates before the
remaining modality query is passed to uniform modality synthesis. -/
namespace ModalityInference.ComparisonElimination

open ComparisonPropagation

def literalFormula (literal : Literal) : BoolExpr :=
  if literal.2 then .atom literal.1 else .imp (.atom literal.1) (.const false)

def formula (clauses : CNF) : BoolExpr :=
  .all (clauses.map fun clause => .any (clause.map literalFormula))

def coordinateCases (first : Nat) : List (ComparisonControls.Coordinate × BoolExpr) :=
  let a := BoolExpr.atom first
  let b := BoolExpr.atom (first + 1)
  let na := BoolExpr.imp a (.const false)
  let nb := BoolExpr.imp b (.const false)
  [(.unaffected, .and na nb), (.locality, .and na b),
   (.affinity, .and a nb), (.uniqueness, .and a b)]

def controlsTheory (fuel : Nat) (basis : ComparisonControls.Basis) : RunResult CNF := do
  let count := basis.types.length
  let mut clauses := []
  for (coordinate, selector) in coordinateCases count do
    let next ← CompactCNF.toCNF fuel true
      (.imp selector (basis.theoryAt id id (count + 2 + ·) coordinate))
    clauses := meet clauses next
  return clauses

def lookupFin [BEq α] [LawfulBEq α] (xs : List α) (x : α) : Option (Fin xs.length) :=
  let i := xs.idxOf x
  if h : i < xs.length then some ⟨i, h⟩ else none

def leaf (basis : ComparisonControls.Basis) (names : List Nat) (v : TypeVar) :
    RunResult (Leaf names.length) :=
  match v with
  | .flex n => match lookupFin names n with
      | some i => .success (.flex i)
      | none => match basis.index (.head (.var v)) with
          | some i => .success (.fixed [[(i, true)]])
          | none => .rejected "fixed head missing from its comparison class"
  | .rigid _ => match basis.index (.head (.var v)) with
      | some i => .success (.fixed [[(i, true)]])
      | none => .rejected "rigid head missing from its comparison class"

def endpoint (basis : ComparisonControls.Basis) (names : List Nat)
    (a : ComparisonGroups.Atom) : RunResult (Endpoint names.length) := do
  return ⟨← leaf basis names a.head, a.mode⟩

def bound (basis : ComparisonControls.Basis) (names : List Nat)
    (a : ComparisonGroups.Inequality) : RunResult (Bound names.length) := do
  return ⟨← endpoint basis names a.1, ← endpoint basis names a.2⟩

structure Result where
  types : List (Nat × CompareTy)
  query : BoolExpr
  deriving Repr

def group (fuel : Nat) (assumptions required : Bounds) (g : ComparisonGroups.Group) :
    RunResult Result := do
  let first :: rest := g.heads | .rejected "comparison class has no fixed generator"
  let labels := ((g.assumptions ++ g.goals).flatMap fun (a, b) => [a.mode, b.mode]).dedup
  let names := (labels.flatMap ModExpr.freeVariables ++ assumptions.modeVariables ++
    required.modeVariables).dedup
  let basis : ComparisonControls.Basis :=
    ⟨.var first, rest.map CompareTy.var, names⟩
  let mut actions : List (ModExpr × Action) := []
  for label in labels do
    let lower ← ComparisonControls.low fuel basis label
    let upper ← ComparisonControls.high fuel basis label
    actions := (label, ⟨lower, upper⟩) :: actions
  let action := fun label => (actions.lookup label).getD ⟨[[]], []⟩
  let count := basis.types.length
  let mut theory ← controlsTheory fuel basis
  let guards ← CompactCNF.toCNF fuel true
    (SymbolicCNF.substitute (fun i => .atom (count + 2 + i))
      (.and (boundsModeFormula assumptions) (boundsModeFormula required)))
  theory := meet theory guards
  for pair in g.assumptions do
    let a ← endpoint basis [] pair.1
    let b ← endpoint basis [] pair.2
    match a.leaf, b.leaf with
    | .fixed x, .fixed y =>
        theory := meet theory (implies ((action a.mode).apply x) ((action b.mode).apply y))
    | .flex i, _ => nomatch i
    | _, .flex i => nomatch i
  let bounds ← g.goals.mapM (bound basis g.leaves)
  let program := compile count action theory bounds
  let result ← reduce basis.types program
  let residual := SymbolicCNF.abstract (fun i => count + 2 ≤ i) result.obligation
  return { types := g.leaves.zip result.images.toList
           query := formula (rename (· - (count + 2)) residual) }

def run (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (templates : ComparisonSkeleton.Templates)
    (reduced : ComparisonReduction.State) : RunResult Result := do
  let groups ← ComparisonGroups.collect p shapes templates reduced
  let mut types := []
  let mut queries := [.imp (boundsModeFormula p.assumptions) (boundsModeFormula reduced.modes)]
  for g in groups do
    let result ← group fuel p.assumptions reduced.modes g
    types := types ++ result.types
    queries := result.query :: queries
  return ⟨types, .all queries⟩

end ModalityInference.ComparisonElimination
