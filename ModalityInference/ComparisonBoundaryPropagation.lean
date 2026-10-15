import ModalityInference.ComparisonParametricPropagation

/-! Eliminate internal coordinate states while retaining nominal boundary states.
Source observations are frozen as signed parameters, so each propagated path
preserves its source and all mode parameters. Upper obligations use universal
symbolic abstraction; reconstructed coordinates use relational images. -/
namespace ModalityInference.ComparisonBoundaryPropagation

open ComparisonPropagation ComparisonSelectorPropagation

/-- A source observation is retained as complementary parameter coordinates. -/
def sourceEquality (heads parameters : Nat) : CNF :=
  (List.range heads).flatMap fun i =>
    [[(i, false), (heads + 2 * parameters + 2 * i, true)],
     [(heads + 2 * parameters + 2 * i, false), (i, true)]]

def sourceProgram (heads parameters : Nat) (program : Program count) (source : Fin count) : Program count :=
  { program with lower := Vector.ofFn fun v =>
      if v == source then sourceEquality heads parameters else [[]] }

def pathClosure (heads parameters : Nat) (program : Program count) (source : Fin count) : Store count :=
  ComparisonParametricPropagation.closure heads (parameters + heads)
    (sourceProgram heads parameters program source)

/-- Decode a frozen source-head pair to a signed source observation, while
ordinary head/parameter atoms become target observations. -/
def decodeLiteral (heads parameters : Nat) (literal : Literal) : Literal :=
  let size := heads + 2 * parameters
  if literal.1 < size then (2 * literal.1 + 1, literal.2)
  else (2 * ((literal.1 - size) / 2),
    if (literal.1 - size) % 2 == 0 then literal.2 else !literal.2)

def decodeRelation (heads parameters : Nat) (clauses : CNF) : CNF :=
  clauses.map (List.map (decodeLiteral heads parameters))

def pathRelation (heads parameters : Nat) (program : Program count)
    (source target : Fin count) : CNF :=
  decodeRelation heads parameters (pathClosure heads parameters program source)[target]

def pathWorld (heads parameters : Nat) (world : Nat → Bool) (v : Nat) : Bool :=
  let size := heads + 2 * parameters
  if v < size then world (2 * v + 1)
  else if (v - size) % 2 == 0 then world (2 * ((v - size) / 2))
    else !world (2 * ((v - size) / 2))

def pathChoice (parameters : Nat) (choice source : Nat → Bool) (i : Nat) : Bool :=
  if i < parameters then choice i else source (i - parameters)

def pairWorld (left right : Nat → Bool) (v : Nat) : Bool :=
  if v % 2 == 0 then left (v / 2) else right (v / 2)

def allTargets (clauses : CNF) : CNF :=
  rename (· / 2) (SymbolicCNF.abstract (fun v => v % 2 == 0) clauses)

def allClauses (clauses : List CNF) : CNF := clauses.foldr meet []

def anyClauses (clauses : List CNF) : CNF := clauses.foldr join [[]]

def guardedPath (heads parameters : Nat) (program : Program count) (source target : Fin count) : CNF :=
  guardRelation heads parameters (pathRelation heads parameters program source target)

def summarize (heads parameters : Nat) (program : Program count)
    (boundary : Vector (Fin count) retained) : Program retained where
  lower := Vector.ofFn fun v => (ComparisonParametricPropagation.closure heads parameters program)[boundary[v]]
  edges := (List.finRange retained).flatMap fun source => (List.finRange retained).map fun target =>
    ⟨source, target, guardedPath heads parameters program boundary[source] boundary[target]⟩
  upper := Vector.ofFn fun source => allClauses ((List.finRange count).map fun target =>
    allTargets (implies (guardedPath heads parameters program boundary[source] target)
      (rename (fun v => 2 * v + 1) program.upper[target])))
  checks := meet program.checks (allClauses ((List.finRange count).map fun v =>
    implies (ComparisonParametricPropagation.closure heads parameters program)[v] program.upper[v]))

def reconstruct (heads parameters : Nat) (program : Program count)
    (boundary : Vector (Fin count) retained) (store : Store retained) : Store count :=
  Vector.ofFn fun target => join (ComparisonParametricPropagation.closure heads parameters program)[target]
    (anyClauses ((List.finRange retained).map fun source => image (heads + 2 * parameters)
      (guardedPath heads parameters program boundary[source] target) store[source]))

def witness (heads parameters : Nat) (choice : Nat → Bool) (program : Program count)
    (boundary : Vector (Fin count) retained) (store : Store retained) : Store count :=
  specializeStore heads choice (reconstruct heads parameters program boundary store)

end ModalityInference.ComparisonBoundaryPropagation
