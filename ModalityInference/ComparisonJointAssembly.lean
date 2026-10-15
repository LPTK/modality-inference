import ModalityInference.ComparisonJointGroup
import ModalityInference.ComparisonJointAxisSummary

/-! Assemble an opaque group's nominal, coordinate, and scalar requirements
into one query. Both coordinate summaries share the same nominal boundary and
constant-selector vector; all scalar occurrences use one modality strategy. -/
namespace ModalityInference.ComparisonJointAssembly

open ComparisonPropagation ComparisonJointGroup ComparisonJointGuarded

def constantCount (input : Input) : Nat := input.locality.length + input.other.length + 1

def localityEmbedding (input : Input) (i : Fin (input.locality.length + 1)) :
    Fin (constantCount input) :=
  if h : i.val < input.locality.length then ⟨i.val + 1, by simp only [constantCount]; omega⟩
  else ⟨0, by simp [constantCount]⟩

def otherEmbedding (input : Input) (i : Fin (input.other.length + 1)) :
    Fin (constantCount input) :=
  if h : i.val < input.other.length then
    ⟨input.locality.length + i.val + 1, by simp only [constantCount]; omega⟩
  else ⟨0, by simp [constantCount]⟩

def boundary (count : Nat) : Vector (Fin (4 * count)) count :=
  Vector.ofFn (state .unaffected)

def modeBound (input : Input) : Nat :=
  (CNFPropagation.atoms (input.locality ++ input.other ++ input.scalar)).foldl max 0 + 1

def nominalState (count v : Nat) : Option (Fin count) :=
  if h : v < count then some ⟨v, h⟩ else none

def nominalProgram (count heads : Nat) (input : Input) : Program count :=
  ComparisonJointProgram.compile heads (nominalState count) (fun i => i - 4 * count) input.nominal

def scalarClauses (clauses : CNF) : List (GuardedClause heads count constants) :=
  clauses.map fun clause => ⟨[], .check [], clause⟩

/-- Odd atoms name local selectors; even atoms retain original scalar indices. -/
def oppositeParameter (selectors v : Nat) : Nat :=
  if v % 2 == 0 then selectors + v / 2 else v / 2

def oppositeClauses (side : Nat → Bool) (component : Bool) (count heads selectors : Nat)
    (embedding : Fin selectors → Fin constants) (clauses : CNF) :
    List (GuardedClause heads retained constants) :=
  (ComparisonJointAxes.otherClauses side component count heads clauses).map fun clause =>
    ComparisonJointSummary.separateParameters (ComparisonJointAxisSummary.decode embedding)
      ⟨.check [], clause.map fun literal => (oppositeParameter selectors literal.1, literal.2)⟩

def compile (side : Nat → Bool) (count heads : Nat) (input : Input) :
    List (GuardedClause heads count (constantCount input)) :=
  ComparisonJointSummary.compileGuarded heads (fun i => .inr i) (nominalProgram count heads input) ++
    ComparisonJointAxisSummary.compile side true (4 * count) heads
      (input.locality.length + 1) (modeBound input) (localityEmbedding input) input.locality (boundary count) ++
    ComparisonJointAxisSummary.compile side false (4 * count) heads
      (input.other.length + 1) (modeBound input) (otherEmbedding input) input.other (boundary count) ++
    oppositeClauses side true (4 * count) heads (input.locality.length + 1)
      (localityEmbedding input) input.locality ++
    oppositeClauses side false (4 * count) heads (input.other.length + 1)
      (otherEmbedding input) input.other ++ scalarClauses input.scalar

structure Result (input : Input) (count : Nat) (flex : List Nat) where
  solution : ComparisonJointGuarded.Result count (constantCount input) flex
  locality : Store (4 * count)
  other : Store (4 * count)

/-- The returned coordinate stores retain their selector and scalar parameters;
only parameters belonging to the opposite component are fixed to a baseline. -/
def reconstruct (side : Nat → Bool) (count heads : Nat) (input : Input)
    (solution : ComparisonJointGuarded.Result count (constantCount input) flex) : Result input count flex :=
  let baseline := fun i => (solution.modes.substitute i).eval (fun _ => false)
  let locality := ComparisonBoundaryPropagation.reconstruct heads
    (input.locality.length + 1 + modeBound input)
    (ComparisonJointAxisSummary.program side true (4 * count) heads
      (input.locality.length + 1) (modeBound input) input.locality) (boundary count) solution.types
  let other := ComparisonBoundaryPropagation.reconstruct heads
    (input.other.length + 1 + modeBound input)
    (ComparisonJointAxisSummary.program side false (4 * count) heads
      (input.other.length + 1) (modeBound input) input.other) (boundary count) solution.types
  ⟨solution,
    ComparisonJointAxisSummary.restrictStore side true heads (input.locality.length + 1) baseline locality,
    ComparisonJointAxisSummary.restrictStore side false heads (input.other.length + 1) baseline other⟩

def run (fuel : Nat) (side : Nat → Bool) (flex : List Nat) (count heads : Nat) (input : Input) :
    RunResult (Result input count flex) := do
  let solution ← ComparisonJointGuarded.run fuel side flex (compile side count heads input)
  return reconstruct side count heads input solution

end ModalityInference.ComparisonJointAssembly
