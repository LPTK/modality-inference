import ModalityInference.ComparisonJointGuarded
import ModalityInference.ComparisonSliceCNF

/-! Translate a parameterized boundary program into joint nominal/scalar clauses.
Head observations occupy a finite prefix. Each scalar parameter occupies a
complementary pair; relational guards use the same scalar parameters at their
source and target observations. -/
namespace ModalityInference.ComparisonJointSummary

open ComparisonPropagation ComparisonJointClauses

def headLiterals (size : Nat) (clause : Clause) : List (HeadLiteral size) :=
  clause.filterMap fun (i, polarity) =>
    if hi : i < size then some (⟨i, hi⟩, polarity) else none

def scalarLiteral (heads : Nat) (literal : Literal) : Literal :=
  ((literal.1 - heads) / 2,
    if (literal.1 - heads) % 2 == 0 then literal.2 else !literal.2)

def modeLiterals (heads : Nat) (clause : Clause) : Clause :=
  (clause.filter fun literal => heads ≤ literal.1).map (scalarLiteral heads)

def edgeModeLiterals (heads : Nat) (clause : Clause) : Clause :=
  (clause.filter fun literal => heads ≤ literal.1 / 2).map fun literal =>
    scalarLiteral heads (literal.1 / 2, literal.2)

def lower (heads : Nat) (target : Fin count) (condition : CNF) : List (JointClause heads count) :=
  (negate (ComparisonSliceCNF.point heads (ComparisonSliceCNF.budget condition) condition)).map fun clause =>
    ⟨.lower target (headLiterals heads clause), modeLiterals heads clause⟩

def edge (heads : Nat) (transition : Edge count) : List (JointClause heads count) :=
  (negate (ComparisonSliceCNF.relation heads (ComparisonSliceCNF.budget transition.relation)
    transition.relation)).map fun clause =>
    ⟨.edge transition.source transition.target (headLiterals (2 * heads) clause),
      edgeModeLiterals heads clause⟩

def upper (heads : Nat) (source : Fin count) (condition : CNF) : List (JointClause heads count) :=
  condition.map fun clause =>
    ⟨.upper source (headLiterals heads clause), modeLiterals heads clause⟩

def checks (heads : Nat) (condition : CNF) : List (JointClause heads count) :=
  condition.map fun clause =>
    ⟨.check (headLiterals heads clause), modeLiterals heads clause⟩

def compile (heads : Nat) (program : Program count) : List (JointClause heads count) :=
  (List.finRange count).flatMap (fun v => lower heads v program.lower[v]) ++
    program.edges.flatMap (edge heads) ++
    (List.finRange count).flatMap (fun v => upper heads v program.upper[v]) ++
    checks heads program.checks

/-- Earlier clause selectors are constants; ordinary scalar atoms remain
inputs to the axis-respecting modality strategy. -/
def constantParameters (decode : Nat → Sum (Fin constants) Nat) (clause : Clause) :
    List (Fin constants × Bool) :=
  clause.filterMap fun literal => match decode literal.1 with
    | .inl i => some (i, literal.2)
    | .inr _ => none

def modeParameters (decode : Nat → Sum (Fin constants) Nat) (clause : Clause) : Clause :=
  clause.filterMap fun literal => match decode literal.1 with
    | .inl _ => none
    | .inr i => some (i, literal.2)

def separateParameters (decode : Nat → Sum (Fin constants) Nat) (clause : JointClause heads count) :
    ComparisonJointGuarded.GuardedClause heads count constants :=
  ⟨constantParameters decode clause.modes, clause.head, modeParameters decode clause.modes⟩

def compileGuarded (heads : Nat) (decode : Nat → Sum (Fin constants) Nat) (program : Program count) :
    List (ComparisonJointGuarded.GuardedClause heads count constants) :=
  (compile heads program).map (separateParameters decode)

end ModalityInference.ComparisonJointSummary
