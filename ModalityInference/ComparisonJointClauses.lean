import ModalityInference.ComparisonSelectorPropagation

/-! Linear nominal clauses with an independent scalar guard. Finite head indices
keep source and target observations separate from the constant clause selectors. -/
namespace ModalityInference.ComparisonJointClauses

open ComparisonPropagation ComparisonSelectorPropagation

abbrev HeadLiteral (size : Nat) := Fin size × Bool

def literals (guard : List (HeadLiteral size)) : Clause := guard.map fun literal => (literal.1.val, literal.2)

inductive HeadClause (heads count : Nat) where
  | lower (target : Fin count) (guard : List (HeadLiteral heads))
  | edge (source target : Fin count) (guard : List (HeadLiteral (2 * heads)))
  | upper (source : Fin count) (guard : List (HeadLiteral heads))
  | check (guard : List (HeadLiteral heads))

structure JointClause (heads count : Nat) where
  head : HeadClause heads count
  modes : Clause

/-- The negative coordinate of selector `2 * index` disables the nominal clause. -/
def headGuard (heads index : Nat) (guard : Clause) : Clause :=
  (heads + 4 * index + 1, true) :: guard

/-- Relational head guards see the selector at the target observation. -/
def edgeGuard (heads index : Nat) (guard : Clause) : Clause :=
  (2 * (heads + 4 * index + 1) + 1, true) :: guard

def addHead (heads index : Nat) (program : Program count) : HeadClause heads count → Program count
  | .lower target guard => program.add heads (.lower target (negate [headGuard heads index (literals guard)]))
  | .edge source target guard => { program with edges :=
      ⟨source, target, negate [edgeGuard heads index (literals guard)]⟩ :: program.edges }
  | .upper source guard => program.add heads (.upper source [headGuard heads index (literals guard)])
  | .check guard => program.add heads (.check [headGuard heads index (literals guard)])

def nominalProgram (clauses : List (JointClause heads count)) : Program count :=
  clauses.zipIdx.foldl (fun program entry => addHead heads entry.2 program entry.1.head) (Program.empty count)

/-- Two constant selectors choose nominal, locality, or affinity/uniqueness. -/
def modeClauses (side : Nat → Bool) (locality : Bool) (clauses : List (JointClause heads count)) : CNF :=
  clauses.zipIdx.map fun (clause, index) =>
    (4 * index + 1, true) :: (4 * index + 3, !locality) ::
      ((clause.modes.filter fun literal => side literal.1 == locality).map fun literal =>
        (2 * literal.1, literal.2))

end ModalityInference.ComparisonJointClauses
