import ModalityInference.ComparisonJointAssembly
import ModalityInference.ComparisonTupleWitness

/-! Rebase both coordinate stores into one shared constant and scalar namespace,
then reconstruct a finite type using only the supplied basis's modality names. -/
namespace ModalityInference.ComparisonJointAssemblyReification

open ComparisonPropagation ComparisonJointAssembly ComparisonControls

/-- The common parameter prefix contains every selected constant exactly once. -/
def parameter (embedding : Fin selectors → Fin constants) (i : Nat) : Nat :=
  if hi : i < selectors then (embedding ⟨i, hi⟩).val else constants + (i - selectors)

def rebaseAtom (heads : Nat) (embedding : Fin selectors → Fin constants) (i : Nat) : Nat :=
  if i < heads then i
  else heads + 2 * parameter embedding ((i - heads) / 2) + (i - heads) % 2

def rebase (heads : Nat) (embedding : Fin selectors → Fin constants) (clauses : CNF) : CNF :=
  rename (rebaseAtom heads embedding) clauses

/-- Unused scalar inputs are fixed uniformly; original permitted names remain
symbolic in the same returned modality expressions. -/
def projectAtom (allowed : List ModVar) (i : Nat) : BoolExpr :=
  if allowed.contains (SymbolicModes.atomVariable i) then .atom i else .const false

def projectExpression (allowed : List ModVar) (e : BoolExpr) : BoolExpr :=
  SymbolicCNF.substitute (projectAtom allowed) e

/-- Normalize only the stored flexible images. Non-flexible substitution
lookups remain literal identities. -/
def projectElimination (allowed : List ModVar) (solution : SymbolicModes.Elimination flex) :
    SymbolicModes.Elimination flex where
  values := solution.values.map (projectExpression allowed)
  obligation := projectExpression allowed solution.obligation

def values (allowed : List ModVar) (result : Result input count flex) (i : Nat) : BoolExpr :=
  if hi : i < constantCount input then .const result.solution.constants[i]
  else projectExpression allowed (result.solution.modes.substitute (i - constantCount input))

def scalars (b : Basis) (result : Result input count flex) : Nat → BoolExpr :=
  ComparisonTupleWitness.signed b.heads.length (values b.modes result)

def leaf (b : Basis) (result : Result input count flex) (i : Fin count) : Option CompareTy :=
  ComparisonTupleWitness.reconstructWith b (scalars b result) result.solution.types[i]
    (rebase b.heads.length (localityEmbedding input) result.locality[ComparisonJointGroup.state .locality i])
    (rebase b.heads.length (otherEmbedding input) result.other[ComparisonJointGroup.state .affinity i])
    (rebase b.heads.length (otherEmbedding input) result.other[ComparisonJointGroup.state .uniqueness i])

end ModalityInference.ComparisonJointAssemblyReification
