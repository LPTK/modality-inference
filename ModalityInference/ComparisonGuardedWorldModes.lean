import ModalityInference.ComparisonWorldModes

/-! Constant guards activate endpoint clauses. All active scalar blocks share
one modality strategy; inactive clauses may leave every world selector false. -/
namespace ModalityInference.ComparisonGuardedWorldModes
open ComparisonWorldClauses

structure Entry where
  guard : Clause
  clause : WorldClause
  deriving Inhabited

def clauses (entries : List Entry) : List WorldClause := entries.map Entry.clause

def externalIndex (total i : Nat) : Nat := selectorAtom (total+i) 0

def externalAtom (total i : Nat) : Nat := ComparisonWorldModes.worldConstant (externalIndex total i)

def externalValue (total : Nat) (selectors : Nat → Bool) (i : Nat) : Bool :=
  selectors (externalAtom total i)

def choices (entries : List Entry) : CNF :=
  entries.zipIdx.map fun (entry,i)=>
    entry.guard.map (fun literal=>(externalAtom entries.length literal.1,literal.2)) ++
      (blocks entry.clause).map (fun b=>(ComparisonWorldModes.worldConstant (selectorAtom i b),true))

def prepare (side : Nat → Bool) (flex : List Nat) (entries : List Entry) :=
  ComparisonWorldModes.prepare side flex (clauses entries)

def query (side : Nat → Bool) (flex : List Nat) (entries : List Entry) : CNF :=
  choices entries ++ (prepare side flex entries).query

def witness (side : Nat → Bool) (flex : List Nat) (entries : List Entry)
    (selectors : Nat → Bool) :=
  ComparisonWorldModes.witness side flex (clauses entries) selectors

end ModalityInference.ComparisonGuardedWorldModes
