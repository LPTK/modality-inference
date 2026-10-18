import ModalityInference.ComparisonWorldClauses
import ModalityInference.ComparisonSignedEndpoints
import ModalityInference.ComparisonPropagation

/-! Whole guarded signed clauses are split into nominal and scalar world
blocks after their state-point equations have been included in the theory.
Image calls occupy the nominal block; all scalar blocks retain identical local
atom names for the common modality strategy. -/
namespace ModalityInference.ComparisonSignedWorlds

open ComparisonSignedEndpoints ComparisonWorldClauses

def calls (clauses : List CompiledClause) : List Call :=
  (clauses.flatMap fun clause => clause.literals.map Prod.fst).dedup

def rawAtom (decode : Nat → Nat × Nat) (v : Nat) : Nat × Nat :=
  let atom := decode v
  if atom.1=0 then (0,2*atom.2) else atom

def rawClause (decode : Nat → Nat × Nat) (clause : ModalityInference.Clause) : WorldClause :=
  clause.map fun (v,p) => ((rawAtom decode v).1,((rawAtom decode v).2,p))

def imageClause (names : List Call) (clause : List (Call × Bool)) : WorldClause :=
  clause.map fun (call,p) => (0,(2*names.idxOf call+1,p))

def query (decode : Nat → Nat × Nat) (theory : CNF)
    (clauses : List CompiledClause) : List WorldClause :=
  clauses.flatMap fun clause =>
    (ComparisonPropagation.implies theory [clause.guard]).map fun guard =>
      rawClause decode guard ++ imageClause (calls clauses) clause.literals

/-- Shared antecedent negation and call indexing are computed once for the batch. -/
def queryCached (decode : Nat → Nat × Nat) (theory : CNF)
    (clauses : List CompiledClause) : List WorldClause :=
  match clauses with
  | [] => []
  | _::_ =>
      let opposite := ComparisonPropagation.negate theory
      let names := calls clauses
      clauses.flatMap fun clause =>
        (ComparisonPropagation.join opposite [clause.guard]).map fun guard =>
          rawClause decode guard ++ imageClause names clause.literals

@[csimp] theorem query_eq_queryCached : @query = @queryCached := by
  funext decode theory clauses
  cases clauses <;> rfl

end ModalityInference.ComparisonSignedWorlds
