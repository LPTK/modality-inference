import ModalityInference.ComparisonJointGuarded

/-! Reindex independent nominal groups into one shared modality query. -/
namespace ModalityInference.ComparisonJointReindex

open ComparisonPropagation ComparisonJointClauses ComparisonJointGuarded

def paired (f : Fin heads → Fin total) (i : Fin (2 * heads)) : Fin (2 * total) :=
  ⟨2 * (f ⟨i.val / 2, by omega⟩).val + i.val % 2, by
    have h := (f ⟨i.val / 2, by omega⟩).isLt
    omega⟩

def headClause (headsMap : Fin heads → Fin totalHeads) (states : Fin count → Fin totalCount) :
    HeadClause heads count → HeadClause totalHeads totalCount
  | .lower target guard => .lower (states target) (guard.map fun l => (headsMap l.1, l.2))
  | .edge source target guard => .edge (states source) (states target)
      (guard.map fun l => (paired headsMap l.1, l.2))
  | .upper source guard => .upper (states source) (guard.map fun l => (headsMap l.1, l.2))
  | .check guard => .check (guard.map fun l => (headsMap l.1, l.2))

def clause (headsMap : Fin heads → Fin totalHeads) (states : Fin count → Fin totalCount)
    (constantsMap : Fin constants → Fin totalConstants) (c : GuardedClause heads count constants) :
    GuardedClause totalHeads totalCount totalConstants where
  constants := c.constants.map fun l => (constantsMap l.1, l.2)
  head := headClause headsMap states c.head
  modes := c.modes

def clauses (headsMap : Fin heads → Fin totalHeads) (states : Fin count → Fin totalCount)
    (constantsMap : Fin constants → Fin totalConstants) (cs : List (GuardedClause heads count constants)) :
    List (GuardedClause totalHeads totalCount totalConstants) :=
  cs.map (clause headsMap states constantsMap)

/-- Head coordinates outside a group's own namespace may be identified with a
retained local head; the projection preserves positive normalized polynomials. -/
def store (headsMap : Nat → Nat) (states : Fin count → Fin totalCount)
    (full : Store totalCount) : Store count :=
  Vector.ofFn fun i => rename headsMap full[states i]

def result (headsMap : Nat → Nat) (states : Fin count → Fin totalCount)
    (constantsMap : Fin constants → Fin totalConstants)
    (full : Result totalCount totalConstants flex) : Result count constants flex where
  constants := Vector.ofFn fun i => full.constants[constantsMap i]
  types := store headsMap states full.types
  modes := full.modes

end ModalityInference.ComparisonJointReindex
