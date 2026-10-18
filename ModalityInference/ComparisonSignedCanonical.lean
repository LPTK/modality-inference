import ModalityInference.ComparisonSignedRelations

/-! A symbolic canonical model for a finite signed implication graph. Tuple
coordinates are processed structurally; shared parameter coordinates are never
quantified or renamed. The model compares successor sets by their greatest
differing vertex under a fixed coordinate order. -/
namespace ModalityInference.ComparisonSignedCanonical
open ComparisonPropagation ComparisonSignedRelations

/-- Flip one tuple bit in the selected input/output lane. -/
def flipLiteral (lane sign : Nat) (literal : Literal) : Literal :=
  (literal.1,if literal.1%3=lane ∧ literal.1/3=sign then !literal.2 else literal.2)

def flip (lane sign : Nat) (clauses : CNF) : CNF :=
  clauses.map (fun clause=>clause.map (flipLiteral lane sign))

/-- Substitute one tuple, optionally complemented, for both relation endpoints. -/
def plugLiteral (sign : Nat) (left right : Bool) (literal : Literal) : Literal :=
  if literal.1%3=0 then
    (literal.1,if left && (literal.1/3==sign) then !literal.2 else literal.2)
  else if literal.1%3=1 then
    (3*(literal.1/3),if right && (literal.1/3==sign) then !literal.2 else literal.2)
  else literal

def plug (sign : Nat) (left right : Bool) (clauses : CNF) : CNF :=
  clauses.map (fun clause=>clause.map (plugLiteral sign left right))

/-- Quantify only present atoms in one tuple lane. -/
def quantify (lane : Nat) (clauses : CNF) : CNF :=
  project ((CNFPropagation.atoms clauses).filter (fun v=>v%3=lane)) clauses

/-- Strict order by the largest differing coordinate. -/
def less : Nat→CNF
  | 0 => [[]]
  | n+1 => join [[(3*n,false)],[(3*n+1,true)]]
      ([[(3*n,false),(3*n+1,true)],[(3*n+1,false),(3*n,true)]] ++ less n)

def difference (sign : Nat) (reached : CNF) : CNF :=
  reached ++ negate (flip 0 sign reached)

def bad (width sign : Nat) (reached : CNF) : CNF :=
  compose (difference sign reached) (negate (less width))

/-- The canonical successor-set choice, retaining the original input tuple. -/
def assignment (width sign : Nat) (reached : CNF) : CNF :=
  quantify 1 (flip 0 sign reached ++ negate reached ++ negate (bad width sign reached))

/-- Absence of a pair of mutually reachable complementary vertices. -/
def consistent (sign : Nat) (reached : CNF) : CNF :=
  negate (quantify 0 (plug sign false true reached ++ plug sign true false reached))

end ModalityInference.ComparisonSignedCanonical
