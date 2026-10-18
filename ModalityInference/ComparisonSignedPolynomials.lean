import ModalityInference.ComparisonSignedRelations

/-! Polynomial constraints on signed graph states. The first bit is the sign,
followed by a fixed image key and its basis coordinates. Monotonicity and the
two endpoint conditions enforce finite lattice terms without empty extrema.
Extraction specializes one image and normalizes its formula by resolution. -/
namespace ModalityInference.ComparisonSignedPolynomials
open ComparisonPropagation

def fixedPrefix (lane : Nat) (key : List Bool) (sign : Bool) : CNF :=
  (List.range (key.length+1)).map fun i => [(3*i+lane,(sign::key)[i]?.getD false)]

def endpoints (key : List Bool) (left right : Bool) : CNF :=
  fixedPrefix 0 key left ++ fixedPrefix 1 key right

def increasing (key : List Bool) (size : Nat) : CNF :=
  endpoints key true true ++ (List.range size).map fun i =>
    [(3*(key.length+1+i),false),(3*(key.length+1+i)+1,true)]

def decreasing (key : List Bool) (size : Nat) : CNF :=
  endpoints key false false ++ (List.range size).map fun i =>
    [(3*(key.length+1+i)+1,false),(3*(key.length+1+i),true)]

def boundary (key : List Bool) (size : Nat) (b : Bool) : CNF :=
  endpoints key (!b) b ++ (List.range size).flatMap fun i =>
    [[(3*(key.length+1+i),b)],[(3*(key.length+1+i)+1,b)]]

def edges (key : List Bool) (size : Nat) : CNF :=
  join (increasing key size) (join (decreasing key size)
    (join (boundary key size false) (boundary key size true)))

/-- A restricted literal is either constant or one retained basis atom. -/
def literal (subst : Nat → Sum Bool Nat) (l : Literal) : CNF :=
  match subst l.1 with
  | .inl b => if b=l.2 then [] else [[]]
  | .inr v => [[(v,l.2)]]

def specialize (subst : Nat → Sum Bool Nat) (clauses : CNF) : CNF :=
  clauses.flatMap fun c => c.foldr (fun l rest => join (literal subst l) rest) [[]]

def imageSubst (parameters : Nat → Bool) (key : List Bool) (size : Nat)
    (v : Nat) : Sum Bool Nat :=
  if v%3=0 then
    if v/3 < key.length+1 then .inl ((true::key)[v/3]?.getD false)
    else if v/3 < key.length+1+size then .inr (v/3-(key.length+1))
    else .inl false
  else if v%3=2 then .inl (parameters (v/3)) else .inl false

def polynomial (parameters : Nat → Bool) (key : List Bool) (size : Nat)
    (assignment : CNF) : CNF :=
  upward (List.range size) (specialize (imageSubst parameters key size) assignment)

def reconstruct (parameters : Nat → Bool) (key : List Bool)
    (basis : List CompareTy) (assignment : CNF) : Option CompareTy :=
  reify basis (polynomial parameters key basis.length assignment)

end ModalityInference.ComparisonSignedPolynomials
