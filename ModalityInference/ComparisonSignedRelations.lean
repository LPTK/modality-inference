import ModalityInference.ComparisonPropagation

/-! Symbolic composition of relations. Each tuple has an input coordinate, an
output coordinate and a retained parameter coordinate. Ordered elimination
quantifies only the intermediate tuple, preserving all shared parameters. -/
namespace ModalityInference.ComparisonSignedRelations

open ComparisonPropagation

def first (v : Nat) : Nat :=
  4*(v/3) + if v%3=0 then 0 else if v%3=1 then 1 else 3

def second (v : Nat) : Nat :=
  4*(v/3) + if v%3=0 then 1 else if v%3=1 then 2 else 3

def retained (v : Nat) : Nat :=
  3*(v/4) + if v%4=0 then 0 else if v%4=2 then 1 else 2

def intermediate (clauses : CNF) : List Nat :=
  (CNFPropagation.atoms clauses).filter fun v => v%4=1

def compose (left right : CNF) : CNF :=
  let combined := rename first left ++ rename second right
  rename retained (project (intermediate combined) combined)

def diagonal (width : Nat) : CNF :=
  (List.range width).flatMap fun i =>
    [[(3*i,false),(3*i+1,true)],[(3*i+1,false),(3*i,true)]]

def step (edges reached : CNF) : CNF := join reached (compose reached edges)

def iterate (edges : CNF) : Nat → CNF → CNF
  | 0,reached => reached
  | n+1,reached => iterate edges n (step edges reached)

def saturate (edges : CNF) : Nat → CNF → CNF
  | 0,reached => reached
  | n+1,reached =>
      let next := step edges reached
      if next=reached then reached else saturate edges n next

def closure (width : Nat) (edges : CNF) : CNF :=
  saturate edges (2^(2*width)) (diagonal width)

end ModalityInference.ComparisonSignedRelations
