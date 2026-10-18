import ModalityInference.ComparisonSignedCanonical
import ModalityInference.ComparisonSignedObservation

/-! Guarded endpoint clauses become one signed relation on image keys and basis
points. Observer inputs are existentially projected; explicitly retained shared
parameters remain unchanged. The endpoint formulas receive one common modality
substitution before this projection. -/
namespace ModalityInference.ComparisonSignedEdges
open ComparisonPropagation ComparisonSignedRelations ComparisonSignedEndpoints
open ComparisonSignedObservation ComparisonStructuralLayout

/-- Retained parameters and genuine observer inputs occupy disjoint lanes. -/
def worldAtom (decode : Nat → Sum Nat Nat) (v : Nat) : Nat :=
  match decode v with
  | .inl p => 4*p+2
  | .inr w => 4*w+3

def tupleAtom (v : Nat) : Nat := 4*(v/3)+v%3

def retained (v : Nat) : Nat := 3*(v/4)+v%4

def observerAtoms (cs : CNF) : List Nat :=
  (CNFPropagation.atoms cs).filter (fun v=>v%4=3)

def projectObservers (cs : CNF) : CNF :=
  rename retained (project (observerAtoms cs) cs)

/-- Sign, image key, then the supplied coordinates in that image's common basis. -/
def patternWith (payload : Call → Nat → Nat) (key : Nat → List Bool) (size : Nat → Nat) (call : Call) (sign : Bool) :
    List (Sum Bool Nat) :=
  (sign::key call.name).map Sum.inl ++
    (List.range (size call.name)).map (fun i=>.inr (payload call i))

def matchCoordinate (decode : Nat → Sum Nat Nat) (v : Nat) : Sum Bool Nat → CNF
  | .inl b => [[(v,b)]]
  | .inr w => [[(v,false),(worldAtom decode w,true)],[(worldAtom decode w,false),(v,true)]]

/-- Unused tuple coordinates have the fixed value false. -/
def matchPattern (width lane : Nat) (decode : Nat → Sum Nat Nat)
    (values : List (Sum Bool Nat)) : CNF :=
  (List.range width).flatMap fun i =>
    matchCoordinate decode (4*i+lane) (values[i]?.getD (.inl false))

def directed (width : Nat) (decode : Nat → Sum Nat Nat)
    (left right : List (Sum Bool Nat)) : CNF :=
  matchPattern width 0 decode left ++ matchPattern width 1 decode right

def guarded (decode : Nat → Sum Nat Nat) (theory : CNF) (guard : ModalityInference.Clause)
    (body : CNF) : CNF :=
  projectObservers (rename (worldAtom decode) (theory ++ negateClause guard) ++ body)

def clauseWith (payload : Call → Nat → Nat) (width : Nat) (key : Nat → List Bool) (size : Nat → Nat)
    (decode : Nat → Sum Nat Nat) (theory : CNF) (c : CompiledClause) : Option CNF :=
  match c.literals with
  | [] => some (guarded decode theory c.guard
      (rename tupleAtom (ComparisonSignedCanonical.flip 0 0 (diagonal width))))
  | [(a,p)] => some (guarded decode theory c.guard
      (directed width decode (patternWith payload key size a (!p)) (patternWith payload key size a p)))
  | [(a,p),(b,q)] => some (join
      (guarded decode theory c.guard
        (directed width decode (patternWith payload key size a (!p)) (patternWith payload key size b q)))
      (guarded decode theory c.guard
        (directed width decode (patternWith payload key size b (!q)) (patternWith payload key size a p))))
  | _ => none

def compileWith (payload : Call → Nat → Nat) (width : Nat) (key : Nat → List Bool) (size : Nat → Nat)
    (decode : Nat → Sum Nat Nat) (theory : CNF) : List CompiledClause → Option CNF
  | [] => some [[]]
  | c::cs => do
      let head ← clauseWith payload width key size decode theory c
      let tail ← compileWith payload width key size decode theory cs
      return join head tail

def prepareWith (payload : Call → Nat → Nat) (fuel width : Nat) (key : Nat → List Bool) (size : Nat → Nat)
    (decode : Nat → Sum Nat Nat) (theory : CNF) (keys : List Nat)
    (layout : Layout) (modes : ModVar → ModExpr) (left right : Ty) : RunResult CNF := do
  let clauses ← compileGuards fuel (ComparisonSignedEndpoints.compile keys
    (context layout modes) left right)
  match compileWith payload width key size decode theory clauses with
  | some result => return result
  | none => .rejected "nonbinary signed endpoint clause"

def routePayload (call : Call) (i : Nat) : Nat := routeAtom call.route (basisAtom i)

abbrev pattern := patternWith routePayload
abbrev clause := clauseWith routePayload
abbrev compile := compileWith routePayload
abbrev prepare := prepareWith routePayload

end ModalityInference.ComparisonSignedEdges
