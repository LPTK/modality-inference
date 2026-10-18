import ModalityInference.ComparisonSignedWorlds
import ModalityInference.ComparisonSignedObservation

/-! Finite nominal points stand for the basis arguments of shared image calls.
Their equalities with actual route observations remain in the guarded theory;
they are not independently chosen witnesses. -/
namespace ModalityInference.ComparisonSignedPoints

open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout

def sourceAtom (v : Nat) : Nat := 2*v

def pointAtom (names : List Call) (call : Call) (i : Nat) : Nat :=
  2*Nat.pair (names.idxOf call) i+1

def pointClauses (names : List Call) (size : Nat → Nat) : CNF :=
  names.flatMap fun call => (List.range (size call.name)).flatMap fun i =>
    let point := pointAtom names call i
    let actual := sourceAtom (routeAtom call.route (basisAtom i))
    [[(point,false),(actual,true)],[(actual,false),(point,true)]]

def theory (names : List Call) (size : Nat → Nat) (original : CNF) : CNF :=
  ComparisonPropagation.rename sourceAtom original ++ pointClauses names size

def clause (original : CompiledClause) : CompiledClause :=
  ⟨original.guard.map (fun literal => (sourceAtom literal.1,literal.2)),original.literals⟩

/-- Existing scalar worlds are retained. Nominal source bits and nominal point
bits use even and odd local slots respectively. -/
def decode (original : Nat → Nat × Nat) (v : Nat) : Nat × Nat :=
  if v%2=0 then
    let atom := original (v/2)
    if atom.1=0 then (0,2*atom.2) else atom
  else (0,v)

end ModalityInference.ComparisonSignedPoints
