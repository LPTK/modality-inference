import ModalityInference.ComparisonSignedObservation
import ModalityInference.ComparisonSignedWorlds
import ModalityInference.ComparisonSignedPoints

/-! Actual structural-layout atoms are partitioned into one nominal block and
one scalar block per route. Every scalar block keeps the original modality atom
indices, so all routes can use the same modality strategy. -/
namespace ModalityInference.ComparisonLayoutWorlds
open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout

def routeCode : Route → Nat
  | [] => 0
  | false::rest => 2 * routeCode rest + 1
  | true::rest => 2 * routeCode rest + 2

def location (v : Nat) : Route × Nat :=
  if v % 3 = 0 then ([],v/3)
  else
    let tail := location (v/3)
    ((v%3==2) :: tail.1,tail.2)
termination_by v
decreasing_by omega

def decode (v : Nat) : Nat × Nat :=
  let (route,slot) := location v
  if slot%4=2 then (routeCode route+1,slot/4) else (0,v)

/-- Apply the same scalar strategy at every node while preserving nominal bits. -/
def apply (scalar : (Nat → Bool) → Nat → Bool) (world : Nat → Bool) (v : Nat) : Bool :=
  let (route,slot) := location v
  if slot%4=2 then scalar (fun i=>world (routeAtom route (modeAtom i))) (slot/4)
  else world v

/-- Point equations are inserted before world-wise clause separation. -/
def pointQuery (size : Nat → Nat) (theory : CNF) (clauses : List CompiledClause) :
    List ComparisonWorldClauses.WorldClause :=
  let names := ComparisonSignedWorlds.calls clauses
  ComparisonSignedWorlds.query (ComparisonSignedPoints.decode decode)
    (ComparisonSignedPoints.theory names size theory) (clauses.map ComparisonSignedPoints.clause)

end ModalityInference.ComparisonLayoutWorlds
