import ModalityInference.ComparisonRankedDecision
import ModalityInference.ComparisonSignedEndpointQueries
import ModalityInference.ComparisonLayoutWorlds
import ModalityInference.ComparisonPreparedScalar
import ModalityInference.ComparisonJointAssemblyReification

/-! One shared scalar strategy and one shared image family over a ranked basis.
The original machine theory reads only fixed mode names. Endpoint observations
also read quantified mode names, in the scalar world of the same machine state. -/
namespace ModalityInference.ComparisonRankedModes

open ComparisonObserverMachineFormula ComparisonSignedEndpoints
  ComparisonStructuralLayout ComparisonSignedObservation

def route (state : Nat) : Route := List.replicate state true

def nominal (state field index : Nat) : BoolExpr :=
  .atom (routeAtom (route state) (choiceAtom (Nat.pair field index)))

def scalarField (state : Nat) (v : ModVar) (axis : Nat) : BoolExpr :=
  .atom (routeAtom (route state) (ComparisonStructuralLayout.modeAtom (v.atomIndex axis)))

def constructorCode : Constructor → Nat
  | .prod => 0
  | .sum => 1
  | .fn => 2

def fields (types : List TypeVar) (names : List ModVar) (count : Nat)
    (i : Fin count) : Fields count where
  atoms := (List.range types.length).map (nominal i 0)
  modes := names.map fun v => (scalarField i v 0, scalarField i v 1, scalarField i v 2)
  first := nominal i 1 0
  second := nominal i 1 1
  unitValue := nominal i 2 0
  creditValue := nominal i 2 1
  left := fun k => nominal i 3 (constructorCode k)
  next := fun k j => nominal i (4 + constructorCode k) j
  range := fun b => nominal i 7 (if b then 1 else 0)

def extended (names : List ModVar) (modeIds : List Nat) : List ModVar :=
  names ++ modeIds.map ModVar.flex

def input (keys : List Nat) (basis : ComparisonControls.Basis) :
    ComparisonSignedSynthesis.Input := ⟨keys, fun _ => basis.types⟩

def aliases (types : List TypeVar) (names : List ModVar) (count : Nat)
    (basis : ComparisonControls.Basis) : BoolExpr :=
  .all ((List.finRange count).flatMap fun i =>
    basis.types.zipIdx.map fun (a, index) =>
      .equal (.atom (routeAtom (route i) (basisAtom index)))
        (value types names (fields types names count) a i))

def theory (Δ : Bounds) (types : List TypeVar) (names : List ModVar) (count : Nat)
    (basis : ComparisonControls.Basis) : BoolExpr :=
  .and (query Δ types names (fields types names count))
    (aliases types names count basis)

def clauses (keys : List Nat) (types : List TypeVar) (names : List ModVar)
    (modeIds : List Nat) (count : Nat) (endpoints : List (Ty × Ty)) :
    List ComparisonSignedEndpoints.Clause :=
  ComparisonRankedDecision.clauses keys types (extended names modeIds)
    (fields types (extended names modeIds) count) ModExpr.var endpoints

def prepare (fuel : Nat) (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty)) :
    RunResult ComparisonSignedEndpointQueries.Source := do
  let original ← CompactCNF.toCNF fuel true (theory Δ types names count basis)
  let required ← compileGuards fuel (clauses keys types names modeIds count endpoints)
  return ⟨ComparisonLayoutWorlds.decode, original, required⟩

def run (fuel : Nat) (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty))
    (scalar : List ComparisonSignedEndpointQueries.Source) :
    RunResult ComparisonSignedQuerySolver.Solution := do
  let endpoint ← prepare fuel Δ keys types names modeIds count basis endpoints
  ComparisonSignedEndpointQueries.run fuel (input keys basis)
    ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds) (endpoint :: scalar)

def assemble (names : List ModVar) (modeIds : List Nat)
    (input : ComparisonSignedSynthesis.Input)
    (sources : List ComparisonSignedEndpointQueries.Source) (selectors : Nat → Bool) :
    Option Substitution :=
  SymbolicSchemeModes.assemble
    (ComparisonJointAssemblyReification.projectElimination names
      (ComparisonSignedEndpointQueries.modes ModalSynthesis.locality
        (SchemeModeSynthesis.atoms modeIds) input sources selectors))
    (SchemeModeSynthesis.parameters modeIds)

/-- Reify the shared strategy using only fixed input mode names. Every selected
image is total; its original endpoint guards remain separate obligations. -/
def synthesize (fuel : Nat) (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty))
    (scalar : List ComparisonSignedEndpointQueries.Source) : RunResult CompareSubstitution := do
  let endpoint ← prepare fuel Δ keys types names modeIds count basis endpoints
  let result ← ComparisonSignedEndpointQueries.run fuel (input keys basis)
    ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds) (endpoint :: scalar)
  match assemble names modeIds (input keys basis) (endpoint :: scalar)
      (CNFPropagation.valuation result.selectors) with
  | none => .rejected "shared modality strategy could not be reified"
  | some assembled => .success { types := result.images, modes := assembled.modes }

end ModalityInference.ComparisonRankedModes
