import ModalityInference.ComparisonDeclaredAnchors

/-! Structural propagation of fixed declared endpoints into source parameters.
The extracted demands are sufficient candidate constraints. Every original
obligation is subsequently certified under the unchanged declared bounds. -/
namespace ModalityInference.ComparisonNestedAnchors

open ComparisonPartialPropagation
open ComparisonDeclaredAnchors (fixed comparisons guards obligations vertices shapeCheck
  checkPairs)

abbrev Result := ComparisonDeclaredAnchors.Result

structure Demand where
  name : Nat
  lower : Bool
  endpoint : Ty
  deriving BEq, Repr

def variableDemand (p : SchemePreparation.Prepared) (lower : Bool) (selected endpoint : Ty) :
    List Demand :=
  match selected with
  | .var (.flex n) =>
      if ComparisonShapeSolver.sourceAllowed p (.flex n) && fixed p endpoint then
        [⟨n, lower, endpoint⟩]
      else []
  | _ => []

/-- Matching uses variance, rather than projecting an arbitrary declared edge.
An identical modal context is retained by the final whole-obligation check. -/
def matchTypes (p : SchemePreparation.Prepared) : Ty → Ty → List Demand
  | .prod a b, .prod c d | .sum a b, .sum c d =>
      matchTypes p a c ++ matchTypes p b d
  | .fn a b, .fn c d => matchTypes p c a ++ matchTypes p b d
  | .modal a m, .modal b n => if m == n then matchTypes p a b else []
  | a, b => variableDemand p false a b ++ variableDemand p true b a
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

def pairs : Constraint → List (Ty × Ty)
  | .sub a b => [(a,b)]
  | .equal v a => [(.var v,a),(a,.var v)]
  | .equiv a b => [(a,b),(b,a)]
  | .mode _ _ | .defined _ => []

/-- Each additional match follows a whole declared edge at a fixed endpoint.
All matching edges contribute demands; none is chosen as a representative. -/
def demandsFor (p : SchemePreparation.Prepared) (a b : Ty) : List Demand :=
  matchTypes p a b ++ (p.assumptions.flatMap pairs).flatMap fun (left,right) =>
    (if a == left && fixed p a then matchTypes p right b else []) ++
    (if b == right && fixed p b then matchTypes p a left else [])

def demands (p : SchemePreparation.Prepared) : List Demand :=
  ((p.sourceBounds.flatMap pairs) ++ [(p.sourceType,p.targetType)]).flatMap
    fun (a,b) => demandsFor p a b

def endpoints (p : SchemePreparation.Prepared) (name : Nat) (lower : Bool) : List Ty :=
  ((demands p).filterMap fun d =>
    if d.name == name && d.lower == lower then some d.endpoint else none).dedup

def action (p : SchemePreparation.Prepared) : CompareSubstitution :=
  { types := (List.range' p.firstType (p.nextType-p.firstType)).map fun name =>
      (name, ComparisonInterpolation.witness
        ((endpoints p name true).map CompareTy.ofTy)
        ((endpoints p name false).map CompareTy.ofTy)) }

def attempt (fuel : Nat) (p : SchemePreparation.Prepared) : RunResult (Option Result) := do
  if p.firstMode != p.nextMode then return none
  let shapes ← ComparisonShapeSolver.prepare fuel p
  let σ := action p
  if !σ.types.all (fun entry => shapeCheck shapes entry.2) then return none
  let nodes := vertices p σ
  let edges ← modeEdges fuel p.assumptions (modeLabels nodes)
  let goals := obligations p σ
  let report ← ConcreteBackend.entails fuel p.assumptions
    (edges.map (fun (a,b) => Constraint.mode a b) ++ goals.flatMap guards)
  if !report.valid then return none
  if !(← checkPairs fuel p shapes edges (initialGraph p.assumptions nodes)
      (goals.flatMap comparisons)) then return none
  return some ⟨shapes, σ, edges, report⟩

def run (fuel : Nat) (source target : Scheme) : RunResult CompareSubstitution := do
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let some result ← attempt fuel p | return ← .rejected "no certified nested-anchor instance"
  return ComparisonPreparation.reconstruct p result.action

end ModalityInference.ComparisonNestedAnchors
