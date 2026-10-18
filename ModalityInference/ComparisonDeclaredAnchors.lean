import ModalityInference.ComparisonPartialPropagation
import ModalityInference.ComparisonPreparation
import ModalityInference.SchemeInstance

/-! Source-bound interpolation followed by whole-type declared-edge propagation.
Every original comparison and definedness obligation is checked after the
simultaneous finite substitution has been constructed. -/
namespace ModalityInference.ComparisonDeclaredAnchors

open ComparisonPartialPropagation

def fixed (p : SchemePreparation.Prepared) (a : Ty) : Bool :=
  a.typeVariables.all fun v => !ComparisonShapeSolver.sourceAllowed p v

def endpoints (p : SchemePreparation.Prepared) (name : Nat) (lower : Bool) : List Ty :=
  p.sourceBounds.flatMap fun c =>
    let pair := match c with
      | .sub a b => [(a, b)]
      | .equal v a => [(.var v, a), (a, .var v)]
      | .equiv a b => [(a, b), (b, a)]
      | _ => []
    pair.filterMap fun (a, b) =>
      let (endpoint, selected) := if lower then (a, b) else (b, a)
      if selected == .var (.flex name) && fixed p endpoint then some endpoint else none

def action (p : SchemePreparation.Prepared) : CompareSubstitution :=
  { types := (List.range' p.firstType (p.nextType - p.firstType)).map fun name =>
      (name, ComparisonInterpolation.witness
        ((endpoints p name true).map CompareTy.ofTy)
        ((endpoints p name false).map CompareTy.ofTy)) }

def comparisons : CompareConstraint → List (CompareTy × CompareTy)
  | .sub a b => [(a, b)]
  | .equal v a => [(.var v, a), (a, .var v)]
  | .equiv a b => [(a, b), (b, a)]
  | .mode _ _ | .defined _ => []

def guards : CompareConstraint → Bounds
  | .sub a b | .equiv a b => a.wellFormedBounds ++ b.wellFormedBounds
  | .equal _ a => a.wellFormedBounds
  | .mode a b => [.mode a b]
  | .defined a => [.defined a]

def obligations (p : SchemePreparation.Prepared) (σ : CompareSubstitution) : CompareBounds :=
  σ.bounds p.sourceBounds ++ [.sub (σ.ty p.sourceType) (.ofTy p.targetType)]

def vertices (p : SchemePreparation.Prepared) (σ : CompareSubstitution) : List CompareTy :=
  (((obligations p σ).flatMap comparisons).flatMap
    (fun (a, b) => expose a .epsilon ++ expose b .epsilon) ++
    (anchors p).flatMap (fun t => expose (.ofTy t) .epsilon)).dedup

def shapeCheck : ComparisonShapeSolver.Result → CompareTy → Bool
  | .infeasibleAssumptions, _ => true
  | .solved shapes, a => wellShaped shapes.fixedShapes a

def checkPair (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Result) (edges : List (ModExpr × ModExpr))
    (graph : Graph) (pair : CompareTy × CompareTy) : RunResult Bool := do
  let mode := fun a b => edges.contains (a, b)
  let some c ← saturate mode pair.1 pair.2 fuel graph | return false
  return c.left == pair.1 && c.right == pair.2 &&
    c.check (shapeCheck shapes) mode p.assumptions

def checkPairs (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Result) (edges : List (ModExpr × ModExpr))
    (graph : Graph) : List (CompareTy × CompareTy) → RunResult Bool
  | [] => .success true
  | pair :: rest => do
      if !(← checkPair fuel p shapes edges graph pair) then return false
      checkPairs fuel p shapes edges graph rest

structure Result where
  shapes : ComparisonShapeSolver.Result
  action : CompareSubstitution
  scalarEdges : List (ModExpr × ModExpr)
  backend : ConcreteBackend.Report
  deriving Repr

/-- No declared structural inequality is inverted. The candidate is the join
of every fixed lower endpoint, or the meet of all fixed upper endpoints when
there is no lower endpoint. Source bounds and the whole body certify it. -/
def attempt (fuel : Nat) (p : SchemePreparation.Prepared) : RunResult (Option Result) := do
  if p.firstMode != p.nextMode then return none
  let shapes ← ComparisonShapeSolver.prepare fuel p
  let σ := action p
  if !σ.types.all (fun entry => shapeCheck shapes entry.2) then return none
  let nodes := vertices p σ
  let edges ← modeEdges fuel p.assumptions (modeLabels nodes)
  let goals := obligations p σ
  let report ← ConcreteBackend.entails fuel p.assumptions
    (edges.map (fun (a, b) => Constraint.mode a b) ++ goals.flatMap guards)
  if !report.valid then return none
  if !(← checkPairs fuel p shapes edges (initialGraph p.assumptions nodes)
      (goals.flatMap comparisons)) then return none
  return some ⟨shapes, σ, edges, report⟩

def run (fuel : Nat) (source target : Scheme) : RunResult CompareSubstitution := do
  let p := SchemePreparation.prepare [] source.requireDefinedInstances target
  let some result ← attempt fuel p | return ← .rejected "no certified declared-anchor instance"
  return ComparisonPreparation.reconstruct p result.action

end ModalityInference.ComparisonDeclaredAnchors
