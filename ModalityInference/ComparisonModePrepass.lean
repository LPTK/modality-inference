import ModalityInference.ComparisonElimination
import ModalityInference.ComparisonContext
import ModalityInference.ComparisonGuardedTotal
import ModalityInference.SchemeModeSynthesis

/-! A symbolic scalar feasibility query for opaque type intervals. Flexible type
coordinates are projected before the fixed type coordinates, so source modality
choices remain coupled to their original type obligations. The returned mode
specialization is checked again by ordinary comparison. -/
namespace ModalityInference.ComparisonModePrepass

open ComparisonPropagation ComparisonElimination

/-- Reserve the first `count` atoms for the unknown leaf coordinates. -/
def leafFormula (leaf : Leaf count) : CNF :=
  match leaf with
  | .fixed cs => rename (count + ·) cs
  | .flex i => [[(i.val, true)]]

def endpointFormula (action : ModExpr → Action) (endpoint : Endpoint count) : CNF :=
  let a := action endpoint.mode
  (Action.mk (rename (count + ·) a.lower) (rename (count + ·) a.upper)).apply
    (leafFormula endpoint.leaf)

def inequalities (action : ModExpr → Action) (theory : CNF)
    (bounds : List (Bound count)) : CNF :=
  bounds.foldr (fun b rest => meet (implies (rename (count + ·) theory)
    (implies (endpointFormula action b.left) (endpointFormula action b.right))) rest) []

/-- Existentially remove leaf coordinates, then universally remove every fixed
type and coordinate-selector atom. Only scalar atoms remain. -/
def projectQuery (leafCount basisSize : Nat) (cs : CNF) : BoolExpr :=
  let firstMode := leafCount + basisSize + 2
  let projected := project (List.range leafCount) cs
  formula (rename (· - firstMode)
    (SymbolicCNF.abstract (fun i => firstMode ≤ i) projected))

def group (fuel : Nat) (assumptions required : Bounds) (g : ComparisonGroups.Group) :
    RunResult BoolExpr := do
  let first :: rest := g.heads | .rejected "comparison class has no fixed generator"
  let labels := ((g.assumptions ++ g.goals).flatMap fun (a, b) => [a.mode, b.mode]).dedup
  let names := (labels.flatMap ModExpr.freeVariables ++ assumptions.modeVariables ++
    required.modeVariables).dedup
  let basis : ComparisonControls.Basis := ⟨.var first, rest.map CompareTy.var, names⟩
  let mut actions : List (ModExpr × Action) := []
  for label in labels do
    let lower ← ComparisonControls.low fuel basis label
    let upper ← ComparisonControls.high fuel basis label
    actions := (label, ⟨lower, upper⟩) :: actions
  let action := fun label => (actions.lookup label).getD ⟨[[]], []⟩
  let count := basis.types.length
  let mut theory ← controlsTheory fuel basis
  let unaffected := BoolExpr.and (.imp (.atom count) (.const false))
    (.imp (.atom (count + 1)) (.const false))
  let guards ← CompactCNF.toCNF fuel true
    (.or unaffected (SymbolicCNF.substitute (fun i => .atom (count + 2 + i))
      (.and (boundsModeFormula assumptions) (boundsModeFormula required))))
  theory := meet theory guards
  for pair in g.assumptions do
    let a ← endpoint basis [] pair.1
    let b ← endpoint basis [] pair.2
    match a.leaf, b.leaf with
    | .fixed x, .fixed y =>
        theory := meet theory (implies ((action a.mode).apply x) ((action b.mode).apply y))
    | .flex i, _ => nomatch i
    | _, .flex i => nomatch i
  let bounds ← g.goals.mapM (bound basis g.leaves)
  return projectQuery g.leaves.length count (inequalities action theory bounds)

def query (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (templates : ComparisonSkeleton.Templates)
    (reduced : ComparisonReduction.State) : RunResult BoolExpr := do
  let groups ← ComparisonGroups.collect p shapes templates reduced
  let queries ← groups.mapM (group fuel p.assumptions reduced.modes)
  return .all (.imp (boundsModeFormula p.assumptions) (boundsModeFormula reduced.modes) :: queries)

/-- The retry only exposes source keys and original retained names. Fresh
coordinate mode images are used by the feasibility query, then discarded. -/
def selection (p : SchemePreparation.Prepared) (modes : Substitution) : Substitution :=
  { modes := modes.modes.filter fun entry => ComparisonInstance.modeAllowed p (.flex entry.1) }

def selectionCheck (p : SchemePreparation.Prepared) (action : Substitution) : Bool :=
  ComparisonContext.scopeCheck p action &&
    action.modes.all fun entry => entry.2.freeVariables.all fun v => v.index < p.nextMode

def attempt (fuel : Nat) (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) : RunResult Substitution := do
  if p.firstMode == p.nextMode then return ← .rejected "no source modality to specialize"
  let templates := ComparisonSkeleton.prepare p shapes
  let reduced ← ComparisonReduction.prepare fuel p templates
  let required := { reduced with modes :=
    ComparisonGuardedTotal.scalarBounds p.sourceBounds ++ reduced.modes }
  let formula ← query fuel p shapes templates required
  let modes ← SchemeModeSynthesis.run fuel
    (List.range' p.firstMode (templates.nextMode - p.firstMode)) formula
  let action := selection p modes.substitution
  if selectionCheck p action then return action
  else .rejected "scalar specialization exceeds the prepared source scope"

end ModalityInference.ComparisonModePrepass
