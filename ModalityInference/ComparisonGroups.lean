import ModalityInference.ComparisonReduction

/-! Partition opaque comparison leaves by their declared shape class. Fixed
heads remain named generators; class membership never identifies their types. -/
namespace ModalityInference.ComparisonGroups

structure Atom where
  head : TypeVar
  mode : ModExpr
  deriving Repr, DecidableEq

abbrev Inequality := Atom × Atom

def atom (a : Ty) : Option Atom :=
  match a.outer with
  | (.var v, m) => some ⟨v, m⟩
  | _ => none

def inequality (a b : Ty) : Option Inequality := do
  return (← atom a, ← atom b)

def shapeClass (shapes : ComparisonShapeSolver.Solved)
    (templates : ComparisonSkeleton.Templates) (v : TypeVar) : Option TypeVar :=
  match v with
  | .flex n => match templates.leaves.find? (fun leaf => leaf.name == n) with
      | some leaf => some leaf.shapeClass
      | none => match shapes.fixedShapes v with | .var c => some c | _ => none
  | .rigid _ => match shapes.fixedShapes v with | .var c => some c | _ => none

structure Group where
  shapeClass : TypeVar
  heads : List TypeVar
  leaves : List Nat
  assumptions : List Inequality
  goals : List Inequality
  deriving Repr

def collect (p : SchemePreparation.Prepared) (shapes : ComparisonShapeSolver.Solved)
    (templates : ComparisonSkeleton.Templates) (reduced : ComparisonReduction.State) :
    RunResult (List Group) := do
  let goals ← reduced.inequalities.mapM fun (a, b) =>
    match inequality a b with
    | none => .rejected "non-opaque comparison leaf"
    | some pair => .success pair
  let assumptions := p.assumptions.filterMap fun c => match c with
    | .sub a b => inequality a b
    | _ => none
  let fixed := (p.assumptions.typeVariables ++ p.targetType.typeVariables ++
    p.sourceType.typeVariables ++ p.sourceBounds.typeVariables).dedup.filter
      (fun v => !ComparisonShapeSolver.sourceAllowed p v)
  let classes := (templates.leaves.map (·.shapeClass) ++
    fixed.filterMap (shapeClass shapes templates)).dedup
  for (a, b) in goals do
    match shapeClass shapes templates a.head, shapeClass shapes templates b.head with
    | some x, some y => if x != y then
        return ← .rejected "opaque endpoints have distinct fixed shapes"
    | _, _ => return ← .rejected "opaque endpoint has a structural fixed shape"
  return classes.map fun c =>
    { shapeClass := c
      heads := fixed.filter fun v => shapeClass shapes templates v == some c
      leaves := templates.leaves.filterMap fun leaf =>
        if leaf.shapeClass == c then some leaf.name else none
      assumptions := assumptions.filter fun pair =>
        shapeClass shapes templates pair.1.head == some c
      goals := goals.filter fun pair => shapeClass shapes templates pair.1.head == some c }

end ModalityInference.ComparisonGroups
