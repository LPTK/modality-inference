import ModalityInference.ComparisonElimination
import ModalityInference.ComparisonJointEncoding

/-! Four coordinated observations of the actual opaque comparison groups.
Flexible state atoms occupy a finite prefix, followed by fixed head atoms and
shared modality coordinates. All scalar guards remain explicit. -/
namespace ModalityInference.ComparisonJointGroup

open ComparisonPropagation ComparisonControls

def coordinateNumber : Coordinate → Nat
  | .unaffected => 0
  | .locality => 1
  | .affinity => 2
  | .uniqueness => 3

def state (coordinate : Coordinate) (i : Fin count) : Fin (4 * count) :=
  ⟨coordinateNumber coordinate * count + i.val, by cases coordinate <;>
    simp only [coordinateNumber] <;> omega⟩

def modeFormula (heads : Nat) (e : BoolExpr) : BoolExpr :=
  SymbolicCNF.substitute (fun i => .atom (heads + i)) e

def lowerFormula (coordinate : Coordinate) (m : ModExpr) : BoolExpr :=
  match coordinate with
  | .uniqueness => .imp m.project.uniqueness (.const false)
  | _ => .const false

def upperFormula (coordinate : Coordinate) (m : ModExpr) : BoolExpr :=
  match coordinate with
  | .locality => m.project.locality
  | .affinity => m.project.affinity
  | _ => .const true

def action (fuel heads : Nat) (coordinate : Coordinate) (m : ModExpr) : RunResult Action := do
  let lower ← CompactCNF.toCNF fuel true (modeFormula heads (lowerFormula coordinate m))
  let upper ← CompactCNF.toCNF fuel true (modeFormula heads (upperFormula coordinate m))
  return ⟨lower, upper⟩

def index [BEq α] (values : List α) (value : α) : Option (Fin values.length) :=
  let i := values.idxOf value
  if h : i < values.length then some ⟨i, h⟩ else none

def fixed (heads : List TypeVar) (coordinate : Coordinate) (a : ComparisonGroups.Atom) :
    RunResult BoolExpr :=
  match index heads a.head with
  | none => .rejected "declared comparison head missing from its shape class"
  | some i => .success (coordinate.modalWith (heads.length + ·) (.atom i.val) a.mode)

def fixedBound (heads : List TypeVar) (coordinate : Coordinate)
    (pair : ComparisonGroups.Inequality) : RunResult BoolExpr := do
  return .imp (← fixed heads coordinate pair.1) (← fixed heads coordinate pair.2)

def leaf (heads : List TypeVar) (names : List Nat) (coordinate : Coordinate)
    (v : TypeVar) : RunResult (Leaf (4 * names.length)) :=
  let fixed := match index heads v with
    | none => .rejected "comparison head missing from its shape class"
    | some i => .success (.fixed [[(i.val, true)]])
  match v with
  | .flex n => match index names n with
      | none => fixed
      | some i => .success (.flex (state coordinate i))
  | .rigid _ => fixed

/-- Explicit left and right actions avoid identifying two separately guarded labels. -/
def compileActions (left right : Action) (theory : CNF) (a b : Leaf count) : List (Obligation count) :=
  let base := meet left.lower left.upper
  match a, b with
  | .fixed x, .fixed y => [.check (implies theory (implies (left.apply x) (right.apply y)))]
  | .fixed x, .flex y =>
      [.lower y (meet theory (meet (left.apply x) (negate right.lower))),
       .check (implies theory (implies (left.apply x) right.upper))]
  | .flex x, .fixed y =>
      [.upper x (implies (meet theory left.upper) (right.apply y)),
       .check (implies theory (implies base (right.apply y)))]
  | .flex x, .flex y =>
      [.lower y (meet theory (meet base (negate right.lower))),
       .edge x y (meet theory (meet left.upper (negate right.lower))),
       .upper x (implies (meet theory left.upper) right.upper),
       .check (implies theory (implies base right.upper))]

def bound (fuel : Nat) (heads : List TypeVar) (names : List Nat) (coordinate : Coordinate)
    (theory : CNF) (pair : ComparisonGroups.Inequality) : RunResult (List (Obligation (4 * names.length))) := do
  let a ← leaf heads names coordinate pair.1.head
  let b ← leaf heads names coordinate pair.2.head
  let left ← action fuel heads.length coordinate pair.1.mode
  let right ← action fuel heads.length coordinate pair.2.mode
  return compileActions left right theory a b

def guards (assumptions required : Bounds) : BoolExpr :=
  .and (boundsModeFormula assumptions) (boundsModeFormula required)

def theory (coordinate : Coordinate) (heads : Nat) (assumptions required : Bounds)
    (declared : List BoolExpr) : BoolExpr :=
  .and (.all declared) (if coordinate == .unaffected then .const true
    else modeFormula heads (guards assumptions required))

def coordinate (fuel : Nat) (assumptions required : Bounds) (g : ComparisonGroups.Group)
    (c : Coordinate) : RunResult CNF := do
  let declared ← g.assumptions.mapM (fixedBound g.heads c)
  let clauses ← CompactCNF.toCNF fuel true (theory c g.heads.length assumptions required declared)
  let goals ← g.goals.mapM (bound fuel g.heads g.leaves c clauses)
  return ComparisonJointEncoding.encodeAll goals.flatten

def sandwich (left right : Coordinate) (count : Nat) : CNF :=
  (List.finRange count).map fun i => [(state left i |>.val, false), (state right i |>.val, true)]

structure Input where
  nominal : CNF
  locality : CNF
  other : CNF
  scalar : CNF

/-- Locality and the other two affected observations retain one shared nominal
state per flexible leaf. Every mode guard also remains in the scalar problem. -/
def prepare (fuel : Nat) (assumptions required : Bounds) (g : ComparisonGroups.Group) : RunResult Input := do
  let nominal ← coordinate fuel assumptions required g .unaffected
  let locality ← coordinate fuel assumptions required g .locality
  let affinity ← coordinate fuel assumptions required g .affinity
  let uniqueness ← coordinate fuel assumptions required g .uniqueness
  let scalar ← CompactCNF.toCNF fuel true
    (.imp (boundsModeFormula assumptions) (boundsModeFormula required))
  return ⟨nominal, locality ++ sandwich .locality .unaffected g.leaves.length,
    affinity ++ uniqueness ++ sandwich .affinity .unaffected g.leaves.length ++
      sandwich .unaffected .uniqueness g.leaves.length, scalar⟩

end ModalityInference.ComparisonJointGroup
