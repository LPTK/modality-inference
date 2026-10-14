import ModalityInference.HornPropagation

/-! Symbolic elimination of flexible coordinates in generalized Horn constraints.
Rigid expressions are constants throughout propagation. The result is a finite
vector of expressions, not a choice of concrete assignments. -/
namespace ModalityInference.SymbolicModes

def left (env : Mapping BoolExpr n) : LeftExpr BoolExpr n → BoolExpr
  | .var i => env.get i
  | .const c => c
  | .meet a b => .and (left env a) (left env b)
  | .join a b => .or (left env a) (left env b)

def right (env : Mapping BoolExpr n) : RightExpr BoolExpr n → BoolExpr
  | .var i => env.get i
  | .const c => c
  | .meet a b => .and (right env a) (right env b)
  | .imply a b => .imp (left env a) (right env b)

def update (env : Mapping BoolExpr n) (c : BoolExpr) :
    RightExpr BoolExpr n → Mapping BoolExpr n
  | .var i => Vector.ofFn fun j => if j = i then .or (env.get i) c else env.get j
  | .const _ => env
  | .meet a b =>
    let x := update env c a
    let y := update env c b
    Vector.ofFn fun i => .or (x.get i) (y.get i)
  | .imply a b => update env (.and c (left env a)) b

def iterate (r : RightExpr BoolExpr n) : Nat → Mapping BoolExpr n
  | 0 => Mapping.const BoolExpr n (.const false)
  | k + 1 => update (iterate r k) (.const true) r

/-- The generic Horn pruning theorem bounds propagation by the flexible dimension. -/
def solve (r : RightExpr BoolExpr n) : Mapping BoolExpr n := iterate r n

def residual (r : RightExpr BoolExpr n) : BoolExpr := right (solve r) r

def rigid (flex : List Nat) (e : BoolExpr) : Bool :=
  e.atoms.all fun v => !flex.contains v

/-- Rigid subexpressions can contain arbitrary lattice operations and implication. -/
def positive (flex : List Nat) (e : BoolExpr) : Option (LeftExpr BoolExpr flex.length) :=
  if rigid flex e then some (.const e) else
  match e with
  | .const b => some (.const (.const b))
  | .atom v => return .var (← ConcreteBackend.atomFin flex v)
  | .and a b => return .meet (← positive flex a) (← positive flex b)
  | .or a b => return .join (← positive flex a) (← positive flex b)
  | .imp _ _ => none

def horn (flex : List Nat) (e : BoolExpr) : Option (RightExpr BoolExpr flex.length) :=
  if rigid flex e then some (.const e) else
  match e with
  | .const b => some (.const (.const b))
  | .atom v => return .var (← ConcreteBackend.atomFin flex v)
  | .and a b => return .meet (← horn flex a) (← horn flex b)
  | .imp a b => return .imply (← positive flex a) (← horn flex b)
  | .or _ _ => none

structure Elimination (flex : List Nat) where
  values : Mapping BoolExpr flex.length
  obligation : BoolExpr

def eliminate (flex : List Nat) (e : BoolExpr) : Option (Elimination flex) := do
  let r ← horn flex e
  return ⟨solve r, residual r⟩

def Elimination.substitute {flex} (s : Elimination flex) (v : Nat) : BoolExpr :=
  ((ConcreteBackend.atomFin flex v).map s.values.get).getD (.atom v)

inductive Axis where
  | locality | affinity | uniqueness
  deriving DecidableEq, Repr

def Axis.embed : Axis → Bool → Mode
  | .locality, b => ⟨b, true, true⟩
  | .affinity, b => ⟨true, b, true⟩
  | .uniqueness, b => ⟨true, true, b⟩

def atomVariable (i : Nat) : ModVar :=
  if i / 3 % 2 = 0 then .flex (i / 6) else .rigid (i / 6)

/-- Locality has its own coordinate domain; closure connects the other two axes. -/
def reifyAtom (axis : Axis) (i : Nat) : Option ModExpr :=
  let v := ModExpr.var (atomVariable i)
  match axis, i % 3 with
  | .locality, 0 => some (.join (.future v) (.const ⟨false, true, true⟩))
  | .affinity, 1 => some (.join (.future v) (.const ⟨true, false, true⟩))
  | .affinity, 2 => some (.join (.close v) (.const ⟨true, false, true⟩))
  | .uniqueness, 1 => some (.join (.closeInv v) .epsilon)
  | .uniqueness, 2 => some (.join v .epsilon)
  | _, _ => none

/-- Each encoded expression has neutral `true` bits on the other coordinates.
The residual operations below are consequently defined for every interpretation. -/
def reify (axis : Axis) : BoolExpr → Option ModExpr
  | .const b => some (.const (axis.embed b))
  | .atom i => reifyAtom axis i
  | .and a b => return .compose (← reify axis a) (← reify axis b)
  | .or a b => do
    let x ← reify axis a
    let y ← reify axis b
    return match axis with | .uniqueness => .meet x y | _ => .join x y
  | .imp a b => do
    let x ← reify axis a
    let y ← reify axis b
    return match axis with | .uniqueness => .leftResidual y x | _ => .rightResidual x y

def Elimination.mode {flex} (s : Elimination flex) (v : ModVar) : Option ModExpr := do
  let l ← reify .locality (s.substitute (v.atomIndex 0))
  let a ← reify .affinity (s.substitute (v.atomIndex 1))
  let u ← reify .uniqueness (s.substitute (v.atomIndex 2))
  return .compose l (.compose a u)

end ModalityInference.SymbolicModes
