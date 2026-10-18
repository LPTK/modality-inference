import ModalityInference.ComparisonObserverMachine

/-! Finite certificates for recursive observer machines. Every node stores a
finite scalar world, a coordinate, finite atom values and constructor edges.
The check evaluates original declared edges without decomposing them. -/
namespace ModalityInference.ComparisonObserverMachineCheck

open ComparisonControls ComparisonStructuralLayout ComparisonObserverMachine

structure Description (State : Type) where
  atoms : List Bool
  modes : List Mode
  coordinate : Coordinate
  unitValue : Bool
  creditValue : Bool
  branch : Constructor → Branch State
  range : Bool → Bool

def atomValue {State} (types : List TypeVar) (d : Description State) (v : TypeVar) : Bool :=
  if types.contains v then d.atoms[types.idxOf v]?.getD d.unitValue else d.unitValue

def modeValue {State} (modes : List ModVar) (d : Description State) (v : ModVar) : Mode :=
  if modes.contains v then d.modes[modes.idxOf v]?.getD Mode.identity else Mode.identity

def bits (η : ModVar → Mode) (i : Nat) : Bool :=
  let m := η (SymbolicModes.atomVariable i)
  match i % 3 with
  | 0 => m.isLocal
  | 1 => m.once
  | _ => m.unique

def act (c : Coordinate) (m : Mode) (x : Bool) : Bool :=
  match c with
  | .unaffected => x
  | .locality => x && m.isLocal
  | .affinity => x && m.once
  | .uniqueness => x || !m.unique

def action {State} (modes : List ModVar) (d : Description State) (m : ModExpr) (x : Bool) : Bool :=
  act d.coordinate ((m.eval (some ∘ modeValue modes d)).getD Mode.identity) x

def nodes {State} (types : List TypeVar) (modes : List ModVar)
    (data : State → Description State) (i : State) : Node State :=
  { atom := atomValue types (data i), unitValue := (data i).unitValue,
    creditValue := (data i).creditValue, action := action modes (data i),
    branch := (data i).branch, range := (data i).range }

def scalarOK {State} (Δ : Bounds) (modes : List ModVar) (d : Description State) : Bool :=
  decide (d.coordinate = .unaffected) ||
    (boundsModeFormula Δ).eval (bits (modeValue modes d))

def sameInputs {State} (modes : List ModVar) (p c : Description State) : Bool :=
  match c.coordinate with
  | .unaffected => true
  | .locality => modes.all fun v => (modeValue modes p v).isLocal == (modeValue modes c v).isLocal
  | .affinity | .uniqueness => modes.all fun v =>
      ((modeValue modes p v).once == (modeValue modes c v).once) &&
      ((modeValue modes p v).unique == (modeValue modes c v).unique)

def pairOK {State} (modes : List ModVar) (p c : Description State) : Bool :=
  decide (c.coordinate = .unaffected) ||
    (decide (c.coordinate = p.coordinate) && sameInputs modes p c)

def closedRange {State} (d : Description State) : Bool :=
  match d.coordinate with
  | .unaffected => true
  | .locality | .affinity => !d.range true || d.range false
  | .uniqueness => !d.range false || d.range true

def branchRange {State} (data : State → Description State) (i : State) (k : Constructor) : Bool :=
  [false,true].all fun x =>
    !(data ((data i).branch k).next).range x ||
      (data i).range (sign k ((data i).branch k).left x)

def functionRange {State} (data : State → Description State) (i : State) : Bool :=
  !decide ((data i).coordinate = .uniqueness) ||
    [false,true].all (fun x => !(data ((data i).branch .fn).next).range x ||
      sign .fn ((data i).branch .fn).left x)

def declared {State} (Δ : Bounds) (types : List TypeVar) (modes : List ModVar)
    (data : State → Description State) (i : State) : Bool :=
  Δ.all fun c => match c with
    | .sub a b => !(value (nodes types modes data) (.ofTy a) i) ||
        value (nodes types modes data) (.ofTy b) i
    | _ => true

def checkNode {State} (Δ : Bounds) (types : List TypeVar) (modes : List ModVar)
    (data : State → Description State) (i : State) : Bool :=
  [scalarOK Δ modes (data i),
   (data i).range (data i).unitValue,
   (data i).range (data i).creditValue,
   types.all (fun v => (data i).range (atomValue types (data i) v)),
   closedRange (data i),
   branchRange data i .prod, branchRange data i .sum, branchRange data i .fn,
   pairOK modes (data i) (data ((data i).branch .prod).next),
   pairOK modes (data i) (data ((data i).branch .sum).next),
   functionRange data i, declared Δ types modes data i].all id

def check {count : Nat} (Δ : Bounds) (types : List TypeVar) (modes : List ModVar)
    (data : Fin count → Description (Fin count)) : Bool :=
  (List.finRange count).all (checkNode Δ types modes data)

end ModalityInference.ComparisonObserverMachineCheck
