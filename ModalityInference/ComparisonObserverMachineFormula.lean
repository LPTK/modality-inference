import ModalityInference.ComparisonObserverMachineCheck

/-! Symbolic compilation of the finite observer checker. Successor choices are
priority multiplexers over the finite state set; no observer description or
Boolean assignment is enumerated. -/
namespace ModalityInference.ComparisonObserverMachineFormula

open ComparisonControls ComparisonStructuralLayout ComparisonObserverMachine

abbrev Scalar := BoolExpr × BoolExpr × BoolExpr

structure Fields (count : Nat) where
  atoms : List BoolExpr
  modes : List Scalar
  first : BoolExpr
  second : BoolExpr
  unitValue : BoolExpr
  creditValue : BoolExpr
  left : Constructor → BoolExpr
  next : Constructor → Fin count → BoolExpr
  range : Bool → BoolExpr

def mux (p yes no : BoolExpr) : BoolExpr := .or (.and p yes) (.and (.imp p (.const false)) no)

def coordinate (first second : Bool) : Coordinate :=
  if first then (if second then .uniqueness else .affinity)
  else (if second then .locality else .unaffected)

def scalar (s : Scalar) (world : Nat → Bool) : Mode :=
  ⟨s.1.eval world, s.2.1.eval world, s.2.2.eval world⟩

def firstTrue {α} (fallback : α) (test : α → Bool) : List α → α
  | [] => fallback
  | x::xs => if test x then x else firstTrue fallback test xs

def choose {α} (fallback : BoolExpr) (test values : α → BoolExpr) : List α → BoolExpr
  | [] => fallback
  | x::xs => mux (test x) (values x) (choose fallback test values xs)

def decode {count} (data : Fin count → Fields count) (world : Nat → Bool) (i : Fin count) :
    ComparisonObserverMachineCheck.Description (Fin count) :=
  { atoms := (data i).atoms.map (BoolExpr.eval world)
    modes := (data i).modes.map (fun s => scalar s world)
    coordinate := coordinate ((data i).first.eval world) ((data i).second.eval world)
    unitValue := (data i).unitValue.eval world
    creditValue := (data i).creditValue.eval world
    branch := fun k => ⟨((data i).left k).eval world,
      firstTrue i (fun j => ((data i).next k j).eval world) (List.finRange count)⟩
    range := fun x => ((data i).range x).eval world }

def atom {count} (types : List TypeVar) (d : Fields count) (v : TypeVar) : BoolExpr :=
  if types.contains v then d.atoms[types.idxOf v]?.getD d.unitValue else d.unitValue

def mode {count} (names : List ModVar) (d : Fields count) (v : ModVar) : Scalar :=
  if names.contains v then d.modes[names.idxOf v]?.getD (.const true,.const true,.const true)
  else (.const true,.const true,.const true)

def modeAtom {count} (names : List ModVar) (d : Fields count) (i : Nat) : BoolExpr :=
  let m := mode names d (SymbolicModes.atomVariable i)
  match i % 3 with | 0 => m.1 | 1 => m.2.1 | _ => m.2.2

def modesFormula {count} (names : List ModVar) (d : Fields count) (e : BoolExpr) : BoolExpr :=
  SymbolicCNF.substitute (modeAtom names d) e

def action {count} (names : List ModVar) (d : Fields count) (m : ModExpr) (x : BoolExpr) : BoolExpr :=
  let p := m.project
  let l := modesFormula names d p.locality
  let f := modesFormula names d p.affinity
  let u := modesFormula names d p.uniqueness
  mux (modesFormula names d p.defined)
    (mux d.first (mux d.second (.or x (.imp u (.const false))) (.and x f))
      (mux d.second (.and x l) x)) x

def successor {count} (data : Fin count → Fields count) (i : Fin count) (k : Constructor)
    (values : Fin count → BoolExpr) : BoolExpr :=
  choose (values i) ((data i).next k) values (List.finRange count)

def value {count} (types : List TypeVar) (names : List ModVar) (data : Fin count → Fields count) :
    CompareTy → Fin count → BoolExpr
  | .var v, i => atom types (data i) v
  | .unit, i => (data i).unitValue
  | .credit, i => (data i).creditValue
  | .prod a b, i => mux ((data i).left .prod)
      (successor data i .prod (value types names data a))
      (successor data i .prod (value types names data b))
  | .sum a b, i => mux ((data i).left .sum)
      (successor data i .sum (value types names data a))
      (successor data i .sum (value types names data b))
  | .fn a b, i => mux ((data i).left .fn)
      (.imp (successor data i .fn (value types names data a)) (.const false))
      (successor data i .fn (value types names data b))
  | .modal a m, i => action names (data i) m (value types names data a i)
  | .join a b, i => .or (value types names data a i) (value types names data b i)
  | .meet a b, i => .and (value types names data a i) (value types names data b i)

def unaffected {count} (d : Fields count) : BoolExpr :=
  .and (.imp d.first (.const false)) (.imp d.second (.const false))

def unique {count} (d : Fields count) : BoolExpr := .and d.first d.second

def scalarOK {count} (Δ : Bounds) (names : List ModVar) (d : Fields count) : BoolExpr :=
  .or (unaffected d) (modesFormula names d (boundsModeFormula Δ))

def sameInputs {count} (names : List ModVar) (p c : Fields count) : BoolExpr :=
  mux c.first
    (.all (names.map fun v => .and (.equal (mode names p v).2.1 (mode names c v).2.1)
      (.equal (mode names p v).2.2 (mode names c v).2.2)))
    (mux c.second (.all (names.map fun v => .equal (mode names p v).1 (mode names c v).1))
      (.const true))

def pairOK {count} (names : List ModVar) (p c : Fields count) : BoolExpr :=
  .or (unaffected c) (.and (.and (.equal c.first p.first) (.equal c.second p.second))
    (sameInputs names p c))

def closedRange {count} (d : Fields count) : BoolExpr :=
  mux d.first
    (mux d.second (.imp (d.range false) (d.range true)) (.imp (d.range true) (d.range false)))
    (mux d.second (.imp (d.range true) (d.range false)) (.const true))

def signed {count} (d : Fields count) (k : Constructor) (x : Bool) : BoolExpr :=
  if k.dual then mux (d.left k) (.const (!x)) (.const x) else .const x

def rangeAt {count} (d : Fields count) (x : BoolExpr) : BoolExpr :=
  mux x (d.range true) (d.range false)

def branchRange {count} (data : Fin count → Fields count) (i : Fin count) (k : Constructor) : BoolExpr :=
  .all ([false,true].map fun x =>
    .imp (successor data i k (fun j => (data j).range x)) (rangeAt (data i) (signed (data i) k x)))

def functionRange {count} (data : Fin count → Fields count) (i : Fin count) : BoolExpr :=
  .imp (unique (data i)) (.all ([false,true].map fun x =>
    .imp (successor data i .fn (fun j => (data j).range x)) (signed (data i) .fn x)))

def declared {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (i : Fin count) : BoolExpr :=
  .all (Δ.map fun c => match c with
    | .sub a b => .imp (value types names data (.ofTy a) i) (value types names data (.ofTy b) i)
    | _ => .const true)

def checkNode {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (i : Fin count) : BoolExpr :=
  .all [scalarOK Δ names (data i), rangeAt (data i) (data i).unitValue,
    rangeAt (data i) (data i).creditValue,
    .all (types.map fun v => rangeAt (data i) (atom types (data i) v)),
    closedRange (data i), branchRange data i .prod, branchRange data i .sum, branchRange data i .fn,
    successor data i .prod (fun j => pairOK names (data i) (data j)),
    successor data i .sum (fun j => pairOK names (data i) (data j)),
    functionRange data i, declared Δ types names data i]

def query {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) : BoolExpr :=
  .all ((List.finRange count).map (checkNode Δ types names data))

end ModalityInference.ComparisonObserverMachineFormula
