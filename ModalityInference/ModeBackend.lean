import ModalityInference.Core.Syntax
import ModalityInference.Subsumption
import Mathlib.Order.BooleanAlgebra.Basic

/-! Reduction of the concrete three-axis algebra to the existing verified solver.

Projection preserves cross-axis closure constraints. A modality variable has three
distinct Boolean atoms. Residual definedness is conjoined with every inequality.
Boolean normalization produces clauses `meet(negative atoms) ≤ join(positive atoms)`;
each clause is discharged by the original, generic `Equation.decide`.
-/

namespace ModalityInference

inductive BoolExpr where
  | const (value : Bool)
  | atom (name : Nat)
  | and (left right : BoolExpr)
  | or (left right : BoolExpr)
  | imp (left right : BoolExpr)
  deriving Repr, DecidableEq, BEq

namespace BoolExpr
def eval (σ : Nat → Bool) : BoolExpr → Bool
  | .const b => b
  | .atom n => σ n
  | .and a b => a.eval σ && b.eval σ
  | .or a b => a.eval σ || b.eval σ
  | .imp a b => !a.eval σ || b.eval σ
def atoms : BoolExpr → List Nat
  | .const _ => []
  | .atom n => [n]
  | .and a b | .or a b | .imp a b => (a.atoms ++ b.atoms).dedup
def all (xs : List BoolExpr) : BoolExpr := xs.foldr .and (.const true)
def any (xs : List BoolExpr) : BoolExpr := xs.foldr .or (.const false)
def equal (a b : BoolExpr) : BoolExpr := .and (.imp a b) (.imp b a)
end BoolExpr

structure Projection where
  locality : BoolExpr
  affinity : BoolExpr
  uniqueness : BoolExpr
  defined : BoolExpr := .const true
  deriving Repr

def ModVar.atomIndex (v : ModVar) (axis : Nat) : Nat :=
  (match v with | .flex n => 2 * n | .rigid n => 2 * n + 1) * 3 + axis

def ModExpr.project : ModExpr → Projection
  | .const m => ⟨.const m.isLocal, .const m.once, .const m.unique, .const true⟩
  | .var v => ⟨.atom (v.atomIndex 0), .atom (v.atomIndex 1), .atom (v.atomIndex 2), .const true⟩
  | .compose a b =>
    let x := a.project; let y := b.project
    ⟨.and x.locality y.locality, .and x.affinity y.affinity,
      .and x.uniqueness y.uniqueness, .and x.defined y.defined⟩
  | .meet a b =>
    let x := a.project; let y := b.project
    ⟨.and x.locality y.locality, .and x.affinity y.affinity,
      .or x.uniqueness y.uniqueness, .and x.defined y.defined⟩
  | .join a b =>
    let x := a.project; let y := b.project
    ⟨.or x.locality y.locality, .or x.affinity y.affinity,
      .and x.uniqueness y.uniqueness, .and x.defined y.defined⟩
  | .leftResidual a b =>
    let x := a.project; let y := b.project
    ⟨x.locality, x.affinity, .imp y.uniqueness x.uniqueness,
      .all [x.defined, y.defined, .imp x.locality y.locality, .imp x.affinity y.affinity]⟩
  | .rightResidual a b =>
    let x := a.project; let y := b.project
    ⟨.imp x.locality y.locality, .imp x.affinity y.affinity, y.uniqueness,
      .all [x.defined, y.defined, .imp y.uniqueness x.uniqueness]⟩
  | .close a => let x := a.project; ⟨.const false, x.uniqueness, .const true, x.defined⟩
  | .closeInv a => let x := a.project; ⟨.const false, .const false, x.affinity, x.defined⟩
  | .future a => let x := a.project; ⟨x.locality, x.affinity, .const true, x.defined⟩
  | .capture a => let x := a.project; ⟨x.locality, x.affinity, x.affinity, x.defined⟩

def modeFormula (a b : ModExpr) : BoolExpr :=
  let x := a.project; let y := b.project
  .all [x.defined, y.defined, .imp x.locality y.locality,
    .imp x.affinity y.affinity, .imp y.uniqueness x.uniqueness]

def constraintModeFormula : Constraint → BoolExpr
  | .mode a b => modeFormula a b
  | .defined m => m.project.defined
  | _ => .const true
def boundsModeFormula (cs : Bounds) : BoolExpr := .all (cs.map constraintModeFormula)

abbrev Literal := Nat × Bool
abbrev Clause := List Literal
abbrev CNF := List Clause

def clauseTautology (c : Clause) : Bool := c.any fun (v, s) => c.contains (v, !s)
def cleanCNF (cs : CNF) : CNF :=
  (cs.map List.dedup |>.filter fun c => !clauseTautology c).dedup
def cnfOr (limit : Nat) (a b : CNF) : RunResult CNF :=
  if a.length * b.length > limit then .exhausted
  else .success (cleanCNF (a.flatMap fun x => b.map (x ++ ·)))

/-- Fuel bounds normalization depth and intermediate clause products. -/
def toCNF : Nat → Bool → BoolExpr → RunResult CNF
  | 0, _, _ => .exhausted
  | fuel + 1, positive, e => match e with
    | .const b => .success (if b == positive then [] else [[]])
    | .atom n => .success [[(n, positive)]]
    | .and a b => do
      let x ← toCNF fuel positive a
      let y ← toCNF fuel positive b
      if positive then return cleanCNF (x ++ y) else cnfOr (fuel + 1) x y
    | .or a b => do
      let x ← toCNF fuel positive a
      let y ← toCNF fuel positive b
      if positive then cnfOr (fuel + 1) x y else return cleanCNF (x ++ y)
    | .imp a b => do
      let x ← toCNF fuel (!positive) a
      let y ← toCNF fuel positive b
      if positive then cnfOr (fuel + 1) x y else return cleanCNF (x ++ y)

namespace ConcreteBackend
instance mappingDecidableLE (n : Nat) : DecidableRel (fun a b : Mapping Bool n => a ≤ b) :=
  fun a b => inferInstanceAs (Decidable (∀ i : Fin n, a.get i ≤ b.get i))

def atomFin (atoms : List Nat) (v : Nat) : Option (Fin atoms.length) :=
  let i := atoms.idxOf v
  if h : i < atoms.length then some ⟨i, h⟩ else none

/-- Accumulate a clause in source order, exposing the state used by the reduction proof. -/
def equationFrom (atoms : List Nat) : Clause → RightExpr Bool atoms.length →
    LeftExpr Bool atoms.length → Option (Equation Bool atoms.length)
  | [], hypothesis, goal => some ⟨hypothesis, goal⟩
  | (v, positive) :: clause, hypothesis, goal => do
    let i ← atomFin atoms v
    if positive then equationFrom atoms clause hypothesis (.join goal (.var i))
    else equationFrom atoms clause (.meet hypothesis (.var i)) goal

def equation (atoms : List Nat) (clause : Clause) : Option (Equation Bool atoms.length) :=
  equationFrom atoms clause (.const true) (.const false)

structure Report where
  atoms : List Nat
  clauses : CNF
  valid : Bool
  deriving Repr, DecidableEq

/-- Check every clause; a false accumulator does not suppress malformed-atom diagnostics. -/
def decideClauses (atoms : List Nat) : CNF → Bool → RunResult Bool
  | [], valid => .success valid
  | c :: cs, valid =>
    match equation atoms c with
    | none => .rejected "internal error: clause atom missing from query domain"
    | some q => decideClauses atoms cs (valid && Equation.decide q)

def decideFormula (fuel : Nat) (e : BoolExpr) : RunResult Report := do
  let cs ← toCNF fuel true e
  let atoms := e.atoms.mergeSort (· ≤ ·)
  let valid ← decideClauses atoms cs true
  return ⟨atoms, cs, valid⟩

def entails (fuel : Nat) (assumptions goals : Bounds) : RunResult Report :=
  decideFormula fuel (.imp (boundsModeFormula assumptions) (boundsModeFormula goals))
end ConcreteBackend

/-- A concrete witness for satisfiable modality bounds; no witness is committed to a scheme. -/
abbrev ModeAssignment := List (ModVar × Mode)
def ModeAssignment.lookup (a : ModeAssignment) (v : ModVar) : Option Mode := List.lookup v a

def ModeAssignment.total (a : ModeAssignment) (v : ModVar) : Mode :=
  (a.lookup v).getD Mode.identity

/-- Reconstruct each occurring modality from its three Boolean coordinates. -/
def ModeAssignment.ofBooleans (cs : Bounds) (σ : Nat → Bool) : ModeAssignment :=
  cs.modeVariables.map fun v =>
    (v, ⟨σ (v.atomIndex 0), σ (v.atomIndex 1), σ (v.atomIndex 2)⟩)

def checkModeConstraint (σ : ModVar → Option Mode) : Constraint → Bool
  | .mode a b => match a.eval σ, b.eval σ with
    | some x, some y => Mode.le x y
    | _, _ => false
  | .defined a => (a.eval σ).isSome
  | _ => true

/-- Prune only fully assigned constraints; undefined residuals then mean false. -/
def partialModesConsistent (cs : Bounds) (a : ModeAssignment) : Bool := cs.all fun c =>
  if c.modeVariables.all (fun v => (a.lookup v).isSome) then checkModeConstraint a.lookup c else true

/-- A fuelled depth-first search. Its explicit frontier also bounds backtracking. -/
def searchModes : Nat → Bounds → List (List ModVar × ModeAssignment) → RunResult ModeAssignment
  | 0, _, _ => .exhausted
  | _ + 1, _, [] => .rejected "inconsistent modality bounds"
  | fuel + 1, cs, (vs, a) :: todo =>
    if !partialModesConsistent cs a then searchModes fuel cs todo
    else match vs with
    | [] => .success a
    | v :: rest => searchModes fuel cs
        (Mode.all.map (fun m => (rest, (v, m) :: a)) ++ todo)

def assignCNF (cs : CNF) (v : Nat) (b : Bool) : CNF :=
  (cs.filter fun c => !c.contains (v,b)).map (List.filter fun lit => lit != (v,!b))

/-- Deterministic DPLL with unit propagation. The frontier makes both branching
and propagation consume fuel; an unfinished search never reports inconsistency. -/
def searchCNF : Nat → List (CNF × List (Nat × Bool)) → RunResult (List (Nat × Bool))
  | 0, _ => .exhausted
  | _ + 1, [] => .rejected "inconsistent modality bounds"
  | fuel + 1, (cs,σ) :: todo =>
    if cs.any List.isEmpty then searchCNF fuel todo
    else if cs.isEmpty then .success σ
    else match cs.findSome? (fun c => match c with | [lit] => some lit | _ => none) with
      | some (v,b) => searchCNF fuel ((assignCNF cs v b, (v,b)::σ) :: todo)
      | none =>
        let atoms := cs.flatMap (List.map Prod.fst)
        let v := atoms.foldl min (atoms.headD 0)
        searchCNF fuel ((assignCNF cs v false, (v,false)::σ) ::
          (assignCNF cs v true, (v,true)::σ) :: todo)

def satisfiableModes (fuel : Nat) (cs : Bounds) : RunResult ModeAssignment := do
  let clauses ← toCNF fuel true (boundsModeFormula cs)
  let σ ← searchCNF fuel [(clauses, [])]
  return cs.modeVariables.map fun v =>
    (v, ⟨(σ.lookup (v.atomIndex 0)).getD false,
         (σ.lookup (v.atomIndex 1)).getD false,
         (σ.lookup (v.atomIndex 2)).getD false⟩)

end ModalityInference
