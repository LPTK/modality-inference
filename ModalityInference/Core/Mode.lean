import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Basic

/-! # Modes and modality syntax

The Boolean coordinates are ordered `global < local`, `many < once`, and
`aliased < unique`. Only the last coordinate is reversed in **modality** order.
Concrete operations, source expressions, and polarized expressions are distinct.
Residuals are partial: their side conditions are never silently discarded.
-/

namespace ModalityInference

inductive RunResult (α : Type) where
  | success (value : α)
  | rejected (message : String)
  | exhausted
  deriving Repr, DecidableEq

namespace RunResult
def bind (r : RunResult α) (f : α → RunResult β) : RunResult β :=
  match r with
  | .success a => f a
  | .rejected e => .rejected e
  | .exhausted => .exhausted
instance : Monad RunResult where
  pure := .success
  bind := bind
def isSuccess : RunResult α → Bool
  | .success _ => true
  | _ => false
end RunResult

structure Mode where
  isLocal : Bool
  once : Bool
  unique : Bool
  deriving Repr, DecidableEq, BEq, Inhabited

namespace Mode
def le (a b : Mode) : Bool :=
  (!a.isLocal || b.isLocal) && (!a.once || b.once) && (!b.unique || a.unique)
def identity : Mode := ⟨true, true, true⟩
def bottom : Mode := ⟨false, false, true⟩
def top : Mode := ⟨true, true, false⟩
def global : Mode := ⟨false, true, true⟩
def many : Mode := ⟨true, false, true⟩
def aliased : Mode := ⟨true, true, false⟩
def uniqueOnly : Mode := ⟨true, true, true⟩
def localLower : Mode := ⟨true, false, true⟩
def onceLower : Mode := ⟨false, true, true⟩
/-- Absorbing for composition; useful as a witness for unconstrained type bounds. -/
def absorbing : Mode := ⟨false, false, false⟩
def compose (a b : Mode) : Mode :=
  ⟨a.isLocal && b.isLocal, a.once && b.once, a.unique && b.unique⟩
def meet (a b : Mode) : Mode :=
  ⟨a.isLocal && b.isLocal, a.once && b.once, a.unique || b.unique⟩
def join (a b : Mode) : Mode :=
  ⟨a.isLocal || b.isLocal, a.once || b.once, a.unique && b.unique⟩
/-- `a / b`, defined only when the future of `a` is below that of `b`. -/
def leftResidual (a b : Mode) : Option Mode :=
  if (!a.isLocal || b.isLocal) && (!a.once || b.once) then
    some ⟨a.isLocal, a.once, !b.unique || a.unique⟩
  else none
/-- `a \ b`, defined only when the past of `b` is below that of `a`. -/
def rightResidual (a b : Mode) : Option Mode :=
  if !b.unique || a.unique then
    some ⟨!a.isLocal || b.isLocal, !a.once || b.once, b.unique⟩
  else none
/-- The antitone closure adjoints satisfy `close a ≤ b ↔ closeInv b ≤ a`. -/
def close (a : Mode) : Mode := ⟨false, a.unique, true⟩
def closeInv (a : Mode) : Mode := ⟨false, false, a.once⟩
/-- A lock depends only on a closure's future, never on its past component. -/
def future (a : Mode) : Mode := ⟨a.isLocal, a.once, true⟩
def capture (a : Mode) : Mode := ⟨a.isLocal, a.once, a.once⟩
def all : List Mode :=
  [false, true].flatMap fun l => [false, true].flatMap fun o =>
    [false, true].map fun u => ⟨l, o, u⟩
end Mode

inductive TypeVar where
  | flex (id : Nat)
  | rigid (id : Nat)
  deriving Repr, DecidableEq, BEq, Ord

inductive ModVar where
  | flex (id : Nat)
  | rigid (id : Nat)
  deriving Repr, DecidableEq, BEq, Ord

inductive Polarity where
  | positive | negative
  deriving Repr, DecidableEq

def Polarity.flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

/-- Ordinary, object-language modalities (Figure 1). -/
inductive Modality where
  | const (mode : Mode)
  | var (name : ModVar)
  | compose (left right : Modality)
  deriving Repr, DecidableEq

/-- Internal expressions also represent residuals and deferred lock operations. -/
inductive ModExpr where
  | const (mode : Mode)
  | var (name : ModVar)
  | compose (left right : ModExpr)
  | meet (left right : ModExpr)
  | join (left right : ModExpr)
  | leftResidual (left right : ModExpr)
  | rightResidual (left right : ModExpr)
  | close (arg : ModExpr)
  | closeInv (arg : ModExpr)
  | future (arg : ModExpr)
  | capture (arg : ModExpr)
  deriving Repr, DecidableEq, BEq

def Modality.toExpr : Modality → ModExpr
  | .const m => .const m
  | .var v => .var v
  | .compose a b => .compose a.toExpr b.toExpr

/-- Polarity enforces the grammar of left/right modalities in the paper. -/
inductive PolarMod : Polarity → Type where
  | basic : Modality → PolarMod p
  | compose : PolarMod p → PolarMod p → PolarMod p
  | join : PolarMod .positive → PolarMod .positive → PolarMod .positive
  | meet : PolarMod .negative → PolarMod .negative → PolarMod .negative
  | leftResidual : PolarMod .positive → PolarMod .negative → PolarMod .positive
  | rightResidual : PolarMod .positive → PolarMod .negative → PolarMod .negative
  | close : PolarMod .negative → PolarMod .positive
  | closeInv : PolarMod .positive → PolarMod .negative

def PolarMod.toExpr : PolarMod p → ModExpr
  | .basic m => m.toExpr
  | .compose a b => .compose a.toExpr b.toExpr
  | .join a b => .join a.toExpr b.toExpr
  | .meet a b => .meet a.toExpr b.toExpr
  | .leftResidual a b => .leftResidual a.toExpr b.toExpr
  | .rightResidual a b => .rightResidual a.toExpr b.toExpr
  | .close a => .close a.toExpr
  | .closeInv a => .closeInv a.toExpr

namespace ModExpr
def freeVariables : ModExpr → List ModVar
  | .const _ => []
  | .var v => [v]
  | .compose a b | .meet a b | .join a b | .leftResidual a b | .rightResidual a b =>
    (a.freeVariables ++ b.freeVariables).dedup
  | .close a | .closeInv a | .future a | .capture a => a.freeVariables

def vars : ModExpr → Finset ModVar
  | .const _ => ∅
  | .var v => {v}
  | .compose a b | .meet a b | .join a b | .leftResidual a b | .rightResidual a b =>
    a.vars ∪ b.vars
  | .close a | .closeInv a | .future a | .capture a => a.vars

def subst (σ : ModVar → ModExpr) : ModExpr → ModExpr
  | .const m => .const m
  | .var v => σ v
  | .compose a b => .compose (a.subst σ) (b.subst σ)
  | .meet a b => .meet (a.subst σ) (b.subst σ)
  | .join a b => .join (a.subst σ) (b.subst σ)
  | .leftResidual a b => .leftResidual (a.subst σ) (b.subst σ)
  | .rightResidual a b => .rightResidual (a.subst σ) (b.subst σ)
  | .close a => .close (a.subst σ)
  | .closeInv a => .closeInv (a.subst σ)
  | .future a => .future (a.subst σ)
  | .capture a => .capture (a.subst σ)

def eval (σ : ModVar → Option Mode) : ModExpr → Option Mode
  | .const m => some m
  | .var v => σ v
  | .compose a b => return Mode.compose (← a.eval σ) (← b.eval σ)
  | .meet a b => return Mode.meet (← a.eval σ) (← b.eval σ)
  | .join a b => return Mode.join (← a.eval σ) (← b.eval σ)
  | .leftResidual a b => do Mode.leftResidual (← a.eval σ) (← b.eval σ)
  | .rightResidual a b => do Mode.rightResidual (← a.eval σ) (← b.eval σ)
  | .close a => return Mode.close (← a.eval σ)
  | .closeInv a => return Mode.closeInv (← a.eval σ)
  | .future a => return Mode.future (← a.eval σ)
  | .capture a => return Mode.capture (← a.eval σ)

def WellFormed (σ : ModVar → Mode) (m : ModExpr) : Prop :=
  (m.eval (some ∘ σ)).isSome = true

def Below (σ : ModVar → Mode) (a b : ModExpr) : Prop :=
  ∃ x y, a.eval (some ∘ σ) = some x ∧ b.eval (some ∘ σ) = some y ∧ Mode.le x y = true

/-- `none` represents infinity, i.e. no flexible variable. -/
def minVar (m : ModExpr) : Option Nat :=
  m.freeVariables.foldl (fun acc v => match v, acc with
    | .rigid _, _ => acc
    | .flex n, none => some n
    | .flex n, some k => some (min n k)) none

def minimumLE : Option Nat → Option Nat → Bool
  | none, none => true
  | none, some _ => false
  | some _, none => true
  | some a, some b => a ≤ b

def epsilon : ModExpr := .const Mode.identity
def bottom : ModExpr := .const Mode.bottom
def top : ModExpr := .const Mode.top
end ModExpr

end ModalityInference
