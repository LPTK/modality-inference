import ModalityInference.SchemePreparation
import ModalityInference.ComparisonTypes

/-! Partial body annotations are retained as opaque outer prefixes. Only
unconditional outer identity/composition steps and explicitly total suffixes
are traversed. Unmatched requests remain obligations of the caller. -/
namespace ModalityInference.ComparisonPartialModes

def expressionSize : ModExpr → Nat
  | .const _ | .var _ => 1
  | .compose a b | .meet a b | .join a b | .leftResidual a b | .rightResidual a b =>
    expressionSize a + expressionSize b + 1
  | .close a | .closeInv a | .future a | .capture a => expressionSize a + 1

def modalitySize : Ty → Nat
  | .var _ | .unit | .credit => 0
  | .prod a b | .sum a b | .fn a b => modalitySize a + modalitySize b
  | .modal a m => modalitySize a + expressionSize m

/-- Rewriting stops below every nonidentity outer annotation. In particular,
this does not flatten a left composition underneath a partial right factor. -/
def normalizeOuterFuel : Nat → Ty → Ty
  | 0, t => t
  | fuel + 1, .modal a (.compose m n) =>
    normalizeOuterFuel fuel (.modal (.modal a m) n)
  | fuel + 1, .modal a m =>
    if m == .epsilon then normalizeOuterFuel fuel a else .modal a m
  | _ + 1, t => t

def normalizeOuter (t : Ty) : Ty := normalizeOuterFuel (modalitySize t) t

/-- Spines are listed from outermost annotation to innermost annotation. -/
def act : List ModExpr → CompareTy → CompareTy
  | [], a => a
  | m :: ms, a => .modal (act ms a) m

/-- Collapse only outer composition steps. The association is significant
when an intermediate annotation is partial. -/
def recompose : List ModExpr → ModExpr
  | [] => .epsilon
  | m :: ms => ms.foldl (fun outer inner => .compose inner outer) m

structure Frame where
  stem : List ModExpr
  suffix : List ModExpr
  deriving Repr, DecidableEq

def splitFuel (total : ModExpr → Bool) : Nat → List ModExpr → Frame
  | 0, ms => ⟨ms, []⟩
  | _ + 1, [] => ⟨[], []⟩
  | fuel + 1, .compose m n :: ms => splitFuel total fuel (n :: m :: ms)
  | fuel + 1, m :: ms =>
    if m == .epsilon then splitFuel total fuel ms
    else if total m then
      let frame := splitFuel total fuel ms
      ⟨frame.stem, m :: frame.suffix⟩
    else ⟨m :: ms, []⟩

def split (total : ModExpr → Bool) (ms : List ModExpr) : Frame :=
  splitFuel total ((ms.map expressionSize).sum) ms

def absentFromBounds (name : Nat) (bounds : Bounds) : Bool :=
  !bounds.any (fun c => c.modeVariables.contains (.flex name))

def eligible (p : SchemePreparation.Prepared) : List Nat :=
  (List.range' p.firstMode (p.nextMode - p.firstMode)).filter fun name =>
    absentFromBounds name p.sourceBounds

/-- A bare source mode occurrence compared with a fixed target annotation.
`isLower` means the target annotation is below the source occurrence. -/
structure Request where
  name : Nat
  target : ModExpr
  isLower : Bool
  deriving Repr, DecidableEq

structure Binding where
  name : Nat
  fresh : Nat
  stem : List ModExpr
  requests : List Request
  deriving Repr, DecidableEq

def Binding.expression (b : Binding) : ModExpr :=
  recompose (.var (.flex b.fresh) :: b.stem)

def Request.bound (total : ModExpr → Bool) (fresh : Nat) (r : Request) : Constraint :=
  let suffix := recompose (split total [r.target]).suffix
  if r.isLower then .mode suffix (.var (.flex fresh))
  else .mode (.var (.flex fresh)) suffix

def Binding.bounds (total : ModExpr → Bool) (b : Binding) : Bounds :=
  b.requests.map (Request.bound total b.fresh)

def plan (total : ModExpr → Bool) (name fresh : Nat) (requests : List Request) :
    Option Binding :=
  let group := requests.filter (fun r => r.name == name)
  match group with
  | [] => none
  | r :: rs =>
    let stem := (split total [r.target]).stem
    if rs.all (fun s => (split total [s.target]).stem == stem) then
      some ⟨name, fresh, stem, group⟩
    else none

structure Result where
  bindings : List Binding
  images : List (Nat × ModExpr)
  bounds : Bounds
  pending : List Request
  nextMode : Nat
  deriving Repr

def Result.substitution (r : Result) : Substitution := { modes := r.images }

/-- Shared partial prefixes are preserved literally; only their total suffix
is replaced by a fresh symbolic modality. No pending request is discharged. -/
def adapt (total : ModExpr → Bool) (indices : List Nat) (requests : List Request)
    (firstFresh : Nat) : Result :=
  let bindings := indices.zipIdx.filterMap fun (name, offset) =>
    plan total name (firstFresh + offset) requests
  let names := bindings.map Binding.name
  { bindings
    images := bindings.map fun b => (b.name, b.expression)
    bounds := bindings.flatMap (Binding.bounds total)
    pending := requests.filter fun r => !names.contains r.name
    nextMode := firstFresh + indices.length }

end ModalityInference.ComparisonPartialModes
