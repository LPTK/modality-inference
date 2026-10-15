import ModalityInference.ComparisonPartial
import ModalityInference.ComparisonPartialModes
import ModalityInference.ModeBackend

/-! Body comparison traverses common total annotations without requiring the
underlying type to be defined. Partial prefixes remain opaque. -/
namespace ModalityInference.ComparisonBody

def residuals : ModExpr → List ModExpr
  | .const _ | .var _ => []
  | .compose a b | .meet a b | .join a b => residuals a ++ residuals b
  | .leftResidual a b => .leftResidual a b :: (residuals a ++ residuals b)
  | .rightResidual a b => .rightResidual a b :: (residuals a ++ residuals b)
  | .close a | .closeInv a | .future a | .capture a => residuals a

def checkTotal (fuel : Nat) (assumptions : Bounds) : List ModExpr →
    RunResult (List ModExpr)
  | [] => .success []
  | m :: ms => do
    let report ← ConcreteBackend.entails fuel assumptions [.defined m]
    let rest ← checkTotal fuel assumptions ms
    pure (if report.valid then m :: rest else rest)

/-- Certify residual subexpressions under declared assumptions. Total syntax
constructors are handled recursively by `isTotal`. -/
def knownTotal (fuel : Nat) (assumptions : Bounds) (expressions : List ModExpr) :
    RunResult (List ModExpr) :=
  checkTotal fuel assumptions (expressions.flatMap residuals).eraseDups

def isTotal (known : List ModExpr) : ModExpr → Bool
  | .const _ | .var _ => true
  | .compose a b | .meet a b | .join a b => isTotal known a && isTotal known b
  | .leftResidual a b => known.contains (.leftResidual a b)
  | .rightResidual a b => known.contains (.rightResidual a b)
  | .close a | .closeInv a | .future a | .capture a => isTotal known a

def dropIdentity : Ty → Option Ty
  | .modal a m => if m == .epsilon then some a else none
  | _ => none

def stripSharedDirect (total : ModExpr → Bool) (left right : Ty) : Option (Ty × Ty) :=
  match dropIdentity left with
  | some a => some (a, right)
  | none => match dropIdentity right with
    | some b => some (left, b)
    | none => match left, right with
      | .modal a m, .modal b n => if m == n && total m then some (a, b) else none
      | _, _ => none

/-- Shared annotations are removed before any outer normalization, preserving
the visible common wrapper around a partial image. This is a sufficient
comparison step, not an invertible decomposition in the presence of bounds. -/
def stripShared (total : ModExpr → Bool) (left right : Ty) : Option (Ty × Ty) :=
  match stripSharedDirect total left right with
  | some pair => some pair
  | none =>
    let a := ComparisonPartialModes.normalizeOuter left
    let b := ComparisonPartialModes.normalizeOuter right
    match stripSharedDirect total a b with
    | some pair => some pair
    | none => if a == left && b == right then none else some (a, b)

def traversalSize : Ty → Nat
  | .var _ | .unit | .credit => 1
  | .prod a b | .sum a b | .fn a b => traversalSize a + traversalSize b + 1
  | .modal a m => traversalSize a + ComparisonPartialModes.expressionSize m + 1

def pairedOccurrencesFuel (name : Nat) (total : ModExpr → Bool) : Nat → Ty → Ty → Bool
  | 0, left, right => ComparisonPartial.bareOccurrences name false left &&
      ComparisonPartial.bareOccurrences name false right
  | fuel + 1, left, right =>
    match stripShared total left right with
    | some (a, b) => pairedOccurrencesFuel name total fuel a b
    | none => match left, right with
      | .prod a b, .prod c d | .sum a b, .sum c d =>
        pairedOccurrencesFuel name total fuel a c && pairedOccurrencesFuel name total fuel b d
      | .fn a b, .fn c d =>
        pairedOccurrencesFuel name total fuel c a && pairedOccurrencesFuel name total fuel b d
      | _, _ => ComparisonPartial.bareOccurrences name false left &&
          ComparisonPartial.bareOccurrences name false right

def pairedOccurrences (name : Nat) (total : ModExpr → Bool) (left right : Ty) : Bool :=
  pairedOccurrencesFuel name total (traversalSize left + traversalSize right + 1) left right

def eligible (p : SchemePreparation.Prepared) (total : ModExpr → Bool) : List Nat :=
  (List.range' p.firstType (p.nextType - p.firstType)).filter fun name =>
    ComparisonPartial.absentFromBounds name p.sourceBounds &&
      pairedOccurrences name total p.sourceType p.targetType

structure Suffix where
  base : Ty
  labels : List ModExpr
  deriving Repr, DecidableEq

def peelFuel (total : ModExpr → Bool) : Nat → Ty → Suffix
  | 0, t => ⟨t, []⟩
  | fuel + 1, t =>
    let a := ComparisonPartialModes.normalizeOuter t
    match a with
    | .modal b m =>
      if total m then
        let rest := peelFuel total fuel b
        ⟨rest.base, m :: rest.labels⟩
      else ⟨a, []⟩
    | _ => ⟨a, []⟩

def peel (total : ModExpr → Bool) (t : Ty) : Suffix :=
  peelFuel total (traversalSize t + 1) t

/-- Compare only certified total suffixes above the same opaque base. The
partial annotations inside that base produce no new definedness obligation. -/
def suffixGoal (total : ModExpr → Bool) (left right : Ty) : Option (ModExpr × ModExpr) :=
  let a := peel total left
  let b := peel total right
  if a.base == b.base then
    some (ComparisonPartialModes.recompose a.labels, ComparisonPartialModes.recompose b.labels)
  else none

end ModalityInference.ComparisonBody
