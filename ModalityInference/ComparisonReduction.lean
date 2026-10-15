import ModalityInference.ComparisonSkeleton
import ModalityInference.ComparisonPartial
import ModalityInference.ComparisonAnnotations
import ModalityInference.Constraints

/-! Shape-directed decomposition keeps opaque type inequalities intact. The
worklist contains bare subtype goals; definedness is recorded separately, only
for written source bounds and the modality rules that require it. -/
namespace ModalityInference.ComparisonReduction

structure State where
  assumptions : Bounds := []
  pending : List (Ty × Ty) := []
  inequalities : List (Ty × Ty) := []
  modes : Bounds := []
  bareVariables : List Nat := []
  bareBounds : List ComparisonPartial.BareBound := []
  partialTypes : List (Nat × CompareTy) := []
  totalModes : List ModExpr := []
  shared : Bool := false
  deriving Repr

def initial (bounds : Bounds) (source target : Ty) : State :=
  let expanded := bounds.assumptions
  { pending := expanded.filterMap (fun c => match c with
      | .sub a b => some (a, b)
      | _ => none) ++ [(source, target)]
    modes := expanded.filter (fun c => match c with
      | .mode _ _ | .defined _ => true
      | _ => false) }

/-- Only literal identity annotations are removed on the bare partial path. -/
def bareVariable (names : List Nat) : Ty → Option Nat
  | .var (.flex n) => if names.contains n then some n else none
  | .modal a .epsilon => bareVariable names a
  | _ => none

def step (s : State) : RunResult State :=
  match s.pending with
  | [] => .success s
  | (left, right) :: rest =>
    let s := { s with pending := rest }
    if left == right || s.assumptions.contains (.sub left right) then .success s else
    match bareVariable s.bareVariables left, bareVariable s.bareVariables right with
    | some n, _ => .success
        { s with bareBounds := ⟨n, right, false⟩ :: s.bareBounds }
    | _, some n => .success
        { s with bareBounds := ⟨n, left, true⟩ :: s.bareBounds }
    | none, none =>
    let total := ComparisonBody.isTotal s.totalModes
    let shared := if s.shared then ComparisonBody.stripTotal total left right else none
    match shared with
    | some step => .success
        { s with pending := step.bases :: rest
                 modes := .mode step.labels.1 step.labels.2 :: s.modes }
    | none =>
    let normalizedLeft := ComparisonPartialModes.normalizeOuter left
    let normalizedRight := ComparisonPartialModes.normalizeOuter right
    if normalizedLeft == normalizedRight then .success s else
    let suffix := if ComparisonAnnotations.hasPartial total left ||
        ComparisonAnnotations.hasPartial total right then
      ComparisonBody.suffixGoal total left right else none
    match suffix with
    | some (m, n) => .success { s with modes := .mode m n :: s.modes }
    | none =>
    let (a, l) := left.outer
    let (b, r) := right.outer
    match a, b with
    | .var _, .var _ => .success
        { s with inequalities := (left, right) :: s.inequalities
                 modes := .defined l :: .defined r :: s.modes }
    | .unit, .unit => .success { s with modes := .mode l r :: s.modes }
    | .credit, .credit => .success
        { s with modes := .mode (.compose l (.const Mode.many)) r :: s.modes }
    | .prod a b, .prod c d | .sum a b, .sum c d => .success
        { s with
          pending := (.modal a l, .modal c r) :: (.modal b l, .modal d r) :: rest
          modes := .mode l r :: s.modes }
    | .fn a b, .fn c d => .success
        { s with
          pending := (c, a) :: (b, d) :: rest
          modes := .mode l (.compose r .top) :: s.modes }
    | _, _ => .rejected "fixed type shapes do not permit structural decomposition"

def run : Nat → State → RunResult State
  | 0, _ => .exhausted
  | fuel + 1, s => if s.pending.isEmpty then .success s else do
      let next ← step s
      run fuel next

def prepare (fuel : Nat) (p : SchemePreparation.Prepared)
    (s : ComparisonSkeleton.Templates) (bare : List Nat := [])
    (knownTotal : List ModExpr := []) (shared : Bool := false) : RunResult State := do
  let initial := initial (s.substitution.bounds p.sourceBounds)
    (s.substitution.ty p.sourceType) p.targetType
  let reduced ← run fuel { initial with
    assumptions := p.assumptions
    bareVariables := bare
    totalModes := knownTotal
    shared := shared }
  let intervals := ComparisonPartial.reduceBare bare reduced.bareBounds
  run fuel { reduced with pending := intervals.goals, bareVariables := [], bareBounds := []
                          partialTypes := intervals.images }

end ModalityInference.ComparisonReduction
