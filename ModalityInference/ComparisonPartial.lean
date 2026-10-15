import ModalityInference.ComparisonInterpolation
import ModalityInference.SchemePreparation

/-! Bare body variables may be instantiated with fixed partial target subtrees.
Their intervals retain those subtrees verbatim and reconstruct finite joins or
meets. Eligibility excludes the full source-bound domain; those bounds keep
their original definedness requirements. -/
namespace ModalityInference.ComparisonPartial

/-- Product and sum components inherit their enclosing modality. Function
arguments and results start a new modality context. -/
def bareOccurrences (name : Nat) (masked : Bool) : Ty → Bool
  | .var (.flex n) => if n == name then !masked else true
  | .var (.rigid _) | .unit | .credit => true
  | .prod a b | .sum a b => bareOccurrences name masked a && bareOccurrences name masked b
  | .fn a b => bareOccurrences name false a && bareOccurrences name false b
  | .modal a m => bareOccurrences name (masked || !(m == .epsilon)) a

def absentFromBounds (name : Nat) (bounds : Bounds) : Bool :=
  !bounds.any (fun c => c.typeVariables.contains (.flex name))

def eligible (p : SchemePreparation.Prepared) : List Nat :=
  (List.range' p.firstType (p.nextType - p.firstType)).filter fun name =>
    absentFromBounds name p.sourceBounds && bareOccurrences name false p.sourceType

structure BareBound where
  name : Nat
  endpoint : Ty
  isLower : Bool
  deriving Repr, DecidableEq

def lower (name : Nat) (bounds : List BareBound) : List Ty :=
  bounds.filterMap fun b => if b.name == name && b.isLower then some b.endpoint else none

def upper (name : Nat) (bounds : List BareBound) : List Ty :=
  bounds.filterMap fun b => if b.name == name && !b.isLower then some b.endpoint else none

def image (name : Nat) (bounds : List BareBound) : CompareTy :=
  ComparisonInterpolation.witness
    ((lower name bounds).map CompareTy.ofTy) ((upper name bounds).map CompareTy.ofTy)

def crossed (name : Nat) (bounds : List BareBound) : List (Ty × Ty) :=
  (lower name bounds).flatMap fun a => (upper name bounds).map fun b => (a, b)

structure BareReduction where
  images : List (Nat × CompareTy)
  goals : List (Ty × Ty)
  remaining : List BareBound
  deriving Repr

def BareReduction.substitution (result : BareReduction) : CompareSubstitution :=
  { types := result.images }

/-- Each selected interval is eliminated algebraically. Unselected obligations
are retained, and no definedness requirement is attached to the bare body. -/
def reduceBare (indices : List Nat) (bounds : List BareBound) : BareReduction :=
  { images := indices.map fun name => (name, image name bounds)
    goals := indices.flatMap fun name => crossed name bounds
    remaining := bounds.filter fun b => !indices.contains b.name }

end ModalityInference.ComparisonPartial
