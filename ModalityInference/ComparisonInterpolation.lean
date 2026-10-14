import ModalityInference.ComparisonTypes

/-! Finite interpolation for an isolated comparison variable. The endpoints are
already independent of that variable; this module does not normalize structural
cycles or select representatives of rigid types. -/
namespace ModalityInference.ComparisonInterpolation

def join (head : CompareTy) : List CompareTy → CompareTy
  | [] => head
  | next :: rest => .join head (join next rest)

def meet (head : CompareTy) : List CompareTy → CompareTy
  | [] => head
  | next :: rest => .meet head (meet next rest)

/-- Nonempty lowers determine a join. An upper-only interval uses their meet;
an unconstrained variable can be instantiated by unit. No extrema are needed. -/
def witness (lower upper : List CompareTy) : CompareTy :=
  match lower, upper with
  | head :: rest, _ => join head rest
  | [], head :: rest => meet head rest
  | [], [] => .unit

def Interval (Δ : Bounds) (lower upper : List CompareTy) (t : CompareTy) : Prop :=
  (∀ a ∈ lower, CompareSubtype Δ a t) ∧
    (∀ b ∈ upper, CompareSubtype Δ t b)

def Crossed (Δ : Bounds) (lower upper : List CompareTy) : Prop :=
  ∀ a ∈ lower, ∀ b ∈ upper, CompareSubtype Δ a b

def EndpointsDefined (Δ : Bounds) (types : List CompareTy) : Prop :=
  ∀ t ∈ types, t.DefinedUnder Δ

def GuardedInterval (Δ : Bounds) (lower upper : List CompareTy) (t : CompareTy) : Prop :=
  (∀ a ∈ lower, CompareEntails Δ (.sub a t)) ∧
    (∀ b ∈ upper, CompareEntails Δ (.sub t b))

/-- Reflexive constraints retain the endpoint guards even when there are no
crossed pairs because one side of the interval is empty. -/
def eliminate (lower upper : List CompareTy) : CompareBounds :=
  lower.flatMap (fun a => upper.map (CompareConstraint.sub a)) ++
    (lower ++ upper).map (fun t => .sub t t)

/-- A common predicate for tracking free type and modality identifiers without
committing to a particular finite set representation. -/
def Supports (types : TypeVar → Prop) (modes : ModVar → Prop) : CompareTy → Prop
  | .var v => types v
  | .unit | .credit => True
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b =>
    Supports types modes a ∧ Supports types modes b
  | .modal a m => Supports types modes a ∧ ∀ v ∈ m.vars, modes v

end ModalityInference.ComparisonInterpolation
