import ModalityInference.ComparisonShapes
import ModalityInference.SchemePreparation

/-! Two-stage finite shape preparation. Declared equations are unified first;
their remaining parameters are frozen before source equations are considered.
These substitutions describe shapes, never substitutions of rigid type names. -/
namespace ModalityInference.ComparisonShapeSolver

abbrev Assignment := List (TypeVar × ComparisonShape)
abbrev Pairs := List (ComparisonShape × ComparisonShape)

def action (s : Assignment) (v : TypeVar) : ComparisonShape :=
  (s.lookup v).getD (.var v)

def replace (v : TypeVar) (t : ComparisonShape) (w : TypeVar) : ComparisonShape :=
  if w == v then t else .var w

def mapPairs (ρ : TypeVar → ComparisonShape) (ps : Pairs) : Pairs :=
  ps.map fun (a, b) => (a.subst ρ, b.subst ρ)

/-- Only a permitted variable can be eliminated. A fixed left endpoint does not
prevent a permitted variable on the right from being solved. -/
def choose (allowed : TypeVar → Bool) (a b : ComparisonShape) :
    Option (TypeVar × ComparisonShape) :=
  match a with
  | .var v => if allowed v then some (v, b) else
      match b with
      | .var w => if allowed w then some (w, a) else none
      | _ => none
  | _ => match b with
      | .var w => if allowed w then some (w, a) else none
      | _ => none

def unify : Nat → (TypeVar → Bool) → Pairs → RunResult Assignment
  | 0, _, _ => .exhausted
  | _ + 1, _, [] => .success []
  | fuel + 1, allowed, (a, b) :: rest =>
    if a == b then unify fuel allowed rest
    else match choose allowed a b with
    | some (v, t) =>
      if t.vars.contains v then .rejected "cyclic finite shape equation"
      else do
        let s ← unify fuel allowed (mapPairs (replace v t) rest)
        return (v, t.subst (action s)) :: s
    | none => match a, b with
      | .prod a b, .prod c d | .sum a b, .sum c d | .fn a b, .fn c d =>
        unify fuel allowed ((a, c) :: (b, d) :: rest)
      | _, _ => .rejected "incompatible or fixed type shapes"

structure Solved where
  fixed : Assignment
  source : Assignment
  deriving Repr

/-- The declared interpretation of original fixed shape names. -/
def Solved.fixedShapes (s : Solved) : TypeVar → ComparisonShape := action s.fixed

/-- Resolve a fresh source variable through both stages. -/
def Solved.resolveAll (s : Solved) (v : TypeVar) : ComparisonShape :=
  (s.fixedShapes v).subst (action s.source)

inductive Result where
  /-- No finite shape assignment satisfies the declared equations. This is not
  a negative answer to scheme subsumption under those assumptions. -/
  | infeasibleAssumptions
  | solved (shapes : Solved)
  deriving Repr

def sourceAllowed (p : SchemePreparation.Prepared) : TypeVar → Bool
  | .flex n => p.firstType ≤ n && n < p.nextType
  | .rigid _ => false

/-- Source-bound guards remain in the prepared input. Shape checking erases
modalities and adds the bare body pair without imposing a definedness guard. -/
def sourcePairs (p : SchemePreparation.Prepared) : Pairs :=
  ComparisonShape.pairs p.sourceBounds ++
    [(ComparisonShape.ofTy p.sourceType, ComparisonShape.ofTy p.targetType)]

def prepare (fuel : Nat) (p : SchemePreparation.Prepared) : RunResult Result :=
  match unify fuel (fun _ => true) (ComparisonShape.pairs p.assumptions) with
  | .exhausted => .exhausted
  | .rejected _ => .success .infeasibleAssumptions
  | .success fixed => do
      let source ← unify fuel (sourceAllowed p) (mapPairs (action fixed) (sourcePairs p))
      return .solved ⟨fixed, source⟩

end ModalityInference.ComparisonShapeSolver
