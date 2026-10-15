import ModalityInference.ComparisonShapeSolver

/-! Structural templates for prepared scheme comparisons. Shape parameters fixed
by declared assumptions become fresh opaque leaves, retaining their shape class.
Unconstrained source shape parameters use unit; they do not choose a rigid head.
Every concrete constructor receives a fresh modality parameter. -/
namespace ModalityInference.ComparisonSkeleton

open ComparisonShapeSolver

structure Leaf where
  name : Nat
  shapeClass : TypeVar
  deriving Repr, DecidableEq

def typeCount (p : SchemePreparation.Prepared) : ComparisonShape → Nat
  | .var v => if sourceAllowed p v then 0 else 1
  | .unit | .credit => 0
  | .prod a b | .sum a b | .fn a b => typeCount p a + typeCount p b

def modeCount (p : SchemePreparation.Prepared) : ComparisonShape → Nat
  | .var v => if sourceAllowed p v then 1 else 0
  | .unit | .credit => 1
  | .prod a b | .sum a b | .fn a b => 1 + modeCount p a + modeCount p b

def build (p : SchemePreparation.Prepared) : ComparisonShape → Nat → Nat → Ty
  | .var v, nt, nm => if sourceAllowed p v then
      .modal .unit (.var (.flex nm)) else .var (.flex nt)
  | .unit, _, nm => .modal .unit (.var (.flex nm))
  | .credit, _, nm => .modal .credit (.var (.flex nm))
  | .prod a b, nt, nm => .modal
      (.prod (build p a nt (nm + 1))
        (build p b (nt + typeCount p a) (nm + 1 + modeCount p a)))
      (.var (.flex nm))
  | .sum a b, nt, nm => .modal
      (.sum (build p a nt (nm + 1))
        (build p b (nt + typeCount p a) (nm + 1 + modeCount p a)))
      (.var (.flex nm))
  | .fn a b, nt, nm => .modal
      (.fn (build p a nt (nm + 1))
        (build p b (nt + typeCount p a) (nm + 1 + modeCount p a)))
      (.var (.flex nm))

def leaves (p : SchemePreparation.Prepared) : ComparisonShape → Nat → List Leaf
  | .var v, nt => if sourceAllowed p v then [] else [⟨nt, v⟩]
  | .unit, _ | .credit, _ => []
  | .prod a b, nt | .sum a b, nt | .fn a b, nt =>
      leaves p a nt ++ leaves p b (nt + typeCount p a)

structure Templates where
  substitution : Substitution
  leaves : List Leaf
  nextType : Nat
  nextMode : Nat
  deriving Repr

def allocate (p : SchemePreparation.Prepared) (s : Solved) :
    List Nat → Nat → Nat → Templates
  | [], nt, nm => ⟨{}, [], nt, nm⟩
  | v :: rest, nt, nm =>
      let shape := s.resolveAll (.flex v)
      let tail := allocate p s rest (nt + typeCount p shape) (nm + modeCount p shape)
      { tail with
        substitution := { types := (v, build p shape nt nm) :: tail.substitution.types }
        leaves := leaves p shape nt ++ tail.leaves }

def prepare (p : SchemePreparation.Prepared) (s : Solved) : Templates :=
  allocate p s (List.range' p.firstType (p.nextType - p.firstType)) p.nextType p.nextMode

end ModalityInference.ComparisonSkeleton
