import ModalityInference.ComparisonStructuralFamily

/-! Finite child-action polynomials use the signed control basis and retain the
original residual expression. Their compilation is shared by all child entries. -/
namespace ModalityInference.ComparisonStructuralActions

open ComparisonControls ComparisonPropagation ComparisonStructuralFamily

structure Action where
  lower : CNF
  upper : CNF
  deriving Repr

def Action.apply (a : Action) (input : CNF) : CNF :=
  meet (join input a.lower) a.upper

def prepareAction (fuel : Nat) (b : Basis) (m : ModExpr) : RunResult Action := do
  let lower ← low fuel b m
  let upper ← high fuel b m
  return ⟨lower, upper⟩

def prepare (fuel : Nat) (left right : Basis) (m : ModExpr) :
    RunResult (Absorption left.types.length right.types.length) := do
  let l ← prepareAction fuel left m
  let r ← prepareAction fuel right m
  return ⟨m, Vector.ofFn (fun i => l.apply [[(i.val,true)]]),
    Vector.ofFn (fun j => r.apply [[(j.val,true)]])⟩

end ModalityInference.ComparisonStructuralActions
