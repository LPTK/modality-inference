import ModalityInference.ComparisonBody

/-! Shared type intervals with one literal partial capsule reduce to symbolic
inequalities on a shared total suffix. The capsule is taken from the input. -/
namespace ModalityInference.ComparisonCapsuleIntervals

structure Request where
  name : Nat
  endpoint : Ty
  action : ModExpr
  isLower : Bool
  deriving Repr, DecidableEq

def Request.base (total : ModExpr → Bool) (r : Request) : Ty :=
  (ComparisonBody.peel total r.endpoint).base

def Request.suffix (total : ModExpr → Bool) (r : Request) : ModExpr :=
  ComparisonPartialModes.recompose (ComparisonBody.peel total r.endpoint).labels

def Request.bound (total : ModExpr → Bool) (suffix : ModExpr) (r : Request) : Constraint :=
  let image := ModExpr.compose suffix r.action
  if r.isLower then .mode (r.suffix total) image else .mode image (r.suffix total)

structure Binding where
  name : Nat
  fresh : Nat
  base : Ty
  requests : List Request
  deriving Repr, DecidableEq

def Binding.image (b : Binding) : Ty := .modal b.base (.var (.flex b.fresh))

def Binding.bounds (total : ModExpr → Bool) (b : Binding) : Bounds :=
  b.requests.map (Request.bound total (.var (.flex b.fresh)))

/-- All occurrences share one suffix variable. Unequal literal bases remain
for other comparison phases; no representative head is selected. -/
def plan (total : ModExpr → Bool) (name fresh : Nat) (requests : List Request) :
    Option Binding :=
  let group := requests.filter (fun r => r.name == name)
  match group with
  | [] => none
  | r :: rs =>
    let base := r.base total
    if rs.all (fun s => s.base total == base) then
      some ⟨name, fresh, base, group⟩
    else none

end ModalityInference.ComparisonCapsuleIntervals
