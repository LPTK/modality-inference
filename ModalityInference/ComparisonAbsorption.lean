import ModalityInference.ComparisonPartial
import ModalityInference.ComparisonPartialModes

/-! Uniform, body-only modality capsules may be absorbed into their type
parameters. The certificate traverses only fixed total enclosing annotations;
partial barriers and nonuniform uses remain unchanged for ordinary comparison. -/
namespace ModalityInference.ComparisonAbsorption

abbrev Owners := List (Nat × Nat)

def modes (owners : Owners) : List Nat := (owners.map Prod.snd).dedup

def typeFree (owners : Owners) : TypeVar → Bool
  | .flex n => !(owners.map Prod.fst).contains n
  | .rigid _ => true

def modeFree (owners : Owners) : ModVar → Bool
  | .flex n => !(modes owners).contains n
  | .rigid _ => true

def disjoint (owners : Owners) (t : Ty) : Bool :=
  t.typeVariables.all (typeFree owners) && t.modeVariables.all (modeFree owners)

def modeDisjoint (owners : Owners) (m : ModExpr) : Bool :=
  m.freeVariables.all (modeFree owners)

/-- A successful rewrite is its own structural certificate. It removes only
uniform direct capsules; every other selected occurrence causes failure. -/
def rewrite (total : ModExpr → Bool) (owners : Owners) (t : Ty) : Option Ty :=
  if disjoint owners t then some t else
    match t with
    | .modal (.var (.flex x)) (.var (.flex m)) =>
      if owners.lookup x == some m then some (.var (.flex x)) else none
    | .prod a b => do pure (.prod (← rewrite total owners a) (← rewrite total owners b))
    | .sum a b => do pure (.sum (← rewrite total owners a) (← rewrite total owners b))
    | .fn a b => do pure (.fn (← rewrite total owners a) (← rewrite total owners b))
    | .modal a m =>
      if modeDisjoint owners m && total m then
        (rewrite total owners a).map (fun a => .modal a m)
      else none
    | _ => none

def sourceType (p : SchemePreparation.Prepared) : Nat → Bool :=
  fun n => p.firstType ≤ n && n < p.nextType

def sourceMode (p : SchemePreparation.Prepared) : Nat → Bool :=
  fun n => p.firstMode ≤ n && n < p.nextMode

/-- Context labels must be fixed by every exact-domain source instantiation. -/
def transparent (p : SchemePreparation.Prepared) (total : ModExpr → Bool) (m : ModExpr) : Bool :=
  total m && m.freeVariables.all (fun v => match v with
    | .flex n => !sourceMode p n
    | .rigid _ => true)

def scopeCheck (p : SchemePreparation.Prepared) (owners : Owners) : Bool :=
  owners.all fun (x, m) => sourceType p x && sourceMode p m &&
    ComparisonPartial.absentFromBounds x p.sourceBounds &&
      ComparisonPartialModes.absentFromBounds m p.sourceBounds

def capsules : Ty → Owners
  | .modal (.var (.flex x)) (.var (.flex m)) => [(x, m)]
  | .prod a b | .sum a b | .fn a b => capsules a ++ capsules b
  | .modal a _ => capsules a
  | _ => []

def candidates (p : SchemePreparation.Prepared) (total : ModExpr → Bool) : Owners :=
  ((List.range' p.firstMode (p.nextMode - p.firstMode)).flatMap fun m =>
    let owners := ((capsules p.sourceType).filter fun pair => pair.2 == m).dedup
    if scopeCheck p owners && (rewrite (transparent p total) owners p.sourceType).isSome
    then owners else []).dedup

structure Result where
  owners : Owners
  body : Ty
  deriving Repr, DecidableEq

def Result.modes (r : Result) : List Nat := ComparisonAbsorption.modes r.owners

def Result.action (r : Result) : Substitution :=
  { modes := r.modes.map fun n => (n, .epsilon) }

/-- Each candidate is a source binder group, not a type or modality witness.
The combined certificate is checked once before any capsule is removed. -/
def plan (p : SchemePreparation.Prepared) (total : ModExpr → Bool) : Result :=
  let owners := candidates p total
  if scopeCheck p owners then
    match rewrite (transparent p total) owners p.sourceType with
    | some body => ⟨owners, body⟩
    | none => ⟨[], p.sourceType⟩
  else ⟨[], p.sourceType⟩

def instantiate (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) (t : Ty) : CompareTy :=
  (CompareTy.ofTy t).subst ts ms

def neutral (owners : Owners) (ms : ModVar → ModExpr) : ModVar → ModExpr
  | .flex n => if (modes owners).contains n then .epsilon else ms (.flex n)
  | .rigid n => ms (.rigid n)

def absorb (owners : Owners) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) :
    TypeVar → CompareTy
  | .flex x => match owners.lookup x with
    | some m => .modal (ts (.flex x)) (ms (.flex m))
    | none => ts (.flex x)
  | .rigid n => ts (.rigid n)

end ModalityInference.ComparisonAbsorption
