import ModalityInference.ComparisonInstance
import ModalityInference.ComparisonTypes

/-! Exact partial-annotation contexts may determine their type bases and mode
images together. This positive prepass preserves every original obligation by
substitution; unrelated components remain for ordinary comparison. -/
namespace ModalityInference.ComparisonExactContext

abbrev Prepared := SchemePreparation.Prepared

/-- Every selected occurrence uses the same simultaneous substitution. Function
domains are paired syntactically because this pass asserts equality, not order. -/
def collect (p : Prepared) (total : ModExpr → Bool) :
    Ty → Ty → Substitution → Option Substitution
  | .prod a b, .prod c d, action
  | .sum a b, .sum c d, action
  | .fn a b, .fn c d, action => do
      let action ← collect p total a c action
      collect p total b d action
  | .modal a m, .modal b n, action =>
      if total n then collect p total a b action
      else ComparisonInstance.matchType p (.modal a m) (.modal b n) action
  | _, _, action => some action

def fixedType (p : Prepared) (t : Ty) : Bool :=
  t.typeVariables.all (fun v => !ComparisonInstance.typeAllowed p v) &&
    t.modeVariables.all (fun v => !ComparisonInstance.modeAllowed p v)

def fixedMode (p : Prepared) (m : ModExpr) : Bool :=
  m.freeVariables.all (fun v => !ComparisonInstance.modeAllowed p v)

/-- The final certificate check also protects calls on arbitrary prepared
records. Images may be partial, but contain no fresh source identifier. -/
def scopeCheck (p : Prepared) (action : Substitution) : Bool :=
  action.types.all (fun (n, t) => ComparisonInstance.typeAllowed p (.flex n) &&
    fixedType p t) &&
  action.modes.all (fun (n, m) => ComparisonInstance.modeAllowed p (.flex n) &&
    fixedMode p m)

def prepare (p : Prepared) (total : ModExpr → Bool) : Option Substitution := do
  if !ComparisonInstance.targetFresh p then none else do
    let action ← collect p total p.sourceType p.targetType {}
    if scopeCheck p action then some action else none

/-- Bounds are rewritten in full, including every written definedness guard. -/
def rewrite (p : Prepared) (action : Substitution) : Prepared :=
  { p with sourceType := action.ty p.sourceType, sourceBounds := action.bounds p.sourceBounds }

/-- Apply the later internal substitution to every earlier image. Earlier keys
take priority; unaffected later images are retained verbatim. -/
def finish (before : Substitution) (after : CompareSubstitution) : CompareSubstitution :=
  { types := before.types.map (fun (n, t) => (n, after.ty t)) ++
      after.types.filter (fun pair => !(before.types.map Prod.fst).contains pair.1)
    modes := (({ modes := after.modes } : Substitution).compose before).modes }

end ModalityInference.ComparisonExactContext
