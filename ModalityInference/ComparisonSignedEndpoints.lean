import ModalityInference.CompactCNF
import ModalityInference.ComparisonTypes

/-! Public endpoint syntax induces finite guarded constructor paths. Each path
contains one call to an original image, or a fixed observation. Function domains
reverse that call's sign; comparisons retain at most two signed image calls.
Calls keep their original binder and observer route, so they can share one
polynomial family rather than introducing occurrence-specific images. -/
namespace ModalityInference.ComparisonSignedEndpoints

abbrev Route := List Bool

structure Call where
  name : Nat
  route : Route
  deriving Repr, BEq, DecidableEq

inductive Data where
  | fixed (value : BoolExpr)
  | image (call : Call) (positive : Bool)
  deriving Repr

def neg (e : BoolExpr) : BoolExpr := .imp e (.const false)

def Data.flip : Data → Data
  | .fixed e => .fixed (neg e)
  | .image call positive => .image call (!positive)

structure View where
  data : Data
  lower : BoolExpr
  upper : BoolExpr
  deriving Repr

def View.base (data : Data) : View := ⟨data,.const false,.const true⟩

def View.dual (v : View) : View := ⟨v.data.flip,neg v.upper,neg v.lower⟩

def View.act (v : View) (lower upper : BoolExpr) : View :=
  ⟨v.data,.and (.or v.lower lower) upper,.and (.or v.upper lower) upper⟩

structure Clause where
  guard : BoolExpr
  literals : List (Call × Bool)
  deriving Repr

def makeClause (guard : BoolExpr) (data : List Data) : Clause :=
  ⟨.or guard (.any (data.filterMap fun d => match d with | .fixed e => some e | _ => none)),
   data.filterMap fun d => match d with | .image call positive => some (call,positive) | _ => none⟩

def compare (active : BoolExpr) (left right : View) : List Clause :=
  [makeClause (.any [neg active,neg left.lower,right.lower]) [left.data,right.data],
   makeClause (.any [neg active,neg left.lower,right.upper]) [left.data,right.data.flip],
   makeClause (.any [neg active,neg left.upper,right.lower]) [left.data.flip,right.data],
   makeClause (.any [neg active,neg left.upper,right.upper]) [left.data.flip,right.data.flip]]

structure Context where
  fixed : Route → Ty → BoolExpr
  choose : Route → BoolExpr
  action : Route → ModExpr → BoolExpr × BoolExpr

def reference (images : List Nat) (ctx : Context) (route : Route) (v : TypeVar) : Data :=
  match v with
  | .flex n => if images.contains n then .image ⟨n,route⟩ true else .fixed (ctx.fixed route (.var v))
  | .rigid _ => .fixed (ctx.fixed route (.var v))

structure Branch where
  guard : BoolExpr
  view : View
  deriving Repr

def Branch.guarded (test : BoolExpr) (b : Branch) : Branch := ⟨.and test b.guard,b.view⟩

def observe (images : List Nat) (ctx : Context) (route : Route) : Ty → List Branch
  | .var v => [⟨.const true,.base (reference images ctx route v)⟩]
  | .unit => [⟨.const true,.base (.fixed (ctx.fixed route .unit))⟩]
  | .credit => [⟨.const true,.base (.fixed (ctx.fixed route .credit))⟩]
  | .prod a b | .sum a b =>
      (observe images ctx (route++[false]) a).map (Branch.guarded (ctx.choose route)) ++
      (observe images ctx (route++[true]) b).map (Branch.guarded (neg (ctx.choose route)))
  | .fn a b =>
      (observe images ctx (route++[false]) a).map (fun branch =>
        Branch.guarded (ctx.choose route) ⟨branch.guard,branch.view.dual⟩) ++
      (observe images ctx (route++[true]) b).map (Branch.guarded (neg (ctx.choose route)))
  | .modal a m => (observe images ctx route a).map fun branch =>
      ⟨branch.guard,branch.view.act (ctx.action route m).1 (ctx.action route m).2⟩

def compile (images : List Nat) (ctx : Context) (left right : Ty) : List Clause :=
  (observe images ctx [] left).flatMap fun l =>
    (observe images ctx [] right).flatMap fun r => compare (.and l.guard r.guard) l.view r.view

structure CompiledClause where
  guard : ModalityInference.Clause
  literals : List (Call × Bool)
  deriving Repr

def compileGuards (fuel : Nat) : List Clause → RunResult (List CompiledClause)
  | [] => .success []
  | clause :: rest => do
      let guards ← CompactCNF.toCNF fuel true clause.guard
      let tail ← compileGuards fuel rest
      return guards.map (fun guard => ⟨guard,clause.literals⟩) ++ tail

end ModalityInference.ComparisonSignedEndpoints
