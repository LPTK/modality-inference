import ModalityInference.ComparisonChecker

namespace ModalityInference.ComparisonRegression

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def rejected (result : RunResult α) : Bool :=
  match result with | .rejected _ => true | _ => false

def shapes (source target : Scheme) :=
  ComparisonShapeSolver.prepare 100 (SchemePreparation.prepare [] source target)

-- Original free names cannot be specialized by the source shape solver.
#guard rejected (shapes (.mono (.var (.flex 0))) (.mono .unit))
#guard rejected (shapes (.mono .unit) (.mono .credit))
#guard (shapes {typeParams := [0], body := .var (.flex 0)} (.mono .unit)).isSuccess

-- Inconsistent declared shapes are distinct from an impossible source shape.
#guard match shapes (.mono .unit)
    { bounds := [.sub .unit .credit], body := .unit } with
  | .success .infeasibleAssumptions => true
  | _ => false

-- Cyclic constructor requirements have no finite source shape.
#guard rejected (shapes
  { typeParams := [0]
    bounds := [.sub (.var (.flex 0)) (.fn (.var (.flex 0)) .unit)]
    body := .unit } (.mono .unit))

def reduce (source target : Scheme) : RunResult ComparisonReduction.State := do
  let p := SchemePreparation.prepare [] source target
  match ← ComparisonShapeSolver.prepare 100 p with
  | .infeasibleAssumptions => .rejected "infeasible declared shapes"
  | .solved s => ComparisonReduction.prepare 100 p (ComparisonSkeleton.prepare p s)

def undefinedMode : ModExpr := .leftResidual .epsilon (.const Mode.bottom)
def partialBody : Ty := .modal .unit undefinedMode

-- Body reflexivity introduces no annotation guard; a written bound keeps it.
#guard match reduce (.mono partialBody) (.mono partialBody) with
  | .success state => state.modes.isEmpty && state.inequalities.isEmpty
  | _ => false
#guard match reduce { bounds := [.sub partialBody partialBody], body := .unit }
    (.mono .unit) with
  | .success state => !state.modes.isEmpty
  | _ => false

def head (n : Nat) : Ty := .var (.rigid n)
def crossed : Bounds := [.sub (head 0) (head 2), .sub (head 0) (head 3),
  .sub (head 1) (head 2), .sub (head 1) (head 3)]
def interval : Scheme :=
  { typeParams := [0]
    bounds := [.sub (head 0) (.var (.flex 0)), .sub (head 1) (.var (.flex 0)),
      .sub (.var (.flex 0)) (head 2), .sub (.var (.flex 0)) (head 3)]
    body := .unit }

def intervalGroups : RunResult (List ComparisonGroups.Group) := do
  let p := SchemePreparation.prepare [] interval { bounds := crossed, body := .unit }
  match ← ComparisonShapeSolver.prepare 100 p with
  | .infeasibleAssumptions => .rejected "infeasible declared shapes"
  | .solved shapes =>
      let templates := ComparisonSkeleton.prepare p shapes
      let reduced ← ComparisonReduction.prepare 100 p templates
      ComparisonGroups.collect p shapes templates reduced

-- Shape unification keeps all four distinct rigid heads for lattice propagation.
#guard match intervalGroups with
  | .success [group] => group.heads.length == 4 && group.leaves.length == 1 &&
      group.assumptions.length == 4 && group.goals.length == 4
  | _ => false

-- Every opaque obligation reaches a group, including a class with no generator.
def unsupportedOpaqueInput := SchemePreparation.prepare [] (.mono .unit) (.mono .unit)
def unsupportedOpaqueShapes : ComparisonShapeSolver.Solved :=
  { fixed := [(.rigid 1, .var (.rigid 0))], source := [] }
def unsupportedOpaqueTemplates : ComparisonSkeleton.Templates := ⟨{}, [], 0, 0⟩
def unsupportedOpaqueState : ComparisonReduction.State :=
  { inequalities := [(head 0, head 1)] }

#guard match ComparisonGroups.collect unsupportedOpaqueInput unsupportedOpaqueShapes
    unsupportedOpaqueTemplates unsupportedOpaqueState with
  | .success [group] => group.heads.isEmpty && group.goals.length == 1
  | _ => false
#guard rejected (ComparisonElimination.run 100 unsupportedOpaqueInput unsupportedOpaqueShapes
  unsupportedOpaqueTemplates unsupportedOpaqueState)

def compare (source target : Scheme) := ComparisonChecker.run 20000 source target

-- Credit signatures require the ordinary ordering of their complete modalities.
#guard rejected (compare (.mono (.modal .credit .epsilon))
  (.mono (.modal .credit (.const Mode.many))))
#guard (compare (.mono (.modal .credit (.const Mode.many)))
  (.mono (.modal .credit .epsilon))).isSuccess
#guard (compare (.mono (.modal .credit .epsilon))
  (.mono (.modal .credit (.const Mode.aliased)))).isSuccess

-- Internal joins witness the rigid interval, without selecting one rigid head.
#guard (compare interval { bounds := crossed, body := .unit }).isSuccess
#guard rejected (compare interval { bounds := crossed.drop 1, body := .unit })

-- Shape compatibility rules out combining unrelated constructors.
#guard rejected (compare
  { typeParams := [0]
    bounds := [.sub .unit (.var (.flex 0)), .sub .credit (.var (.flex 0))]
    body := .unit } (.mono .unit))

-- Body-only type images retain partial target syntax, with no new guards.
#guard (compare { typeParams := [0], body := .var (.flex 0) }
  (.mono partialBody)).isSuccess
#guard (compare { typeParams := [0], body := .fn (.var (.flex 0)) (.var (.flex 0)) }
  (.mono (.fn partialBody partialBody))).isSuccess
#guard (compare
  { typeParams := [0], body := .prod (.var (.flex 0)) (.var (.flex 0)) }
  (.mono (.prod partialBody .unit))).isSuccess
#guard rejected (compare { bounds := [.sub partialBody partialBody], body := .unit }
  (.mono .unit))
#guard rejected (compare (.mono (.var (.flex 0))) (.mono .unit))

-- Exact body certificates may contain partial type and modality images.
#guard (compare { typeParams := [0], body := .modal (.var (.flex 0)) (.const Mode.global) }
  (.mono (.modal partialBody (.const Mode.global)))).isSuccess
#guard (compare { modParams := [0], body := .modal .unit (.var (.flex 0)) }
  (.mono partialBody)).isSuccess
#guard (compare (.mono (.modal partialBody .epsilon))
  (.mono (.modal .unit (.compose undefinedMode .epsilon)))).isSuccess

-- One partial prefix supports different total suffixes, with a single mode image.
#guard (compare
  { modParams := [0]
    body := .prod (.modal .unit (.var (.flex 0))) (.modal .unit (.var (.flex 0))) }
  (.mono (.prod (.modal .unit (.compose undefinedMode .epsilon))
    (.modal .unit (.compose undefinedMode (.const Mode.global)))))).isSuccess

-- Sufficient shared-wrapper reduction also handles strict sibling comparisons.
#guard (compare
  { typeParams := [0]
    body := .prod (.modal (.var (.flex 0)) (.const Mode.global)) .unit }
  (.mono (.prod (.modal partialBody (.const Mode.global)) (.modal .unit .top)))).isSuccess

def masked (t : Ty) : Ty := .modal t (.const Mode.global)
def maskedFunction : Scheme :=
  { typeParams := [0]
    body := .fn (masked (.var (.flex 0))) (.prod (masked (.var (.flex 0))) .unit) }
def maskedTarget (result : Ty) : Scheme :=
  .mono (.fn (masked partialBody) (.prod (masked result) (.modal .unit .top)))
#guard (compare maskedFunction (maskedTarget partialBody)).isSuccess
#guard rejected (compare maskedFunction (maskedTarget .unit))

-- The strengthened path preserves each form of written source-bound guard.
#guard ([ [.sub (.var (.flex 0)) (.var (.flex 0))],
    [.equiv (.var (.flex 0)) (.var (.flex 0))],
    [.equal (.flex 0) (.var (.flex 0))] ] : List Bounds).all fun bounds =>
  rejected (compare { maskedFunction with bounds := bounds } (maskedTarget partialBody))

-- Repeated holes in compound annotations are matched simultaneously.
#guard (compare
  { modParams := [0, 1]
    body := .prod (.modal .unit (.compose (.var (.flex 0)) (.var (.flex 1))))
      (.prod (.modal .unit (.var (.flex 0))) (.modal .unit (.var (.flex 1)))) }
  (.mono (.prod (.modal .unit (.compose undefinedMode (.const Mode.global)))
    (.prod partialBody (.modal .unit (.const Mode.global)))))).isSuccess

-- Partial mode contexts are matched without demanding exact sibling bodies.
#guard (compare
  { modParams := [0, 1]
    body := .prod (.modal (.modal (head 0) (.var (.flex 0))) (.var (.flex 1))) .unit }
  (.mono (.prod (.modal (.modal (head 0) undefinedMode) (.const Mode.global))
    (.modal .unit .top)))).isSuccess
#guard rejected (compare
  { modParams := [0, 1], bounds := [.defined (.var (.flex 0))]
    body := .prod (.modal (.modal (head 0) (.var (.flex 0))) (.var (.flex 1))) .unit }
  (.mono (.prod (.modal (.modal (head 0) undefinedMode) (.const Mode.global))
    (.modal .unit .top))))

-- Uniform body-only mode capsules can be absorbed into their type images.
def capsule (x m : Nat) : Ty := .modal (.var (.flex x)) (.var (.flex m))
def coupledSource : Scheme :=
  { typeParams := [0], modParams := [0]
    body := .prod (capsule 0 0) (capsule 0 0) }
def coupledTarget : Scheme :=
  { bounds := [.sub (head 0) (head 1)]
    body := .prod (.modal (head 0) undefinedMode) (.modal (head 1) undefinedMode) }
#guard match compare coupledSource coupledTarget with
  | .success result => result.substitution.mode (.flex 0) == .epsilon &&
      (result.substitution.type (.flex 0)).wellFormedBounds.contains (.defined undefinedMode)
  | _ => false
#guard (compare
  { typeParams := [0, 1], modParams := [0]
    body := .prod (capsule 0 0) (.prod (capsule 1 0) .unit) }
  (.mono (.prod partialBody (.prod (.modal .credit undefinedMode) (.modal .unit .top))))).isSuccess

-- Context matching must preserve the identity choice of absorbed modalities.
#guard match compare
    { typeParams := [7], modParams := [11, 4]
      body := .prod (.prod (capsule 7 11) (capsule 7 11))
        (.prod (.modal (head 92) (.close (.var (.flex 4)))) .unit) }
    { bounds := [.sub (head 93) (head 94)]
      body := .prod (.prod (.modal (head 93) undefinedMode) (.modal (head 94) undefinedMode))
        (.prod (.modal (head 92) (.close undefinedMode)) (.modal .unit .top)) } with
  | .success result => result.substitution.mode (.flex 11) == .epsilon &&
      result.substitution.mode (.flex 4) == undefinedMode &&
      result.substitution.types.map Prod.fst == [7] &&
      result.substitution.modes.map Prod.fst == [11, 4]
  | _ => false

-- An opaque partial context can determine a bound-constrained type base.
def constrainedPartialSource : Scheme :=
  { typeParams := [0], modParams := [0]
    bounds := [.sub (head 0) (.var (.flex 0)), .sub (.var (.flex 0)) (head 0)]
    body := .prod (capsule 0 0) .unit }
def constrainedPartialTarget : Scheme :=
  .mono (.prod (.modal (head 0) undefinedMode) (.modal .unit .top))
#guard match compare constrainedPartialSource constrainedPartialTarget with
  | .success result => result.substitution.type (.flex 0) == .ofTy (head 0) &&
      result.substitution.mode (.flex 0) == undefinedMode &&
      result.substitution.types.map Prod.fst == [0] &&
      result.substitution.modes.map Prod.fst == [0]
  | _ => false
#guard rejected (compare
  { constrainedPartialSource with
    bounds := .defined (.var (.flex 0)) :: constrainedPartialSource.bounds }
  constrainedPartialTarget)

-- Modal propagation preserves dependence on the fixed type endpoints.
def aliased (t : Ty) : Ty := .modal t (.const Mode.aliased)
#guard (compare
  { typeParams := [0]
    bounds := [.sub (aliased (head 0)) (aliased (.var (.flex 0))),
      .sub (.var (.flex 0)) (head 1)]
    body := .unit }
  { bounds := [.sub (aliased (head 0)) (aliased (head 1))], body := .unit }).isSuccess

-- A common total mask cannot be cancelled when doing so loses declared bounds.
def global (t : Ty) : Ty := .modal t (.const Mode.global)
#guard (compare
  { typeParams := [0], body := .fn (global (.var (.flex 0))) (global (.var (.flex 0))) }
  { bounds := [.sub (global (head 0)) (global (head 1))]
    body := .fn (global (head 0)) (global (head 1)) }).isSuccess

-- Impossible scalar bounds do not reverse the modality-unaffected rigid order.
#guard rejected (compare (.mono (head 1))
  { bounds := [.sub (head 0) (head 1), .mode .top .bottom], body := head 0 })
#guard (compare (.mono (head 0))
  { bounds := [.sub (head 0) (head 1), .mode .top .bottom], body := head 1 }).isSuccess

-- Cycles are handled by propagation; an unused source variable is instantiated.
#guard (compare
  { typeParams := [0, 1, 2]
    bounds := [.sub (.var (.flex 0)) (.var (.flex 1)),
      .sub (.var (.flex 1)) (.var (.flex 0)), .sub (head 0) (.var (.flex 0)),
      .sub (.var (.flex 1)) (head 1)]
    body := .unit }
  { bounds := [.sub (head 0) (head 1)], body := .unit }).isSuccess

#guard match ComparisonChecker.run 0 interval { bounds := crossed, body := .unit } with
  | .exhausted => true
  | _ => false

-- Public scheme bodies and bounds still have the join-free `Ty` grammar.
#guard match compare interval { bounds := crossed, body := .unit } with
  | .success result => result.substitution.types.map Prod.fst == [0] &&
      result.substitution.modes.isEmpty
  | _ => false

end ModalityInference.ComparisonRegression
