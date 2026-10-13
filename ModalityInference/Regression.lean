import ModalityInference.Examples
import ModalityInference.Core.Scoping

/-! Executable regression checks. No imports from `Proofs` and no native-decide
axioms: these commands run examples; they do not assert metatheorems. -/
namespace ModalityInference.Regression
open Examples
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def modeCode (m : Mode) : Nat := 4*m.isLocal.toNat + 2*m.once.toNat + (!m.unique).toNat
#guard Mode.all.length = 8
#guard (Mode.all.map modeCode).dedup.length = 8
#guard Mode.all.all fun a => Mode.all.all fun b =>
  Mode.le a b == ((modeCode a &&& modeCode b) == modeCode a)
#guard Mode.all.all fun a => Mode.all.all fun b => Mode.all.all fun c =>
  Mode.le a (b.meet c) == (Mode.le a b && Mode.le a c)
#guard Mode.all.all fun a => Mode.all.all fun b => Mode.all.all fun c =>
  Mode.le (a.join b) c == (Mode.le a c && Mode.le b c)
#guard Mode.all.all fun a => a.compose Mode.identity == a
#guard Mode.all.all fun a => Mode.all.all fun b => Mode.all.all fun c =>
  (a.compose b).compose c == a.compose (b.compose c)
#guard Mode.all.all fun a => Mode.all.all fun b =>
  match a.leftResidual b with
  | none => !(Mode.all.any fun c => Mode.le a (b.compose c))
  | some r => Mode.all.all fun c => Mode.le r c == Mode.le a (b.compose c)
#guard Mode.all.all fun a => Mode.all.all fun b =>
  match a.rightResidual b with
  | none => !(Mode.all.any fun c => Mode.le (c.compose a) b)
  | some r => Mode.all.all fun c => Mode.le c r == Mode.le (c.compose a) b
#guard Mode.all.all fun a => Mode.all.all fun b =>
  Mode.le a.close b == Mode.le b.closeInv a
-- Moving the *same* closure operator to the other side is wrong.
#guard Mode.le Mode.identity.close Mode.bottom != Mode.le Mode.bottom.close Mode.identity
#guard Mode.all.all fun a => Mode.all.all fun b =>
  if a.isLocal == b.isLocal && a.once == b.once then a.capture == b.capture else true
#guard ModExpr.minimumLE none (some 0) = false
#guard ModExpr.minimumLE (some 0) none = true

-- The past comparison goes from right to left.
#guard !(Mode.le Mode.aliased Mode.identity)
#guard Mode.le Mode.identity Mode.aliased
#guard rejected (solve 200 [.defined (.leftResidual (.const Mode.identity) (.const Mode.bottom))])
#guard rejected (solve 200 [.defined (.rightResidual (.const Mode.aliased) (.const Mode.identity))])

-- Variable scopes, binder order and capture-avoiding substitution.
#guard identity.freeVars = ∅
#guard (Term.split (.var 4) (.pair (.var 1) (.var 6)) : RawTerm).freeVars = {3,4}
#guard (Term.lam () (.app (.var 0) (.var 1)) : RawTerm).subst
  (fun _ => .var 0) = .lam () (.app (.var 0) (.var 1))
#guard (Term.var 0 : RawTerm).rename (·+2) = .var 2
#guard rejected (infer 500 [] (.var 0))
def captureAvoidance : Scheme :=
  ({typeParams := [0], body := .fn (.var (.flex 0)) (.var (.flex 1))} : Scheme).subst
    {types := [(1,.var (.flex 0))]}
#guard captureAvoidance.typeParams = [2]
#guard captureAvoidance.body == .fn (.var (.flex 2)) (.var (.flex 0))
#guard ((Scheme.generalize [] (.var (.flex 0))).instantiate 7 9).2 == .var (.flex 7)
#guard ((Scheme.generalize [] (.var (.flex 0))).instantiate 7 9 true).2 == .var (.rigid 7)
#guard ({typeParams := [40], body := .unit} : Scheme).freshTypeIndex = 41

-- Scheme instantiation transports captured metadata, including after alpha-renaming.
def instantiatedCreditAt (m : Mode) : RunResult InstantiatedValue → Bool
  | .success r =>
    r.type == .fn .unit (.modal .credit (.const m)) &&
      match r.value with
      | .closure [.credit (.heap 0)] [some captured] (.var 1) =>
        captured.body == .modal .credit (.const m)
      | _ => false
  | _ => false
#guard Mode.all.all fun m =>
  instantiatedCreditAt m (polymorphicCapturedCredit.instantiate [] [.const m])
#guard Mode.all.all fun m =>
  instantiatedCreditAt m ((polymorphicCapturedCredit.subst {}).instantiate [] [.const m])
#guard rejected (polymorphicCapturedCredit.instantiate [] [])
#guard rejected (polymorphicCapturedCredit.instantiate [.unit] [.const Mode.identity])

-- Definedness is retained even for unused quantified arguments.
def badArgument : ModExpr := .leftResidual (.const Mode.identity) (.const Mode.bottom)
def checkInstantiation (p : SchemeValue) (types : List Ty) (modes : List ModExpr) :
    RunResult Solved := do
  let r ← p.instantiate types modes
  solve 500 r.bounds
def unusedArguments : SchemeValue :=
  ⟨{typeParams := [0], modParams := [0], body := .unit}, .unit⟩
#guard rejected (checkInstantiation polymorphicCapturedCredit [] [badArgument])
#guard rejected (checkInstantiation unusedArguments [.unit] [badArgument])
#guard rejected (checkInstantiation unusedArguments
  [.fn .unit (.prod .unit (.modal .credit badArgument))] [.const Mode.identity])
#guard Mode.all.all fun m =>
  (checkInstantiation unusedArguments [.modal .credit (.const m)] [.const m]).isSuccess

-- All constructors, both case alternatives, closed polymorphism and locality.
def evaluate (t : RawTerm) : RunResult Value := do
  let r ← infer 5000 [] t
  evalFuel 100 initialSupplies [] r.elaborated
def isUnit : RunResult Value → Bool
  | .success .unit => true
  | _ => false
def isHeapPair : RunResult Value → Bool
  | .success (.pair (.heap _) _ _) => true
  | _ => false
def isStackPair : RunResult Value → Bool
  | .success (.pair (.stack _ _) _ _) => true
  | _ => false
#guard isUnit (evaluate (.app identity .unit))
#guard isHeapPair (evaluate heapPair)
#guard isStackPair (evaluate stackPair)
#guard isStackPair (evaluate reusePair)
#guard isUnit (evaluate stackScoped)
#guard isHeapPair (evaluate polyIdentity)
#guard isUnit (evaluate (.case (.inl .unit) (.var 0) .unit))
#guard isUnit (evaluate (.case (.inr .unit) .unit (.var 0)))
#guard isUnit (evaluate (.defn .unit (.var 0)))
#guard (infer 3000 [] (.app branchUsage .unit)).isSuccess
#guard rejected (infer 4000 [] (.defn stackEscape .unit))
#guard exhausted (infer 1 [] heapPair)
#guard (infer 2000 [] heapPair).isSuccess
#guard exhausted (evalFuel 1 initialSupplies [] (.pair .unit .unit))
#guard isHeapPair (evalFuel 10 initialSupplies [] (.pair .unit .unit))
#guard rejected (evalFuel 10 initialSupplies [] (.app .unit .unit))

-- Allocation partitioning: slices exclude the reserved head and do not overlap.
#guard ((initialSupplies.afterHeap.branch 2 0).heap.at 0) = 1
#guard ((initialSupplies.afterHeap.branch 2 1).heap.at 0) = 2
#guard (List.range 30).all fun i => (List.range 30).all fun j =>
  (initialSupplies.branch 2 0).heap.at i != (initialSupplies.branch 2 1).heap.at j
#guard (initialSupplies.branch 2 0).enter.currentFrame !=
  (initialSupplies.branch 2 1).enter.currentFrame

-- Explicit counterexample to mode-only support: the pair owns its cell, but its
-- aliased credit field is still not owned. Liveness must check that field separately.
def aliasedField : Value := .pair (.heap 0) (.credit (.stack 9 1)) .unit
def fieldType : GroundTy := .prod (.credit Mode.aliased) (.unit Mode.identity) Mode.identity
#guard firstOrderSupport 20 aliasedField fieldType = some [.heap 0]
#guard firstOrderSupport 20 aliasedField
  (.prod (.credit Mode.identity) (.unit Mode.identity) Mode.identity) = some [.heap 0,.stack 9 1]
#guard firstOrderSupport 20 (.inl aliasedField)
  (.sum fieldType (.unit Mode.identity) Mode.aliased) = some []
def referenceLocations : Nat → Value → List Location
  | 0, _ => []
  | _+1, .unit => []
  | _+1, .credit l => [l]
  | n+1, .pair l a b => l :: (referenceLocations n a ++ referenceLocations n b)
  | n+1, .inl a | n+1, .inr a => referenceLocations n a
  | n+1, .closure γ _ _ => γ.flatMap (referenceLocations n)
#guard (referenceLocations 20 aliasedField).contains (.stack 9 1)
#guard !(referenceLocations 20 aliasedField).all fun l => match l with
  | .heap _ => true | .stack f _ => f == 0
-- Capture selection follows syntax, not a possibly misleading annotation.
#guard match evalFuel 10 initialSupplies [.credit (.stack 9 1)] (.lam [] .unit) with
  | .success (.closure γ _ _) => (γ.flatMap (referenceLocations 10)).isEmpty
  | _ => false
#guard match evalFuel 10 initialSupplies [.credit (.stack 9 1)] (.lam [] (.var 1)) with
  | .success (.closure γ _ _) => (γ.flatMap (referenceLocations 10)).contains (.stack 9 1)
  | _ => false

-- Cycles, equality bookkeeping, occurs checks, fixed skolems and residual WF.
def x : ModExpr := .var (.flex 0)
def y : ModExpr := .var (.flex 1)
#guard (solve 1000 [.mode x y, .mode y x]).isSuccess
-- A modal self-equality has an absorbing-unit solution for every concrete mode.
#guard Mode.all.all fun m =>
  (solve 500 [.equal (.flex 0) (.modal (.var (.flex 0)) (.const m))]).isSuccess
#guard rejected (solve 500 [.equal (.flex 0) (.modal (.var (.flex 0)) badArgument)])
#guard rejected (solve 500 [.equal (.flex 0) (.fn (.var (.flex 0)) .unit)])
#guard rejected (solve 500 [.equal (.flex 0)
  (.modal (.fn (.var (.flex 0)) .unit) (.const Mode.bottom))])
#guard rejected (solve 500 [.sub (.var (.flex 0)) (.fn (.var (.flex 0)) .unit)])
#guard rejected (solve 500 [.equal (.rigid 0) .unit])
#guard rejected (solve 500 [.equal (.flex 0) .unit, .equal (.flex 0) .credit])
#guard match solve 500 [.equal (.flex 0) (.var (.flex 1)), .equal (.flex 1) .unit] with
  | .success s => s.substitution.ty (.var (.flex 0)) == .unit
  | _ => false
#guard rejected (solve 500 [.sub (.modal (.var (.flex 0))
  (.leftResidual (.const Mode.identity) (.const Mode.bottom))) (.var (.flex 1))])
#guard exhausted (solve 0 [])
#guard (solve 100 []).isSuccess

-- Schemes: body-only quantifiers, signature assumptions, functions' irrelevant past.
def polyId : Scheme := .generalize [] (.fn (.var (.flex 0)) (.var (.flex 0)))
def bounded : Scheme := {
  typeParams := [0,1]
  bounds := [.sub (.var (.flex 0)) (.var (.flex 1))]
  body := .fn (.var (.flex 0)) (.var (.flex 1))}
#guard (checkSubsumption 20000 polyId polyId).isSuccess
#guard (checkSubsumption 20000 polyId (.mono (.fn .unit .unit))).isSuccess
#guard rejected (checkSubsumption 20000 (.mono (.fn .unit .unit)) polyId)
#guard (checkSubsumption 20000 bounded bounded).isSuccess
#guard rejected (checkSubsumption 20000 bounded {bounded with bounds := []})
def localSignature : Scheme := {
  modParams := [0]
  bounds := [.mode (.const Mode.localLower) x]
  body := .modal .credit x}
#guard (checkSubsumption 20000 (.mono (.modal .credit .epsilon)) localSignature).isSuccess
#guard rejected (checkSubsumption 20000 (.mono (.modal .credit .epsilon))
  {localSignature with bounds := []})
#guard (checkSubsumption 20000 (.mono (.modal (.fn .unit .unit) (.const Mode.aliased)))
  (.mono (.modal (.fn .unit .unit) .epsilon))).isSuccess
#guard rejected (checkSubsumption 20000 (.mono (.modal .credit (.const Mode.aliased)))
  (.mono (.modal .credit .epsilon)))
#guard exhausted (checkSubsumption 0 polyId polyId)

-- Compare the verified backend with exhaustive valuations of two complete modes.
def boolValuation (a b : Mode) (i : Nat) : Bool :=
  let m := if i / 6 == 0 then a else b
  match i % 3 with | 0 => m.isLocal | 1 => m.once | _ => m.unique
def exhaustive (e : BoolExpr) : Bool := Mode.all.all fun a => Mode.all.all fun b => e.eval (boolValuation a b)
def backendAgrees (e : BoolExpr) : Bool := match ConcreteBackend.decideFormula 20000 e with
  | .success r => r.valid == exhaustive e
  | _ => false
def queries : List BoolExpr :=
  [modeFormula x y, modeFormula y x,
   .imp (modeFormula x y) (modeFormula (.compose x y) y),
   .imp (modeFormula x y) (modeFormula (.close y) (.close x)),
   .imp (modeFormula x y) (modeFormula y x),
   modeFormula (.leftResidual x y) y,
   modeFormula x (.rightResidual y x),
   .equal (modeFormula (.close x) y) (modeFormula (.closeInv y) x),
   .equal (modeFormula x (.compose y x)) (modeFormula (.leftResidual x x) y)]
#guard queries.all backendAgrees
#guard Mode.all.all fun a => Mode.all.all fun b =>
  backendAgrees (modeFormula (.const a) (.const b))
#guard ((ConcreteBackend.atomFin [7,100,42] 100).map Fin.val) = some 1
#guard (ConcreteBackend.atomFin [7,100,42] 9).isNone
#guard [.const true, .const false, .atom 42, .imp (.atom 42) (.atom 42)].all backendAgrees
-- A false validity accumulator still visits subsequent clauses and reports missing atoms.
#guard rejected (ConcreteBackend.decideClauses [] [[], [(42, true)]] true)

-- Indirect cycles must reject rather than expand an unbounded sequence of shapes.
#guard rejected (solve 500 [.sub (.var (.flex 0)) (.var (.flex 1)),
  .sub (.var (.flex 1)) (.fn (.var (.flex 0)) .unit)])
-- Supplied worklist states must also validate their accumulated substitution.
#guard rejected (runSolver 100
  { pending := [.sub (.var (.flex 0)) (.var (.flex 1))]
    substitution := { types := [(0, .fn (.var (.flex 0)) .unit)] }, nextType := 2 })
#guard rejected (runSolver 100
  { pending := [.mode (.var (.flex 0)) (.var (.flex 1))]
    substitution := { modes := [(0, .compose (.var (.flex 0)) (.const Mode.many))] }, nextMode := 2 })
#guard Mode.all.all fun a => Mode.all.all fun b =>
  match solve 500 [.mode (.const a) x, .mode x (.const b)] with
  | .success _ => Mode.le a b
  | .rejected _ => !Mode.le a b
  | .exhausted => false

-- Solving an equality must retain the definedness of its substituted type image.
def undefinedType : Ty := .modal .unit
  (.leftResidual (.const Mode.top) (.const Mode.bottom))
#guard rejected (solve 500 [.equal (.flex 0) undefinedType])
#guard rejected (solve 500 [.sub undefinedType undefinedType])
#guard rejected (solve 500 [.equiv undefinedType undefinedType])
#guard rejected (solve 500 [.equal (.flex 0) (.fn .unit undefinedType)])
#guard (solve 500 [.equal (.flex 0) (.fn .unit (.modal .unit .epsilon))]).isSuccess
-- Returned types require definedness even without application or elimination.
#guard rejected (infer 500 [some (Scheme.mono (.fn undefinedType .unit))] (.var 0))
#guard rejected (infer 500 [some (Scheme.mono (.sum .unit undefinedType))] (.var 0))

end ModalityInference.Regression
