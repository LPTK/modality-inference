import ModalityInference.SchemePreparation
import ModalityInference.ModeBackend

/-! A positive syntactic certificate for exact body instances. Only fresh source
binders may be replaced; type and modality images are retained verbatim, including
partial expressions. Written source bounds retain all their guards. A missing
certificate leaves the general symbolic comparison available. -/
namespace ModalityInference.ComparisonInstance

abbrev Prepared := SchemePreparation.Prepared

def typeAllowed (p : Prepared) : TypeVar → Bool
  | .flex n => p.firstType ≤ n && n < p.nextType
  | .rigid _ => false

def modeAllowed (p : Prepared) : ModVar → Bool
  | .flex n => p.firstMode ≤ n && n < p.nextMode
  | .rigid _ => false

def bindType (name : Nat) (image : Ty) (action : Substitution) : Option Substitution :=
  match action.types.lookup name with
  | none => some { action with types := (name, image) :: action.types }
  | some previous => if previous == image then some action else none

def bindMode (name : Nat) (image : ModExpr) (action : Substitution) : Option Substitution :=
  match action.modes.lookup name with
  | none => some { action with modes := (name, image) :: action.modes }
  | some previous => if previous == image then some action else none

def matchMode (p : Prepared) : ModExpr → ModExpr → Substitution → Option Substitution
  | .var (.flex n), target, action =>
      if modeAllowed p (.flex n) then bindMode n target action
      else if target == .var (.flex n) then some action else none
  | .var (.rigid n), .var (.rigid k), action => if n == k then some action else none
  | .const a, .const b, action => if a == b then some action else none
  | .compose a b, .compose c d, action
  | .meet a b, .meet c d, action
  | .join a b, .join c d, action
  | .leftResidual a b, .leftResidual c d, action
  | .rightResidual a b, .rightResidual c d, action => do
      let action ← matchMode p a c action
      matchMode p b d action
  | .close a, .close b, action
  | .closeInv a, .closeInv b, action
  | .future a, .future b, action
  | .capture a, .capture b, action => matchMode p a b action
  | _, _, _ => none

def matchType (p : Prepared) : Ty → Ty → Substitution → Option Substitution
  | .var (.flex n), target, action =>
      if typeAllowed p (.flex n) then bindType n target action
      else if target == .var (.flex n) then some action else none
  | .var (.rigid n), .var (.rigid k), action => if n == k then some action else none
  | .unit, .unit, action | .credit, .credit, action => some action
  | .prod a b, .prod c d, action
  | .sum a b, .sum c d, action
  | .fn a b, .fn c d, action => do
      let action ← matchType p a c action
      matchType p b d action
  | .modal a m, .modal b n, action => do
      let action ← matchType p a b action
      matchMode p m n action
  | _, _, _ => none

/-- Source binders cannot occur in a fixed target image. This also prevents
cycles when the matcher is called on an arbitrary `Prepared` record. -/
def targetFresh (p : Prepared) : Bool :=
  p.targetType.typeVariables.all (fun v => !typeAllowed p v) &&
    p.targetType.modeVariables.all (fun v => !modeAllowed p v)

/-- Fill unused binders and discard all keys outside the exact fresh domains. -/
def complete (p : Prepared) (action : Substitution) : Substitution :=
  { types := (List.range' p.firstType (p.nextType - p.firstType)).map
      (fun n => (n, (action.types.lookup n).getD .unit))
    modes := (List.range' p.firstMode (p.nextMode - p.firstMode)).map
      (fun n => (n, (action.modes.lookup n).getD .epsilon)) }

def candidate (p : Prepared) : Option Substitution := do
  if !targetFresh p then none else do
    let matched ← matchType p p.sourceType p.targetType {}
    let action := complete p matched
    if action.ty p.sourceType == p.targetType then some action else none

/-- Expanded bounds contain only subtype, mode, and definedness constraints.
Type comparisons are discharged only by reflexivity or a literal declaration. -/
def structural (assumptions : Bounds) : Constraint → Bool
  | .sub a b => a == b || assumptions.contains (.sub a b)
  | .mode _ _ | .defined _ => true
  | .equal _ _ | .equiv _ _ => false

structure Result where
  action : Substitution
  query : BoolExpr
  backend : ConcreteBackend.Report
  deriving Repr

/-- Preserve exhaustion once a syntactic candidate applies. A caller may select
another comparison path only after this attempt returns `success none`. -/
def attempt (fuel : Nat) (p : Prepared) : RunResult (Option Result) :=
  match candidate p with
  | none => .success none
  | some action =>
    let obligations := (action.bounds p.sourceBounds).assumptions
    if !obligations.all (structural p.assumptions) then .success none else do
      let query := BoolExpr.imp (boundsModeFormula p.assumptions) (boundsModeFormula obligations)
      let backend ← ConcreteBackend.decideFormula fuel query
      return if backend.valid then some ⟨action, query, backend⟩ else none

/-- Compatibility view of the positive certificate; control-flow decisions
between algorithms should use `attempt` so exhaustion remains visible. -/
def run (fuel : Nat) (p : Prepared) : Option Result :=
  match attempt fuel p with
  | .success result => result
  | .rejected _ | .exhausted => none

end ModalityInference.ComparisonInstance
