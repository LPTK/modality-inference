import ModalityInference.ModeConsistency
import ModalityInference.Declarative
import ModalityInference.Core.Scoping

namespace ModalityInference

namespace ModExpr
/-- Constant folding preserves undefined residuals rather than assigning them a default. -/
def foldConstants (r : ModExpr) : ModExpr :=
  match r.eval (fun _ => none) with
  | some m => .const m
  | none => match r with
    | .compose (.const a) b => if a == Mode.identity then b else r
    | .compose a (.const b) => if b == Mode.identity then a else r
    | .compose a b | .meet a b | .join a b => if a == b then a else r
    | _ => r

def normalize : ModExpr → ModExpr
  | .const m => .const m
  | .var v => .var v
  | .compose a b => foldConstants (.compose a.normalize b.normalize)
  | .meet a b => foldConstants (.meet a.normalize b.normalize)
  | .join a b => foldConstants (.join a.normalize b.normalize)
  | .leftResidual a b => foldConstants (.leftResidual a.normalize b.normalize)
  | .rightResidual a b => foldConstants (.rightResidual a.normalize b.normalize)
  | .close a => foldConstants (.close a.normalize)
  | .closeInv a => foldConstants (.closeInv a.normalize)
  | .future a => foldConstants (.future a.normalize)
  | .capture a => foldConstants (.capture a.normalize)
end ModExpr

def TypeExpr.normalize : Ty → Ty
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod a.normalize b.normalize
  | .sum a b => .sum a.normalize b.normalize
  | .fn a b => .fn a.normalize b.normalize
  | .modal a m =>
    let n := m.normalize
    match a.normalize with
    | .modal b k => .modal b (ModExpr.compose k n).normalize
    | b => if n == .epsilon then b else .modal b n

def Constraint.normalize : Constraint → Constraint
  | .sub a b => .sub a.normalize b.normalize
  | .mode a b => .mode a.normalize b.normalize
  | .defined a => .defined a.normalize
  | .equal v t => .equal v t.normalize
  | .equiv a b => .equiv a.normalize b.normalize

inductive RewriteRule where
  | hypothesis | variableBound | expand | compose | unit | credit | prod | sum | fn
  | substitute | sub1 | sub2 | imp1 | imp2 | left1 | left2 | right1 | right2
  | andOr | close | modeBound | constant | defined | projection
  deriving Repr, DecidableEq, BEq

structure SolverState where
  pending : Bounds
  bounds : Bounds := []
  substitution : Substitution := {}
  seen : Bounds := []
  nextType : Nat := 0
  nextMode : Nat := 0
  trace : List RewriteRule := []
  deriving Repr

namespace SolverState
def emit (s : SolverState) (rule : RewriteRule) (cs : Bounds) : SolverState :=
  { s with pending := cs ++ s.pending, trace := rule :: s.trace }
def retain (s : SolverState) (rule : RewriteRule) (c : Constraint) : SolverState :=
  { s with bounds := if s.bounds.contains c then s.bounds else c :: s.bounds
           trace := rule :: s.trace }
def freshType (s : SolverState) : Ty × SolverState :=
  (.var (.flex s.nextType), { s with nextType := s.nextType + 1 })
def freshMode (s : SolverState) : ModExpr × SolverState :=
  (.var (.flex s.nextMode), { s with nextMode := s.nextMode + 1 })
/-- A shallow shape expansion; the original constraint is reprocessed after substitution. -/
def skeleton (s : SolverState) (t : Ty) : Ty × SolverState :=
  let (m, s) := s.freshMode
  match t with
  | .prod _ _ | .sum _ _ | .fn _ _ =>
    let (a, s) := s.freshType
    let (b, s) := s.freshType
    let body := match t with
      | .prod _ _ => TypeExpr.prod a b
      | .sum _ _ => .sum a b
      | _ => .fn a b
    (.modal body m, s)
  | t => (.modal t m, s)
end SolverState

/-- Retain the bound for finite modality checking. Re-enqueuing transitive
consequences can grow residual syntax without bound, even for satisfiable inputs;
those consequences are already implied by the retained premises. -/
def recordModeBound (s : SolverState) (a b : ModExpr) : SolverState :=
  s.retain .modeBound (.mode a b)

/-- Orient residual rewrites toward the least flexible variable. Deferred projection
constraints are retained verbatim and checked in the finite modality algebra. -/
def stepMode (s : SolverState) (a b : ModExpr) : RunResult SolverState := do
  let guard := [Constraint.defined a, Constraint.defined b]
  if a.freeVariables.isEmpty && b.freeVariables.isEmpty then
    if checkModeConstraint (fun _ => none) (.mode a b) then return s.emit .constant []
    else return ← .rejected "false or undefined concrete modality inequality"
  if a == b then return s.emit .hypothesis guard
  match a, b with
  | .join x y, _ => return s.emit .andOr [.mode x b, .mode y b]
  | _, .meet x y => return s.emit .andOr [.mode a x, .mode a y]
  | .var _, _ | _, .var _ => return (recordModeBound s a b).emit .defined guard
  | .leftResidual x y, _ =>
    if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar b.minVar then
      return s.emit .sub1 (guard ++ [.mode x (.compose y b)])
    -- A tie with the right operand would permit two swaps followed by duplicate
    -- discharge of an unresolved inequality. Keep that constraint for projection.
    else if ModExpr.minimumLE y.minVar x.minVar && y.minVar != x.minVar &&
        ModExpr.minimumLE y.minVar b.minVar && y.minVar != b.minVar then
      return s.emit .sub2 (guard ++ [.mode (.leftResidual x b) y])
    else return s.retain .projection (.mode a b)
  | _, .rightResidual x y =>
    if ModExpr.minimumLE y.minVar x.minVar &&
        ModExpr.minimumLE y.minVar a.minVar && y.minVar != a.minVar then
      return s.emit .imp1 (guard ++ [.mode (.compose a x) y])
    else if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar a.minVar &&
        x.minVar != y.minVar && x.minVar != a.minVar then
      return s.emit .imp2 (guard ++ [.mode x (.rightResidual a y)])
    else return s.retain .projection (.mode a b)
  | .compose x y, _ =>
    if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar b.minVar then
      return s.emit .left1 (guard ++ [.mode x (.rightResidual y b)])
    else if ModExpr.minimumLE y.minVar x.minVar && y.minVar != x.minVar &&
        ModExpr.minimumLE y.minVar b.minVar then
      return s.emit .left2 (guard ++ [.mode y (.rightResidual x b)])
    else return s.retain .projection (.mode a b)
  | _, .compose x y =>
    if ModExpr.minimumLE x.minVar y.minVar && ModExpr.minimumLE x.minVar a.minVar &&
        x.minVar != a.minVar then
      return s.emit .right1 (guard ++ [.mode (.leftResidual a y) x])
    else if ModExpr.minimumLE y.minVar x.minVar && ModExpr.minimumLE y.minVar a.minVar &&
        y.minVar != x.minVar && y.minVar != a.minVar then
      return s.emit .right2 (guard ++ [.mode (.leftResidual a x) y])
    else return s.retain .projection (.mode a b)
  | .close x, _ =>
    if ModExpr.minimumLE x.minVar b.minVar && x.minVar != b.minVar then
      return s.emit .close (guard ++ [.mode (.closeInv b) x])
    else return s.retain .projection (.mode a b)
  | _, _ => return s.retain .projection (.mode a b)

def stepType (s : SolverState) (left right : Ty) : RunResult SolverState := do
  let (a, l) := left.outer
  let (b, r) := right.outer
  let l := l.normalize
  let r := r.normalize
  let original := Constraint.sub (.modal a l) (.modal b r)
  match a, b with
  | .var _, .var _ => return (s.retain .variableBound original).emit .defined [.defined l, .defined r]
  | .var (.flex n), _ =>
    if b.typeVariables.contains (.flex n) then return ← .rejected "occurs check failed in type bound"
    let (t, s) := s.skeleton b
    return s.emit .expand [.equal (.flex n) t, original]
  | _, .var (.flex n) =>
    if a.typeVariables.contains (.flex n) then return ← .rejected "occurs check failed in type bound"
    let (t, s) := s.skeleton a
    return s.emit .expand [.equal (.flex n) t, original]
  | .unit, .unit => return s.emit .unit [.mode l r]
  | .credit, .credit => return s.emit .credit [.mode l r]
  | .prod a₁ a₂, .prod b₁ b₂ =>
    return s.emit .prod [.sub (.modal a₁ l) (.modal b₁ r), .sub (.modal a₂ l) (.modal b₂ r), .mode l r]
  | .sum a₁ a₂, .sum b₁ b₂ =>
    return s.emit .sum [.sub (.modal a₁ l) (.modal b₁ r), .sub (.modal a₂ l) (.modal b₂ r), .mode l r]
  | .fn a₁ a₂, .fn b₁ b₂ => return s.emit .fn [.sub b₁ a₁, .sub a₂ b₂, .mode l (.compose r .top)]
  | _, _ => .rejected "incompatible type shapes (or a rigid variable would need instantiation)"

def solverStep (s : SolverState) : RunResult SolverState := do
  match s.pending with
  | [] => return s
  | c :: rest =>
    let c := (s.substitution.constraint c).normalize
    let s := { s with pending := rest }
    if s.seen.contains c then return s.emit .hypothesis []
    let s := { s with seen := c :: s.seen }
    match c with
    | .equiv a b => return s.emit .substitute [.sub a b, .sub b a]
    | .sub a b => stepType s a b
    | .mode a b => stepMode s a b
    | .defined a =>
      if a.freeVariables.isEmpty then
        if (a.eval (fun _ => none)).isSome then return s.emit .defined []
        else return ← .rejected "undefined modality residual"
      else return s.retain .defined c
    | .equal v t => match v with
      | .rigid _ => if t == .var v then return s else .rejected "cannot substitute a skolem"
      | .flex n =>
        if t == .var v then return s
        -- Modal self-equalities can have finite solutions. Preserve their two
        -- subtype obligations; the entry shape check rejects structural cycles.
        if t.typeVariables.contains v then
          return s.emit .substitute [.sub (.var v) t, .sub t (.var v)]
        let one : Substitution := { types := [(n, t)] }
        return { s with pending := one.bounds (s.pending ++ s.bounds ++ t.wellFormedBounds)
                        bounds := [], seen := []
                        substitution := s.substitution.extendType n t
                        trace := .substitute :: s.trace }

/-- Subtyping preserves finite constructor shape. This separate unification check
catches indirect cycles (α ≤ β, β ≤ α → unit) before shallow expansion can keep
creating fresh variables. Its temporary variable identifications are *not* used
as the principal type substitution: modality-bearing bounds remain independent. -/
def TypeExpr.eraseModes : Ty → Ty
  | .var v => .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod a.eraseModes b.eraseModes
  | .sum a b => .sum a.eraseModes b.eraseModes
  | .fn a b => .fn a.eraseModes b.eraseModes
  | .modal a _ => a.eraseModes

def checkShapePairs : Nat → List (Ty × Ty) → RunResult Unit
  | 0, _ => .exhausted
  | _+1, [] => .success ()
  | fuel+1, (a,b)::rest =>
    if a == b then checkShapePairs fuel rest
    else match a,b with
    | .var v,t | t,.var v =>
      if t.typeVariables.contains v then .rejected "occurs check failed through type-bound cycle"
      else
        let replace := fun w => if w == v then t else TypeExpr.var w
        checkShapePairs fuel (rest.map fun (x,y) =>
          (x.subst replace ModExpr.var, y.subst replace ModExpr.var))
    | .prod a b,.prod c d | .sum a b,.sum c d | .fn a b,.fn c d =>
      checkShapePairs fuel ((a,c)::(b,d)::rest)
    | _,_ => .rejected "incompatible finite type shapes"

def checkShapes (fuel : Nat) (cs : Bounds) : RunResult Unit :=
  checkShapePairs fuel (cs.filterMap fun c => match c with
    | .sub a b | .equiv a b => some (a.eraseModes,b.eraseModes)
    | .equal v t => some (.var v,t.eraseModes)
    | _ => none)

def runWorklist : Nat → SolverState → RunResult SolverState
  | 0, _ => .exhausted
  | fuel + 1, s => if s.pending.isEmpty then .success s else do
      let next ← solverStep s
      runWorklist fuel next

def runSolver (fuel : Nat) (s : SolverState) : RunResult SolverState := do
  if !s.substitution.checkAcyclic then
    return ← .rejected "initial solver substitution is cyclic, duplicated, or not normalized"
  -- The pending syntax may still mention variables in the accumulated substitution.
  -- Check the shapes that the worklist will actually process.
  checkShapes fuel (s.substitution.bounds (s.pending ++ s.bounds))
  runWorklist fuel s

structure Solved where
  substitution : Substitution
  bounds : Bounds
  witness : ModeAssignment
  nextType : Nat
  nextMode : Nat
  trace : List RewriteRule
  deriving Repr

def solveFrom (fuel nextType nextMode : Nat) (cs : Bounds) : RunResult Solved := do
  let s ← runSolver fuel { pending := cs, nextType := nextType, nextMode := nextMode }
  let witness ← satisfiableModes fuel s.bounds
  return ⟨s.substitution, s.bounds, witness, s.nextType, s.nextMode, s.trace.reverse⟩

def solve (fuel : Nat) (cs : Bounds) : RunResult Solved :=
  let nt := cs.typeVariables.foldl (fun n v => max n (v.index + 1)) 0
  let nm := cs.modeVariables.foldl (fun n v => max n (v.index + 1)) 0
  solveFrom fuel nt nm cs

/-- Solution semantics is declarative and independent of `solve`. -/
def Solution (cs Δ : Bounds) (σ : Substitution) : Prop := EntailsAll Δ (σ.bounds cs)

/-- Local rewriting specifications, independent of the worklist implementation.
Definedness guards are part of residual rewrites, including both original operands.
These constructors describe the transformations; theorem files state their correctness. -/
inductive ConstraintReduction : Bounds → Bounds → Prop where
  | pair {a b c d l r} : ConstraintReduction
      [.sub (.modal (.prod a b) l) (.modal (.prod c d) r)]
      [.sub (.modal a l) (.modal c r), .sub (.modal b l) (.modal d r), .mode l r]
  | sum {a b c d l r} : ConstraintReduction
      [.sub (.modal (.sum a b) l) (.modal (.sum c d) r)]
      [.sub (.modal a l) (.modal c r), .sub (.modal b l) (.modal d r), .mode l r]
  | fn {a b c d l r} : ConstraintReduction
      [.sub (.modal (.fn a b) l) (.modal (.fn c d) r)]
      [.sub c a, .sub b d, .mode l (.compose r .top)]
  | unit {l r} : ConstraintReduction [.sub (.modal .unit l) (.modal .unit r)] [.mode l r]
  | credit {l r} : ConstraintReduction [.sub (.modal .credit l) (.modal .credit r)] [.mode l r]
  | join {a b c} : ConstraintReduction [.mode (.join a b) c] [.mode a c, .mode b c]
  | meet {a b c} : ConstraintReduction [.mode a (.meet b c)] [.mode a b, .mode a c]
  | sub {a b c} : ConstraintReduction [.mode (.leftResidual a b) c]
      [.defined (.leftResidual a b), .defined c, .mode a (.compose b c)]
  | imp {a b c} : ConstraintReduction [.mode a (.rightResidual b c)]
      [.defined a, .defined (.rightResidual b c), .mode (.compose a b) c]
  | left {a b c} : ConstraintReduction [.mode (.compose a b) c]
      [.defined (.compose a b), .defined c, .mode a (.rightResidual b c)]
  | right {a b c} : ConstraintReduction [.mode a (.compose b c)]
      [.defined a, .defined (.compose b c), .mode (.leftResidual a c) b]
  | close {a b} : ConstraintReduction [.mode (.close a) b]
      [.defined (.close a), .defined b, .mode (.closeInv b) a]
  | context {xs ys before after} : ConstraintReduction xs ys →
      ConstraintReduction (before ++ xs ++ after) (before ++ ys ++ after)

end ModalityInference
