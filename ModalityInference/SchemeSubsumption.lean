import ModalityInference.Constraints
import ModalityInference.SchemeModeSynthesis

namespace ModalityInference
namespace BoolExpr
/-- Smart Boolean constructors keep finite graph closure and quantifier elimination small. -/
def conj (a b : BoolExpr) : BoolExpr := match a,b with
  | .const false, _ | _, .const false => .const false
  | .const true, b => b
  | a, .const true => a
  | a,b => if a == b then a else .and a b
def disj (a b : BoolExpr) : BoolExpr := match a,b with
  | .const true, _ | _, .const true => .const true
  | .const false, b => b
  | a, .const false => a
  | a,b => if a == b then a else .or a b
def implies (a b : BoolExpr) : BoolExpr := match a,b with
  | .const false, _ | _, .const true => .const true
  | .const true, b => b
  | a,b => if a == b then .const true else .imp a b
def simplify : BoolExpr → BoolExpr
  | .const b => .const b
  | .atom i => .atom i
  | .and a b => conj a.simplify b.simplify
  | .or a b => disj a.simplify b.simplify
  | .imp a b => implies a.simplify b.simplify
end BoolExpr

abbrev RigidNode := TypeVar × Mode

def sameMode (a b : ModExpr) : BoolExpr :=
  BoolExpr.conj (modeFormula a b).simplify (modeFormula b a).simplify

/-- A declared type-bound edge, closed under applying the same modality on both
sides. All eight concrete modalities are needed, including past variance. -/
def assumptionEdge (assumptions : Bounds) (x y : RigidNode) : BoolExpr :=
  assumptions.foldl (fun out c => match c with
    | .sub a b => match a.outer, b.outer with
      | (.var v,l), (.var w,r) =>
        if v == x.1 && w == y.1 then
          Mode.all.foldl (fun out k => BoolExpr.disj out
            (BoolExpr.conj (sameMode (.compose l (.const k)) (.const x.2))
              (sameMode (.compose r (.const k)) (.const y.2)))) out
        else out
      | _,_ => out
    | _ => out) (.const false)

/-- Floyd--Warshall over Boolean formulas, with a fixed node order. This is a
finite proof search for reflexivity, submoding, congruence, bounds and transitivity. -/
def rigidClosure (fuel : Nat) (assumptions : Bounds) (vars : List TypeVar) :
    RunResult (List RigidNode × Array (Array BoolExpr)) := do
  let nodes := vars.flatMap fun v => Mode.all.map (v, ·)
  if nodes.length ^ 3 > fuel then return ← .exhausted
  let mut matrix := (nodes.map fun x => (nodes.map fun y =>
    BoolExpr.disj (.const (x.1 == y.1 && Mode.le x.2 y.2))
      (assumptionEdge assumptions x y)).toArray).toArray
  for k in [:nodes.length] do
    let old := matrix
    matrix := old.mapIdx fun i row => row.mapIdx fun j edge =>
      BoolExpr.disj edge (BoolExpr.conj ((old[i]?.getD #[])[k]?.getD (.const false))
        ((old[k]?.getD #[])[j]?.getD (.const false)))
  return (nodes,matrix)

def rigidGoal (nodes : List RigidNode) (matrix : Array (Array BoolExpr))
    (v : TypeVar) (l : ModExpr) (w : TypeVar) (r : ModExpr) : BoolExpr :=
  (nodes.zipIdx).foldl (fun out (x,i) => if x.1 == v then
    (nodes.zipIdx).foldl (fun out (y,j) => if y.1 == w then
      BoolExpr.disj out (BoolExpr.conj (sameMode l (.const x.2))
        (BoolExpr.conj (sameMode r (.const y.2))
          ((matrix[i]?.getD #[])[j]?.getD (.const false)))) else out) out
    else out) (.const false)

/-- Projection queries retain rigid type assumptions; they are not silently erased
when the modality fragment is sent to `Equation.decide`. -/
def residualFormula (fuel : Nat) (assumptions goals : Bounds) : RunResult BoolExpr := do
  let vars := (assumptions.typeVariables ++ goals.typeVariables).dedup
  let (nodes, matrix) ← rigidClosure fuel assumptions vars
  let mut query := BoolExpr.const true
  for c in goals do
    let q ← match c with
      | .mode a b => .success (modeFormula a b).simplify
      | .defined a => .success a.project.defined.simplify
      | .sub a b => match a.outer,b.outer with
        | (.var v,l), (.var w,r) => .success (rigidGoal nodes matrix v l w r)
        | _,_ => .rejected "non-residual type constraint after normalization"
      | .equal _ _ | .equiv _ _ => .rejected "unprocessed type equality"
    query := BoolExpr.conj query q
  return query

structure SubsumptionEvidence where
  /-- Structural images after applying the reconstructed symbolic modalities. -/
  substitution : Substitution
  assumptions : Bounds
  obligations : Bounds
  flexibleAtoms : List Nat
  query : BoolExpr
  backend : ConcreteBackend.Report
  deriving Repr

/-- Search state for the finitely many base-type representatives of a residual
flexible type variable. Modes on these representatives are freshly flexible. -/
structure SubsumptionCandidate where
  state : SolverState
  remaining : List Nat
  deriving Repr

/-- Search alternatives in identifier order. An exhausted alternative prevents a
negative answer, even if all other explored alternatives reject. -/
def checkCandidates (normalizationFuel firstFlexibleMode : Nat) (assumptions : Bounds)
    (rigids : List TypeVar) : Nat → List SubsumptionCandidate → Bool → RunResult SubsumptionEvidence
  | 0, _, _ => .exhausted
  | _ + 1, [], exhausted => if exhausted then .exhausted else .rejected "scheme is not subsumed under the declared assumptions"
  | fuel + 1, candidate :: todo, exhausted =>
    match candidate.remaining with
    | v :: vs =>
      let m := ModExpr.var (.flex candidate.state.nextMode)
      let choices := rigids.map TypeExpr.var ++ [TypeExpr.unit]
      let alternatives := choices.map fun t =>
        {state := {candidate.state with
          pending := [.equal (.flex v) (.modal t m)] ++ candidate.state.pending
          nextMode := candidate.state.nextMode + 1}
         remaining := vs : SubsumptionCandidate}
      checkCandidates normalizationFuel firstFlexibleMode assumptions rigids fuel (alternatives ++ todo) exhausted
    | [] =>
      match runSolver normalizationFuel candidate.state with
      | .exhausted => checkCandidates normalizationFuel firstFlexibleMode assumptions rigids fuel todo true
      | .rejected _ => checkCandidates normalizationFuel firstFlexibleMode assumptions rigids fuel todo exhausted
      | .success s =>
        let attempt := do
          let q ← residualFormula normalizationFuel assumptions s.bounds
          -- Eliminate all coordinates of fresh parameters, including coordinates
          -- absent from the query, so reconstructed images contain no fresh names.
          let modeIds := List.range' firstFlexibleMode (s.nextMode - firstFlexibleMode)
          let original := BoolExpr.implies (boundsModeFormula assumptions).simplify q
          let modes ← SchemeModeSynthesis.run normalizationFuel modeIds original
          let report ← ConcreteBackend.decideFormula normalizationFuel modes.query
          if report.valid then
            return ({
              substitution := modes.substitution.compose s.substitution
              assumptions := assumptions
              obligations := modes.substitution.bounds s.bounds
              flexibleAtoms := modes.flexibleAtoms
              query := modes.query
              backend := report} : SubsumptionEvidence)
          else .rejected "modality or rigid type-bound entailment failed"
        match attempt with
        | .success evidence => .success evidence
        | .exhausted => checkCandidates normalizationFuel firstFlexibleMode assumptions rigids fuel todo true
        | .rejected _ => checkCandidates normalizationFuel firstFlexibleMode assumptions rigids fuel todo exhausted

/-- Both schemes are freshly instantiated, but every declared quantifier becomes
rigid. In particular, quantifiers mentioned only by the body are skolemized too.
The returned evidence is executable certificate data, not a metatheorem. -/
def checkSubsumption (fuel : Nat) (inferred declared : Scheme) : RunResult SubsumptionEvidence := do
  let nt := max inferred.freshTypeIndex declared.freshTypeIndex
  let nm := max inferred.freshModeIndex declared.freshModeIndex
  let (assumptions, target) := declared.instantiate nt nm true
  let ft := nt + declared.typeParams.length
  let fm := nm + declared.modParams.length
  let (cs, source) := inferred.instantiate ft fm
  let s ← runSolver fuel {
    pending := cs ++ [.sub source target]
    nextType := ft + inferred.typeParams.length
    nextMode := fm + inferred.modParams.length}
  let flex := (s.bounds.typeVariables.filterMap fun v => match v with
    | .flex n => if n >= ft then some n else none
    | _ => none).mergeSort (· ≤ ·)
  let rigids := (assumptions.typeVariables ++ target.typeVariables ++ s.bounds.typeVariables).dedup.filter
    fun v => match v with | .rigid _ => true | .flex n => n < ft
  checkCandidates fuel fm assumptions rigids fuel [⟨s,flex⟩] false

end ModalityInference
