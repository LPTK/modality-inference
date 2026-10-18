import ModalityInference.ComparisonGuardedEndpointQueries
import ModalityInference.ComparisonSignedBranchCalls
import ModalityInference.ComparisonSignedPreparation
import ModalityInference.ComparisonSelectedPlan
import ModalityInference.ComparisonStructuralCoherence
import ModalityInference.ComparisonLayoutWorlds

/-! Each required endpoint pair selects a compatible structural query. Shape
choices are shared constants, and all active queries retain the original
declared-edge theory. No required endpoint or guard is added to that theory. -/
namespace ModalityInference.ComparisonPreparedQueries

structure Alternative where
  activation : Nat
  branch : ComparisonSelectedBases.Branch
  endpoint : Ty × Ty
  layout : ComparisonStructuralLayout.Layout
  theory : CNF
  original : List ComparisonSignedEndpoints.CompiledClause
  clauses : List ComparisonSignedEndpoints.CompiledClause

def Alternative.source (a : Alternative) : ComparisonGuardedEndpointQueries.Source :=
  ⟨[(a.activation,false)],⟨ComparisonLayoutWorlds.decode,a.theory,a.clauses⟩⟩

def Alternative.condition (a : Alternative) : BoolExpr :=
  .imp (.atom a.activation) a.branch.guard

def branches (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (endpoint : Ty × Ty) :
    List ComparisonSelectedBases.Branch :=
  ComparisonSelectedBases.bases (ComparisonSelectedBases.layout first p solved)
    (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
    solved.fixedShapes ((ComparisonShape.ofTy endpoint.1).subst solved.resolveAll)

/-- A failed structural alternative is omitted; it cannot be activated. Fuel
exhaustion is retained so increasing fuel can finish its construction. -/
def branch (fuel first activation : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair)
    (endpoint : Ty × Ty) (b : ComparisonSelectedBases.Branch) : RunResult (Option Alternative) :=
  match ComparisonStructuralLayout.selected (ComparisonSelectedBases.inputNames p)
      (ComparisonSelectedBases.inputModes p) solved.fixedShapes b with
  | none => .success none
  | some layout =>
      match ComparisonStructuralCoherence.run fuel p.assumptions
          (ComparisonStructuralEndpoints.atShape declared) layout with
      | .exhausted => .exhausted
      | .rejected _ => .success none
      | .success theory => do
          let original ← ComparisonSignedEndpoints.compileGuards fuel
            (ComparisonSignedEndpoints.compile (ComparisonSelectedBases.inputTypeKeys p)
              (ComparisonSignedObservation.context layout ModExpr.var) endpoint.1 endpoint.2)
          match ComparisonSignedBranchCalls.compile
              (ComparisonSignedBranchImages.entries first p solved) layout original with
          | none => return none
          | some clauses => return some ⟨activation,b,endpoint,layout,theory,original,clauses⟩

def alternatives (fuel first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair)
    (endpoint : Ty × Ty) : Nat → List ComparisonSelectedBases.Branch → RunResult (List Alternative)
  | _,[] => .success []
  | activation,b::bs => do
      let head ← branch fuel first activation p solved declared endpoint b
      let tail ← alternatives fuel first p solved declared endpoint (activation+1) bs
      return head.toList ++ tail

structure Group where
  endpoint : Ty × Ty
  alternatives : List Alternative

def Group.formula (g : Group) : BoolExpr :=
  .and (.any (g.alternatives.map fun a=>.atom a.activation))
    (.all (g.alternatives.map Alternative.condition))

def groups (fuel first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (declared : List ComparisonStructuralEndpoints.Pair) :
    Nat → List (Ty × Ty) → RunResult (List Group)
  | _,[] => .success []
  | next,endpoint::rest => do
      let bs := branches first p solved endpoint
      let choices ← alternatives fuel first p solved declared endpoint next bs
      let tail ← groups fuel first p solved declared (next+bs.length) rest
      return ⟨endpoint,choices⟩::tail

structure Program where
  declared : List ComparisonStructuralEndpoints.Pair
  groups : List Group
  condition : CNF

def Program.sources (program : Program) : List ComparisonGuardedEndpointQueries.Source :=
  program.groups.flatMap fun group=>group.alternatives.map Alternative.source

def compile (fuel first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) : RunResult Program := do
  let declared ← ComparisonStructuralEndpoints.normalizeList fuel p solved
    (ComparisonStructuralEndpoints.declared p)
  let gs ← groups fuel first p solved declared
    (ComparisonSelectedBases.layout first p solved).next
    (ComparisonSignedObservation.sourceEndpoints p)
  let condition ← CompactCNF.toCNF fuel true
    (.and (ComparisonSelectedBases.selectorFormula first p solved)
      (.all (gs.map Group.formula)))
  return ⟨declared,gs,condition⟩

end ModalityInference.ComparisonPreparedQueries
