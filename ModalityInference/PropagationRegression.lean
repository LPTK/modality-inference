import ModalityInference.Inference

/-! Executable checks for the public propagation dispatcher and general elimination.
Exhaustive valuations occur only in these small test oracles. No proof imports or
native-decide axioms are used. -/

namespace ModalityInference.PropagationRegression

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def rejected : RunResult α → Bool
  | .rejected _ => true
  | _ => false

def exhausted : RunResult α → Bool
  | .exhausted => true
  | _ => false

-- Every CNF of at most two clauses over two Boolean atoms, including tautologies,
-- empty clauses, and repeated clauses, is compared with exhaustive valuations.
def literals : List Literal := [(0, false), (0, true), (1, false), (1, true)]
def clauses : List Clause := (List.range 16).map fun mask =>
  (literals.zipIdx.filter fun p => mask.testBit p.2).map Prod.fst
def smallCNFs : List CNF := [] ::
  (clauses.map (fun a => [a]) ++ clauses.flatMap (fun a => clauses.map fun b => [a, b]))
def cnfHolds (cs : CNF) (σ : Nat → Bool) : Bool := cs.all (CNFPropagation.clauseValue σ)
def cnfOracle (cs : CNF) : Bool :=
  (List.range 8).any fun bits => cnfHolds cs (fun v => bits.testBit v)
def cnfAgrees (cs : CNF) : Bool := match CNFPropagation.solve 100 cs with
  | .success σ => cnfOracle cs && cnfHolds cs (CNFPropagation.valuation σ)
  | .rejected _ => !cnfOracle cs
  | .exhausted => false

#guard smallCNFs.length = 273
#guard smallCNFs.all cnfAgrees
#guard cnfAgrees [[(0, true), (0, true)], [(0, false)]]
#guard cnfAgrees [[(0, true), (1, true)], [(0, true), (1, false)],
  [(0, false), (1, true)], [(0, false), (1, false)]]
#guard cnfAgrees [[(1, false), (2, true)], [(0, false), (1, true)],
  [(2, false), (0, true)], [(0, true)]]
#guard cnfAgrees [[(1, false), (2, true)], [(0, false), (1, true)],
  [(2, false), (0, true)], [(0, true)], [(2, false)]]

-- Exhaustion protects the crossed-clause product before it is allocated.
def productCNF : CNF :=
  [[(0, true), (1, true)], [(0, true), (2, true)], [(0, true), (3, true)],
   [(0, false), (4, true)], [(0, false), (5, true)], [(0, false), (6, true)]]
#guard CNFPropagation.crossSize productCNF 0 = 9
#guard exhausted (CNFPropagation.solve 8 productCNF)
#guard match CNFPropagation.solve 128 productCNF with
  | .success σ => cnfHolds productCNF (CNFPropagation.valuation σ)
  | _ => false
#guard CNFPropagation.solve 128 productCNF = CNFPropagation.solve 256 productCNF
#guard rejected (CNFPropagation.solve 1 [[]])
#guard exhausted (CNFPropagation.solve 0 [[]])

def x : ModExpr := .var (.flex 0)
def y : ModExpr := .var (.flex 1)
def z : ModExpr := .var (.flex 2)
def rigid : ModExpr := .var (.rigid 0)

def modeWitnessValid (cs : Bounds) : RunResult ModeAssignment → Bool
  | .success σ => cs.all (checkModeConstraint (some ∘ σ.total))
  | _ => false

def solvedWitnessValid (cs : Bounds) : Bool := match solve 2000 cs with
  | .success s => modeWitnessValid s.bounds (.success s.witness)
  | _ => false

def stableSolve (cs : Bounds) : Bool := match solve 2000 cs, solve 4000 cs with
  | .success a, .success b => a.witness == b.witness && a.bounds == b.bounds &&
      a.substitution == b.substitution
  | _, _ => false

-- A disjunctive conclusion is outside the direct Horn domain but remains accepted
-- by the unrestricted public API, which validates the reconstructed witness.
def nonHorn : Bounds := [.mode (.const Mode.localLower) (.join x y)]
def nonHornFalse : Bounds := nonHorn ++
  [.mode x (.const Mode.global), .mode y (.const Mode.global)]
#guard !ModeConsistency.isPolarized nonHorn
#guard !ModeConsistency.isPolarized nonHornFalse
#guard satisfiableModes 2000 nonHorn = ModeConsistency.general 2000 nonHorn
#guard modeWitnessValid nonHorn (satisfiableModes 2000 nonHorn)
#guard solvedWitnessValid nonHorn
#guard rejected (satisfiableModes 2000 nonHornFalse)
#guard rejected (solve 2000 nonHornFalse)
#guard exhausted (satisfiableModes 0 nonHorn)
#guard satisfiableModes 2000 nonHorn = satisfiableModes 4000 nonHorn
#guard stableSolve nonHorn
#guard match solve 2000 nonHorn with
  | .success s => s.substitution.modes.isEmpty && !s.bounds.isEmpty
  | _ => false

-- Guard failure must be detected on either backend, including mixed broad inputs.
def futureGuard : Bounds :=
  [.defined (.leftResidual x (.const Mode.bottom)), .mode (.const Mode.localLower) x]
def pastGuard : Bounds :=
  [.defined (.rightResidual (.const Mode.aliased) x), .mode x (.const Mode.uniqueOnly)]
#guard ModeConsistency.isPolarized futureGuard
#guard ModeConsistency.isPolarized pastGuard
#guard rejected (satisfiableModes 2000 futureGuard)
#guard rejected (satisfiableModes 2000 pastGuard)
#guard rejected (satisfiableModes 2000 (nonHorn ++ futureGuard))
#guard rejected (solve 2000 (nonHorn ++ futureGuard))
#guard rejected (satisfiableModes 2000 (nonHorn ++ pastGuard))
#guard rejected (solve 2000 (nonHorn ++ pastGuard))

-- A late lower bound propagates around a cycle; adding a contradictory upper bound
-- rejects. Satisfiable residual cycles also terminate and keep a stable witness.
def cycle : Bounds := [.mode y z, .mode x y, .mode z x, .mode (.const Mode.localLower) x]
#guard ModeConsistency.isPolarized cycle
#guard satisfiableModes 2000 cycle = HornPropagation.satisfiableModes 2000 cycle
#guard modeWitnessValid cycle (satisfiableModes 2000 cycle)
#guard solvedWitnessValid cycle
#guard rejected (solve 2000 (cycle ++ [.mode z (.const Mode.global)]))
#guard stableSolve cycle
def residualCycle : Bounds :=
  [.mode (.leftResidual x (.const Mode.global)) x, .mode x (.compose x (.const Mode.many))]
#guard modeWitnessValid residualCycle (satisfiableModes 2000 residualCycle)
#guard solvedWitnessValid residualCycle
#guard stableSolve residualCycle

-- Rigid and flexible identifiers with the same index remain distinct, and premise
-- assumptions remain present in universal validity queries.
def rigidBounds : Bounds := [.mode (.const Mode.localLower) rigid, .mode rigid x]
#guard modeWitnessValid rigidBounds (satisfiableModes 2000 rigidBounds)
#guard solvedWitnessValid rigidBounds
#guard match satisfiableModes 2000 rigidBounds with
  | .success σ => (σ.lookup (.rigid 0)).isSome && (σ.lookup (.flex 0)).isSome
  | _ => false
#guard match ConcreteBackend.entails 2000 rigidBounds [.mode (.const Mode.localLower) x] with
  | .success r => r.valid
  | _ => false
#guard match ConcreteBackend.entails 2000 [] [.mode (.const Mode.localLower) x] with
  | .success r => !r.valid
  | _ => false
#guard rejected (solve 2000 [.equal (.rigid 0) .unit])

-- The body ignores these closed definitions; their RHS is nevertheless solved.
def unusedBadLocal : RawTerm := .defn (.region (.stackPair .unit .unit)) .unit
def unusedBadShape : RawTerm := .defn (.app .unit .unit) .unit
#guard exhausted (infer 1 [] unusedBadLocal)
#guard rejected (infer 4000 [] unusedBadLocal)
#guard rejected (infer 4000 [] unusedBadShape)
#guard (infer 4000 [] (.defn (.stackPair .unit .unit) .unit)).isSuccess
#guard match infer 4000 [] (.lam () (.var 0)) with
  | .success r => !r.scheme.modParams.isEmpty && r.substitution.modes.isEmpty
  | _ => false

end ModalityInference.PropagationRegression
