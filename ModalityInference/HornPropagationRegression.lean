import ModalityInference.HornPropagation

/-! Executable checks for direct propagation, finite cycles, and its domain boundary. -/
namespace ModalityInference.HornPropagationRegression

open HornPropagation
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def accepted (e : BoolExpr) : Bool := (checkFormula 1000 e).isSuccess

def rejected : RunResult α → Bool
  | .rejected _ => true
  | _ => false

def exhaustive (e : BoolExpr) : Bool :=
  (List.range 8).any fun bits => e.eval fun i => bits.testBit i

def a : BoolExpr := .atom 0
def b : BoolExpr := .atom 1
def c : BoolExpr := .atom 2

-- A late lower bound must revisit earlier upper bounds until the cycle is saturated.
def cycle : BoolExpr := .all [.imp b c, .imp a b, .imp c a, a]
#guard match checkFormula 100 cycle with
  | .success m => m.eval 0 && m.eval 1 && m.eval 2
  | _ => false
#guard rejected (checkFormula 100 (.and cycle (.imp c (.const false))))

-- Keep disjunctive premises factored; propagation never distributes them into CNF.
#guard accepted (.all [.imp (.or a b) c, a, c])
#guard rejected (checkFormula 100 (.all [.imp (.or a b) c, b, .imp c (.const false)]))

-- A disjunctive conclusion belongs to the unrestricted API, not this fragment.
#guard (horn (domain (.or a b)) (.or a b)).isNone
#guard checkFormula 0 cycle matches .exhausted
#guard match checkFormula (requiredFuel cycle) cycle, checkFormula 1000 cycle with
  | .success x, .success y => (List.range 3).all fun i => x.eval i == y.eval i
  | _, _ => false

-- Differential checks use exhaustive valuations only as a test oracle.
def premises : List BoolExpr :=
  [.const false, .const true, a, b, c, .and a b, .or b c, .and a (.or b c)]
def conclusions : List BoolExpr := [.const false, .const true, a, b, c]
def queries : List BoolExpr := premises.flatMap fun p => conclusions.map (.imp p)
#guard queries.all fun x => accepted x == exhaustive x
#guard queries.all fun x => queries.all fun y =>
  accepted (.and x y) == exhaustive (.and x y)

-- Partial expressions keep their definedness obligations in the propagated query.
def mu : ModExpr := .var (.flex 0)
#guard (HornPropagation.satisfiableModes 200
  [.defined (.leftResidual mu (.const Mode.bottom)),
   .mode (.const Mode.localLower) mu]).isSuccess == false
#guard (HornPropagation.satisfiableModes 200
  [.defined (.rightResidual (.const Mode.aliased) mu),
   .mode mu (.const Mode.uniqueOnly)]).isSuccess == false

-- A satisfiable cyclic residual family is processed as a finite Horn query.
#guard (HornPropagation.satisfiableModes 200
  [.mode (.leftResidual mu (.const Mode.global)) mu,
   .mode mu (.compose mu (.const Mode.many))]).isSuccess

end ModalityInference.HornPropagationRegression
