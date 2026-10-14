import ModalityInference.ModeBackend

/-! Deterministic consistency for the polarized Boolean fragment. Translation
preserves positive lattice premises and Horn conclusions directly; it never
constructs CNF or branches on assignments. The generic Horn solver constructs
the least Boolean witness, kept separate from symbolic modality bounds. -/
namespace ModalityInference

namespace BoolExpr

inductive IsPositive : BoolExpr → Prop where
  | const (b) : IsPositive (.const b)
  | atom (v) : IsPositive (.atom v)
  | and {a b} : IsPositive a → IsPositive b → IsPositive (.and a b)
  | or {a b} : IsPositive a → IsPositive b → IsPositive (.or a b)

inductive IsHorn : BoolExpr → Prop where
  | const (b) : IsHorn (.const b)
  | atom (v) : IsHorn (.atom v)
  | and {a b} : IsHorn a → IsHorn b → IsHorn (.and a b)
  | imp {a b} : IsPositive a → IsHorn b → IsHorn (.imp a b)

def nodes : BoolExpr → Nat
  | .const _ | .atom _ => 1
  | .and a b | .or a b | .imp a b => 1 + a.nodes + b.nodes

end BoolExpr

namespace HornPropagation

def positive (atoms : List Nat) : BoolExpr → Option (LeftExpr Bool atoms.length)
  | .const b => some (.const b)
  | .atom v => return .var (← ConcreteBackend.atomFin atoms v)
  | .and a b => return .meet (← positive atoms a) (← positive atoms b)
  | .or a b => return .join (← positive atoms a) (← positive atoms b)
  | .imp _ _ => none

def horn (atoms : List Nat) : BoolExpr → Option (RightExpr Bool atoms.length)
  | .const b => some (.const b)
  | .atom v => return .var (← ConcreteBackend.atomFin atoms v)
  | .and a b => return .meet (← horn atoms a) (← horn atoms b)
  | .imp a b => return .imply (← positive atoms a) (← horn atoms b)
  | .or _ _ => none

def domain (e : BoolExpr) : List Nat := e.atoms.mergeSort (· ≤ ·)

structure Model where
  atoms : List Nat
  values : Mapping Bool atoms.length

def Model.eval (m : Model) (v : Nat) : Bool :=
  ((ConcreteBackend.atomFin m.atoms v).map m.values.get).getD false

/-- The budget covers translation nodes and the atom-bounded propagation rounds.
Larger budgets select the same computation and the same least witness. -/
def requiredFuel (e : BoolExpr) : Nat := e.nodes + (domain e).length + 1

/-- Unsupported syntax is diagnosed separately from a contradictory Horn query. -/
def checkFormula (fuel : Nat) (e : BoolExpr) : RunResult Model :=
  if fuel < requiredFuel e then .exhausted else
  match horn (domain e) e with
  | none => .rejected "modality constraints are outside the polarized Horn fragment"
  | some r =>
    let values := RightExpr.hornSolve true r
    if RightExpr.eval values r then .success ⟨domain e, values⟩
    else .rejected "inconsistent modality bounds"

/-- Only the consistency witness is concrete; callers keep their symbolic bounds. -/
def satisfiableModes (fuel : Nat) (cs : Bounds) : RunResult ModeAssignment := do
  let model ← checkFormula fuel (boundsModeFormula cs)
  return ModeAssignment.ofBooleans cs model.eval

end HornPropagation
end ModalityInference
