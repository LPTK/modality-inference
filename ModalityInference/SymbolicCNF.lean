import ModalityInference.SymbolicModes
import ModalityInference.CNFPropagation

/-! Ordered symbolic Boolean elimination. Each pivot is replaced by the join of
its lower demands after the remaining pivots have been eliminated. No Boolean
assignment is enumerated: the retained witness is an expression in the parameters.
-/
namespace ModalityInference.SymbolicCNF

abbrev Assignment := List (Nat × BoolExpr)

def lookup (s : Assignment) (v : Nat) : BoolExpr := (s.lookup v).getD (.atom v)

def substitute (s : Nat → BoolExpr) : BoolExpr → BoolExpr
  | .const b => .const b
  | .atom v => s v
  | .and a b => SymbolicModes.smartAnd (substitute s a) (substitute s b)
  | .or a b => SymbolicModes.smartOr (substitute s a) (substitute s b)
  | .imp a b => SymbolicModes.smartImp (substitute s a) (substitute s b)

def literal (s : Assignment) (l : Literal) : BoolExpr :=
  if l.2 then lookup s l.1 else SymbolicModes.smartImp (lookup s l.1) (.const false)

def clause (s : Assignment) (c : Clause) : BoolExpr :=
  c.foldr (fun l e => SymbolicModes.smartOr (literal s l) e) (.const false)

def lower (s : Assignment) (cs : CNF) (v : Nat) : BoolExpr :=
  (CNFPropagation.lower cs v).foldr (fun c e =>
    SymbolicModes.smartOr (SymbolicModes.smartImp (clause s c) (.const false)) e)
    (.const false)

structure Result where
  values : Assignment
  residual : CNF

/-- The pivot order is finite and explicit. The residual retains every uneliminated
parameter and every constant obligation, including an inconsistent empty clause. -/
def solve : List Nat → CNF → Result
  | [], cs => ⟨[], cs⟩
  | v :: vs, cs =>
    let r := solve vs (CNFPropagation.eliminate cs v)
    ⟨(v, lower r.values cs v) :: r.values, r.residual⟩

/-- Universal abstraction of all non-parameters. Tautological clauses are removed
before their quantified literals, so a quantified tautology remains true. -/
def abstract (keep : Nat → Bool) (cs : CNF) : CNF :=
  (cleanCNF cs).map (List.filter fun l => keep l.1)

end ModalityInference.SymbolicCNF
