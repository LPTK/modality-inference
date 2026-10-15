import ModalityInference.ComparisonJointHorn

/-! Compile the axis-separated linear clauses into a boundary propagation
program. State indices are decoded separately from head observations and
complementary scalar parameters. -/
namespace ModalityInference.ComparisonJointProgram

open ComparisonPropagation

def renameParameters (parameters : Nat → Nat) : Obligation count → Obligation count
  | .lower target condition => .lower target (rename parameters condition)
  | .edge source target condition => .edge source target (rename parameters condition)
  | .upper source condition => .upper source (rename parameters condition)
  | .check condition => .check (rename parameters condition)

def compile (size : Nat) (decode : Nat → Option (Fin count))
    (parameters : Nat → Nat) (clauses : CNF) : Program count :=
  (clauses.map fun clause => renameParameters parameters
    (ComparisonJointHorn.compileClause decode clause)).foldl
      (Program.add size) (Program.empty count)

/-- Axis separation doubles input indices and reserves odd indices for
constant clause selectors. -/
def axisState (count v : Nat) : Option (Fin count) :=
  if v % 2 = 0 then
    if h : v / 2 < count then some ⟨v / 2, h⟩ else none
  else none

/-- Heads retain their finite prefix. Constant selectors precede the original
scalar inputs, and every parameter has a complementary positive pair. -/
def axisParameter (count heads selectors v : Nat) : Nat :=
  if v % 2 = 0 then
    if v / 2 < count + heads then v / 2 - count
    else heads + 2 * (selectors + (v / 2 - (count + heads)))
  else heads + 2 * (v / 2)

def axisProgram (count heads selectors modes : Nat) (clauses : CNF) : Program count :=
  compile (heads + 2 * (selectors + modes)) (axisState count)
    (axisParameter count heads selectors) clauses

end ModalityInference.ComparisonJointProgram
