import ModalityInference.ComparisonSelectorPropagation

/-! Parameter-preserving positive closure for coordinate formulas. Unlike the
nominal type polynomial solver, this primitive admits constant formulas. -/
namespace ModalityInference.ComparisonParametricPropagation

open ComparisonPropagation ComparisonSelectorPropagation

/-- Positive closure with no zero/one normalization on its head coordinates. -/
def closure (heads parameters : Nat) (program : Program count) : Store count :=
  let p := prepareProgram heads parameters program
  propagate (heads + 2 * parameters) p.edges p.lower

/-- Construct only the fields used by propagation. -/
def closureDirect (heads parameters : Nat) (program : Program count) : Store count :=
  propagate (heads + 2 * parameters)
    (program.edges.map fun e => { e with relation := guardRelation heads parameters e.relation })
    (Vector.ofFn fun v => meet (theory heads parameters) program.lower[v])

@[csimp] theorem closure_eq_closureDirect : @closure = @closureDirect := by
  rfl

def residualQuery (heads parameters : Nat) (program : Program count) : CNF :=
  residual (prepareProgram heads parameters program) (closure heads parameters program)

def witness (heads parameters : Nat) (choice : Nat → Bool) (program : Program count) : Store count :=
  specializeStore heads choice (closure heads parameters program)

end ModalityInference.ComparisonParametricPropagation
