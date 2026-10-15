import ModalityInference.ComparisonPropagation
import ModalityInference.SymbolicCNF
import ModalityInference.ComparisonSliceCNF

/-! Joint constant-selector and positive-polynomial synthesis by propagation.
Selectors are encoded by complementary positive coordinates. Relational closure
preserves their values, while head coordinates remain monotone. The residual
query is abstracted to selector atoms before ordered Boolean elimination; the
selected constants are substituted before reconstructing finite type syntax.
-/
namespace ModalityInference.ComparisonSelectorPropagation

open ComparisonPropagation

def theory (heads selectors : Nat) : CNF :=
  (List.range selectors).flatMap fun i =>
    [[(heads + 2 * i, true), (heads + 2 * i + 1, true)],
     [(heads + 2 * i, false), (heads + 2 * i + 1, false)]]


def agreement (heads selectors : Nat) : CNF :=
  (List.range (2 * selectors)).flatMap fun i =>
    [[(2 * (heads + i), false), (2 * (heads + i) + 1, true)],
     [(2 * (heads + i) + 1, false), (2 * (heads + i), true)]]

def guardRelation (heads selectors : Nat) (relation : CNF) : CNF :=
  relation ++ rename (2 * ·) (theory heads selectors) ++
    rename (fun i => 2 * i + 1) (theory heads selectors) ++ agreement heads selectors

def prepareProgram (heads selectors : Nat) (program : Program count) : Program count where
  lower := Vector.ofFn fun v => meet (theory heads selectors) program.lower[v]
  edges := program.edges.map fun e => { e with relation := guardRelation heads selectors e.relation }
  upper := Vector.ofFn fun v => implies (theory heads selectors) program.upper[v]
  checks := implies (theory heads selectors) program.checks


def fixedValue (heads : Nat) (choice : Nat → Bool) (v : Nat) : Bool :=
  if (v - heads) % 2 == 0 then choice ((v - heads) / 2) else !choice ((v - heads) / 2)

def select (heads : Nat) (choice parameters : Nat → Bool) (v : Nat) : Bool :=
  if v < heads then parameters v else fixedValue heads choice v

def fixedClause (heads : Nat) (choice : Nat → Bool) (c : Clause) : Bool :=
  c.any fun literal => decide (heads ≤ literal.1) && fixedValue heads choice literal.1 == literal.2

/-- Substitute the chosen constant selectors and retain only head literals. -/
def specialize (heads : Nat) (choice : Nat → Bool) (cs : CNF) : CNF :=
  (cs.filter fun c => !(fixedClause heads choice c)).map
    (List.filter fun literal => literal.1 < heads)

def specializeStore (heads : Nat) (choice : Nat → Bool) (store : Store count) : Store count :=
  Vector.ofFn fun v => specialize heads choice store[v]


def cap (heads : Nat) : CNF := [(List.range heads).map fun i => (i, true)]

def normalize (heads : Nat) (program : Program count) : Program count :=
  { program with
    lower := Vector.ofFn fun v => join (seed heads) program.lower[v]
    upper := Vector.ofFn fun v => meet (cap heads) program.upper[v] }


def prepared (heads selectors : Nat) (program : Program count) : Program count :=
  prepareProgram heads selectors (normalize heads program)

def closure (heads selectors : Nat) (program : Program count) : Store count :=
  let p := prepared heads selectors program
  propagate (heads + 2 * selectors) p.edges p.lower

/-- Closure depends only on lower bounds and edges. Construct them directly so
unused upper/check implications are not evaluated during witness extraction. -/
def closureDirect (heads selectors : Nat) (program : Program count) : Store count :=
  propagate (heads + 2 * selectors)
    (program.edges.map fun e => { e with relation := guardRelation heads selectors e.relation })
    (Vector.ofFn fun v => meet (theory heads selectors) (join (seed heads) program.lower[v]))

@[csimp] theorem closure_eq_closureDirect : @closure = @closureDirect := by
  funext count heads selectors program
  simp only [closure, closureDirect, prepared, prepareProgram, normalize, Fin.getElem_fin,
    Vector.getElem_ofFn]

def residualQuery (heads selectors : Nat) (program : Program count) : CNF :=
  residual (prepared heads selectors program) (closure heads selectors program)

def witness (heads selectors : Nat) (choice : Nat → Bool) (program : Program count) : Store count :=
  specializeStore heads choice (closure heads selectors program)


def selectorChoice (heads : Nat) (parameters : Nat → Bool) (i : Nat) : Bool :=
  parameters (heads + 2 * i)

def keepSelectors (heads selectors : Nat) (v : Nat) : Bool :=
  decide (heads ≤ v ∧ v < heads + 2 * selectors)

/-- The outer selector theory is fixed throughout abstraction, so upper/check
obligations need no duplicate implication from that theory. -/
def query (heads selectors : Nat) (program : Program count) : CNF :=
  theory heads selectors ++ SymbolicCNF.abstract (keepSelectors heads selectors)
    (ComparisonSliceCNF.residual heads selectors (normalize heads program) (closure heads selectors program))


structure Result (count : Nat) where
  assignment : CNFPropagation.Assignment
  store : Store count

/-- Solve only constant selector clauses, then specialize the propagated polynomial. -/
def run (fuel heads selectors : Nat) (program : Program count) : RunResult (Result count) := do
  let assignment ← CNFPropagation.solve fuel (query heads selectors program)
  return ⟨assignment, witness heads selectors
    (selectorChoice heads (CNFPropagation.valuation assignment)) program⟩

end ModalityInference.ComparisonSelectorPropagation
