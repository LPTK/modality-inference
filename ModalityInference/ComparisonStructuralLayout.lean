import ModalityInference.ComparisonSelectedBases
import ModalityInference.ComparisonStructuralNode
import ModalityInference.ComparisonStructuralFamily

/-! Recursive observer queries over a selected finite structural basis. A node
retains whole endpoint implications. Its constructor cells use one selected
child observer; product and sum copies agree on the retained scalar inputs,
while a function child has its own scalar namespace. -/
namespace ModalityInference.ComparisonStructuralLayout

open ComparisonControls

inductive Constructor where
  | prod | sum | fn
  deriving Repr, DecidableEq

def Constructor.op : Constructor → CompareTy → CompareTy → CompareTy
  | .prod => .prod
  | .sum => .sum
  | .fn => .fn

def Constructor.shape : Constructor → ComparisonShape → ComparisonShape → ComparisonShape
  | .prod => .prod
  | .sum => .sum
  | .fn => .fn

def Constructor.dual : Constructor → Bool
  | .fn => true
  | _ => false

inductive Layout where
  | leaf (shape : ComparisonShape) (basis : Basis)
  | fork (kind : Constructor) (basis : Basis) (left right : Layout)
  deriving Repr

def Layout.shape : Layout → ComparisonShape
  | .leaf shape _ => shape
  | .fork kind _ left right => kind.shape left.shape right.shape

def Layout.basis : Layout → Basis
  | .leaf _ basis | .fork _ basis _ _ => basis

/-- Empty child bases have no constructor cells, hence no child port. -/
def build (names : List TypeVar) (modes : List ModVar)
    (fixed : TypeVar → ComparisonShape) : ComparisonShape → Option Layout
  | s@(.var _) | s@(.unit) | s@(.credit) =>
      (ComparisonStructuralBasis.basis names modes fixed s).map (.leaf s)
  | s@(.prod a b) | s@(.sum a b) | s@(.fn a b) => do
      let basis ← ComparisonStructuralBasis.basis names modes fixed s
      let kind := match s with | .prod _ _ => Constructor.prod | .sum _ _ => .sum | _ => .fn
      match ComparisonStructuralBasis.basis names modes fixed a,
          ComparisonStructuralBasis.basis names modes fixed b with
      | some _, some _ => return .fork kind basis (← build names modes fixed a) (← build names modes fixed b)
      | _, _ => return .leaf s basis

/-- Three disjoint namespaces: this node, its left subtree, its right subtree. -/
def localAtom (i : Nat) : Nat := 3 * i

def leftAtom (i : Nat) : Nat := 3 * i + 1

def rightAtom (i : Nat) : Nat := 3 * i + 2

/-- The local namespace separates basis, fixed heads, scalar inputs and choices. -/
def basisAtom (i : Nat) : Nat := localAtom (4 * i)
def headAtom (i : Nat) : Nat := localAtom (4 * i + 1)
def modeAtom (i : Nat) : Nat := localAtom (4 * i + 2)
def choiceAtom (i : Nat) : Nat := localAtom (4 * i + 3)

def rename (atoms : Nat → Nat) (e : BoolExpr) : BoolExpr :=
  SymbolicCNF.substitute (fun i => .atom (atoms i)) e

def coordinateBits : Coordinate → Bool × Bool
  | .unaffected => (false, false)
  | .locality => (false, true)
  | .affinity => (true, false)
  | .uniqueness => (true, true)

def coordinateTest (c : Coordinate) : BoolExpr :=
  .and (.equal (.atom (choiceAtom 1)) (.const (coordinateBits c).1))
    (.equal (.atom (choiceAtom 2)) (.const (coordinateBits c).2))

/-- Choices 3 and 4 record globally inhabited false and true observer fibers. -/
def rangeTheory (basis : Basis) : BoolExpr :=
  .and (.or (.atom (choiceAtom 3)) (.atom (choiceAtom 4)))
    (.all ((List.range basis.types.length).map fun i =>
      .and (.imp (.atom (basisAtom i)) (.atom (choiceAtom 4)))
        (.imp (.imp (.atom (basisAtom i)) (.const false)) (.atom (choiceAtom 3)))))

def nodeTheory (assumptions : Bounds) (basis : Basis) (bounds : List ComparisonStructuralNode.Bound) : BoolExpr :=
  .and (rangeTheory basis)
    (.and (.any ([Coordinate.unaffected, .locality, .affinity, .uniqueness].map fun c =>
      .and (coordinateTest c) (.and (basis.theoryAt basisAtom headAtom modeAtom c)
        (if c == .unaffected then .const true else rename modeAtom (boundsModeFormula assumptions)))))
      (ComparisonStructuralFamily.cnfFormula false BoolExpr.atom
        (ComparisonStructuralNode.clauses basisAtom bounds)))

def childCoordinate (child : Nat → Nat) : BoolExpr :=
  .or (rename child (coordinateTest .unaffected))
    (.any ([Coordinate.unaffected, .locality, .affinity, .uniqueness].map fun c =>
      .and (coordinateTest c) (rename child (coordinateTest c))))

def sharedModes (modes : List ModVar) (child : Nat → Nat) : BoolExpr :=
  .all (modes.flatMap fun v => (List.range 3).map fun i =>
    .equal (.atom (modeAtom (v.atomIndex i))) (.atom (child (modeAtom (v.atomIndex i)))))

def childTheory (kind : Constructor) (modes : List ModVar) (child : Nat → Nat) : BoolExpr :=
  if kind.dual then .const true else .and (childCoordinate child) (sharedModes modes child)

/-- Every Cartesian constructor atom keeps its whole parent observation. -/
def links (kind : Constructor) (parent left right : Basis) (takeLeft : Bool) : BoolExpr :=
  .all (left.types.flatMap fun a => right.types.map fun b =>
    let p := .atom (headAtom (parent.heads.idxOf (kind.op a b)))
    let c := if takeLeft then .atom (leftAtom (basisAtom (left.types.idxOf a)))
      else .atom (rightAtom (basisAtom (right.types.idxOf b)))
    .equal p (if takeLeft && kind.dual then .imp c (.const false) else c))

def query (assumptions : Bounds) (endpoints : ComparisonShape → List (CompareTy × CompareTy)) : Layout → Option BoolExpr
  | .leaf s basis => do
      return nodeTheory assumptions basis (← ComparisonStructuralNode.prepare basis (endpoints s))
  | layout@(.fork kind basis left right) => do
      let here ← ComparisonStructuralNode.prepare basis (endpoints layout.shape)
      let l ← query assumptions endpoints left
      let r ← query assumptions endpoints right
      return .and (nodeTheory assumptions basis here)
        (.or (.and (.atom (choiceAtom 0))
          (.and (links kind basis left.basis right.basis true)
            (.and (childTheory kind basis.modes leftAtom) (rename leftAtom l))))
          (.and (.imp (.atom (choiceAtom 0)) (.const false))
            (.and (links kind basis left.basis right.basis false)
              (.and (childTheory kind basis.modes rightAtom) (rename rightAtom r)))))

def run (fuel : Nat) (assumptions : Bounds) (endpoints : ComparisonShape → List (CompareTy × CompareTy))
    (layout : Layout) : RunResult CNF :=
  match query assumptions endpoints layout with
  | none => .rejected "structural endpoint is outside its selected finite basis"
  | some q => CompactCNF.toCNF fuel true q

/-- The selected branch uses the exact same computable structural basis. -/
def selected (names : List TypeVar) (modes : List ModVar) (fixed : TypeVar → ComparisonShape)
    (branch : ComparisonSelectedBases.Branch) : Option Layout :=
  build names modes fixed branch.shape

end ModalityInference.ComparisonStructuralLayout
