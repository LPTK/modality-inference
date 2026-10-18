import ModalityInference.ComparisonShapeCandidates
import ModalityInference.CompactCNF

/-! Shared finite shape choices are Boolean selectors. Constructor branches
combine their guards while repeated parameters use the same selector atoms. -/
namespace ModalityInference.ComparisonShapeSelectors

structure Layout where
  parameters : List TypeVar
  choices : List ComparisonShape
  first : Nat
  deriving Repr

def ofTemplates (first : Nat) (choices templates : List ComparisonShape) : Layout :=
  ⟨(templates.flatMap ComparisonShape.vars).dedup, choices, first⟩

def Layout.atom (layout : Layout) (v : TypeVar) (i : Nat) : Nat :=
  layout.first + layout.choices.length * layout.parameters.idxOf v + i

def Layout.next (layout : Layout) : Nat :=
  layout.first + layout.choices.length * layout.parameters.length

def Layout.one (layout : Layout) (v : TypeVar) : BoolExpr :=
  .and
    (.any ((List.finRange layout.choices.length).map fun (i : Fin layout.choices.length) => .atom (layout.atom v i)))
    (.all ((List.finRange layout.choices.length).flatMap fun (i : Fin layout.choices.length) =>
      (List.finRange layout.choices.length).map fun (j : Fin layout.choices.length) =>
        if i = j then .const true
        else .imp (.atom (layout.atom v i)) (.imp (.atom (layout.atom v j)) (.const false))))

def Layout.theory (layout : Layout) : BoolExpr :=
  .all (layout.parameters.map layout.one)

def Layout.compile (layout : Layout) (fuel : Nat) : RunResult CNF :=
  CompactCNF.toCNF fuel true layout.theory

/-- Choose the first occurrence of a candidate, retaining duplicate input
anchors without creating competing true selectors. -/
def Layout.encode (layout : Layout) (ρ : TypeVar → ComparisonShape) (n : Nat) : Bool :=
  layout.parameters.any fun v => n == layout.atom v (layout.choices.idxOf (ρ v))

def Layout.decode (layout : Layout) (world : Nat → Bool) (v : TypeVar) : ComparisonShape :=
  match (List.finRange layout.choices.length).find? (fun (i : Fin layout.choices.length) => world (layout.atom v i)) with
  | some i => layout.choices[i]
  | none => .unit

structure Branch where
  shape : ComparisonShape
  guard : BoolExpr
  deriving Repr

def combine (op : ComparisonShape → ComparisonShape → ComparisonShape)
    (left right : List Branch) : List Branch :=
  left.flatMap fun a => right.map fun b => ⟨op a.shape b.shape, .and a.guard b.guard⟩

/-- The list contains finite structural alternatives; its guards synchronize
all occurrences of every parameter through the common layout. -/
def Layout.branches (layout : Layout) : ComparisonShape → List Branch
  | .var v => (List.finRange layout.choices.length).map fun (i : Fin layout.choices.length) =>
      ⟨layout.choices[i], .atom (layout.atom v i)⟩
  | .unit => [⟨.unit, .const true⟩]
  | .credit => [⟨.credit, .const true⟩]
  | .prod a b => combine .prod (layout.branches a) (layout.branches b)
  | .sum a b => combine .sum (layout.branches a) (layout.branches b)
  | .fn a b => combine .fn (layout.branches a) (layout.branches b)

end ModalityInference.ComparisonShapeSelectors
