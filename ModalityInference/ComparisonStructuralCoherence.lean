import ModalityInference.ComparisonStructuralLayout

/-! Function roots compare future modalities. A uniqueness observer therefore
has only true constructor values; the selected child's global range records
that condition, with the function-domain sign reversed. -/
namespace ModalityInference.ComparisonStructuralCoherence

open ComparisonControls ComparisonStructuralLayout

def signed (takeLeft : Bool) (value : Bool) : Bool := if takeLeft then !value else value

def rangeClause (takeLeft : Bool) (child : Nat → Nat) : BoolExpr :=
  .imp (coordinateTest .uniqueness)
    (.imp (.atom (child (choiceAtom (if takeLeft then 4 else 3)))) (.const false))

def childClause (kind : Constructor) (takeLeft : Bool) (child : Nat → Nat) : BoolExpr :=
  if kind.dual then rangeClause takeLeft child else .const true

def rangeAtom (route : Nat → Nat) (value : Bool) : BoolExpr :=
  .atom (route (choiceAtom (if value then 4 else 3)))

def rangeClosure : BoolExpr :=
  .and (.imp (.or (coordinateTest .locality) (coordinateTest .affinity))
      (.imp (rangeAtom id true) (rangeAtom id false)))
    (.imp (coordinateTest .uniqueness) (.imp (rangeAtom id false) (rangeAtom id true)))

def constructorSigned (kind : Constructor) (takeLeft value : Bool) : Bool :=
  if kind.dual then signed takeLeft value else value

def rangeInclusion (kind : Constructor) (takeLeft : Bool) (child : Nat → Nat) : BoolExpr :=
  .and (.imp (rangeAtom child false) (rangeAtom id (constructorSigned kind takeLeft false)))
    (.imp (rangeAtom child true) (rangeAtom id (constructorSigned kind takeLeft true)))

def headCoherence (basis : Basis) : BoolExpr :=
  .all (basis.heads.mapIdx fun i t =>
    .equal (.atom (headAtom i)) (.atom (headAtom (basis.heads.idxOf t))))

def theory : Layout → BoolExpr
  | .leaf _ basis => .and (headCoherence basis) rangeClosure
  | .fork kind basis left right =>
      .and (headCoherence basis) (.and rangeClosure
        (.or (.and (.atom (choiceAtom 0))
          (.and (childClause kind true leftAtom)
            (.and (rangeInclusion kind true leftAtom) (rename leftAtom (theory left)))))
          (.and (.imp (.atom (choiceAtom 0)) (.const false))
            (.and (childClause kind false rightAtom)
              (.and (rangeInclusion kind false rightAtom) (rename rightAtom (theory right)))))))

def run (fuel : Nat) (assumptions : Bounds)
    (endpoints : ComparisonShape → List (CompareTy × CompareTy)) (layout : Layout) : RunResult CNF :=
  match query assumptions endpoints layout with
  | none => .rejected "structural endpoint is outside its selected finite basis"
  | some q => CompactCNF.toCNF fuel true (.and q (theory layout))

end ModalityInference.ComparisonStructuralCoherence
