import ModalityInference.ComparisonControls

/-! Finite inherited-action tests relate product and sum observer coordinates.
Signed controls expose precisely the input bits used by each modal channel. -/
namespace ModalityInference.ComparisonStructuralAlignment

open ComparisonControls

def neutral : Coordinate → Mode → Bool
  | .unaffected, _ => true
  | .locality, m => m.isLocal
  | .affinity, m => m.once
  | .uniqueness, m => m.unique

def neutralFormula (coordinate : Coordinate) (modeAtom : Nat → Nat)
    (m : ModExpr) : BoolExpr :=
  let rename := SymbolicCNF.substitute (fun i => .atom (modeAtom i))
  match coordinate with
  | .unaffected => .const true
  | .locality => rename m.project.locality
  | .affinity => rename m.project.affinity
  | .uniqueness => rename m.project.uniqueness

def tests (names : List ModVar) : List ModExpr :=
  [.const Mode.global, .const Mode.many, .const Mode.top] ++
    (names.flatMap controls).map Control.expression

def transition (parent child : Coordinate) (parentAtom childAtom : Nat → Nat)
    (names : List ModVar) : BoolExpr :=
  .all ((tests names).map fun m =>
    .imp (neutralFormula parent parentAtom m) (neutralFormula child childAtom m))

def compile (fuel : Nat) (parent child : Coordinate) (parentAtom childAtom : Nat → Nat)
    (names : List ModVar) : RunResult CNF :=
  CompactCNF.toCNF fuel true (transition parent child parentAtom childAtom names)

end ModalityInference.ComparisonStructuralAlignment
