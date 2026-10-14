import ModalityInference.SymbolicCNF
import ModalityInference.CompactCNF

/-! Uniform modality synthesis with the actual coordinate dependency domains.

Original atoms use even identifiers internally. Odd identifiers are constant
selectors: one selector chooses which independent component discharges each CNF
clause. All transformations are symbolic clause operations, without expansion of
Boolean valuations or candidates for modality expressions.
-/
namespace ModalityInference.ModalSynthesis

def locality (v : Nat) : Bool := v % 3 == 0

def selector (v : Nat) : Bool := v % 2 == 1

def component (side : Nat → Bool) (b : Bool) (cs : CNF) : CNF :=
  cs.zipIdx.map fun (c, i) =>
    (2 * i + 1, !b) ::
      ((c.filter fun l => side l.1 == b).map fun l => (2 * l.1, l.2))

def pivots (side : Nat → Bool) (b : Bool) (flex : List Nat) : List Nat :=
  (flex.filter fun v => side v == b).map (2 * ·)

structure Prepared where
  left : SymbolicCNF.Result
  right : SymbolicCNF.Result

def prepare (side : Nat → Bool) (flex : List Nat) (cs : CNF) : Prepared :=
  ⟨SymbolicCNF.solve (pivots side true flex) (component side true cs),
   SymbolicCNF.solve (pivots side false flex) (component side false cs)⟩

def Prepared.part (p : Prepared) (b : Bool) : SymbolicCNF.Result :=
  if b then p.left else p.right

def Prepared.query (p : Prepared) : CNF :=
  SymbolicCNF.abstract selector p.left.residual ++
  SymbolicCNF.abstract selector p.right.residual

def decode (σ : Nat → Bool) (v : Nat) : BoolExpr :=
  if selector v then .const (σ v) else .atom (v / 2)

def image (side : Nat → Bool) (p : Prepared) (σ : Nat → Bool) (v : Nat) : BoolExpr :=
  SymbolicCNF.substitute (decode σ)
    (SymbolicCNF.lookup (p.part (side v)).values (2 * v))

def witness (side : Nat → Bool) (flex : List Nat) (p : Prepared) (σ : Nat → Bool) :
    SymbolicModes.Elimination flex :=
  ⟨Vector.ofFn fun i => image side p σ flex[i], .const true⟩

/-- Constant selector consistency is decided by ordered lower/upper resolution. -/
def synthesizeCNF (fuel : Nat) (flex : List Nat) (cs : CNF) :
    RunResult (SymbolicModes.Elimination flex) := do
  let p := prepare locality flex cs
  let σ ← CNFPropagation.solve fuel (CompactCNF.clean p.query)
  return witness locality flex p (CNFPropagation.valuation σ)

/-- Callers include every required guard and rigid hypothesis in the formula.
The direct CNF conversion introduces no auxiliary Boolean atoms. -/
def synthesize (fuel : Nat) (flex : List Nat) (e : BoolExpr) :
    RunResult (SymbolicModes.Elimination flex) := do
  let cs ← CompactCNF.toCNF fuel true e
  synthesizeCNF fuel flex cs

end ModalityInference.ModalSynthesis
