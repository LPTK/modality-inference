import ModalityInference.ComparisonPropagation
import ModalityInference.SymbolicModes

/-! A finite signed control basis for modal action on a common shape. Its
endpoints are actual types, and every Boolean constant is represented by an
endpoint atom. The compiler never introduces Boolean atoms outside this basis.
Partial modality expressions retain a separate definedness condition. -/
namespace ModalityInference.ComparisonControls

inductive Channel where
  | lower | locality | affinity
  deriving Repr, DecidableEq, BEq

inductive Control where
  | locality (name : ModVar) (positive : Bool)
  | affinity (name : ModVar) (uniqueInput positive : Bool)
  | uniqueness (name : ModVar) (uniqueInput positive : Bool)
  deriving Repr, DecidableEq, BEq

def Control.name : Control → ModVar
  | .locality v _ | .affinity v _ _ | .uniqueness v _ _ => v

def Control.channel : Control → Channel
  | .locality _ _ => .locality
  | .affinity _ _ _ => .affinity
  | .uniqueness _ _ _ => .lower

def Control.axis : Control → SymbolicModes.Axis
  | .locality _ _ => .locality
  | .affinity _ _ _ => .affinity
  | .uniqueness _ _ _ => .uniqueness

def Control.positive : Control → Bool
  | .locality _ p | .affinity _ _ p | .uniqueness _ _ p => p

def Control.atom : Control → Nat
  | .locality v _ => v.atomIndex 0
  | .affinity v u _ | .uniqueness v u _ => v.atomIndex (if u then 2 else 1)

def Control.bit : Control → ModExpr
  | .locality v _ => .join (.future (.var v)) (.const ⟨false, true, true⟩)
  | .affinity v false _ => .join (.future (.var v)) (.const ⟨true, false, true⟩)
  | .affinity v true _ => .join (.close (.var v)) (.const ⟨true, false, true⟩)
  | .uniqueness v false _ => .join (.closeInv (.var v)) .epsilon
  | .uniqueness v true _ => .join (.var v) .epsilon

/-- Uniqueness is reversed in type order, so its positive control embeds a
negated mode bit. The residuals used here are total by their neutral axes. -/
def Control.expression (c : Control) : ModExpr :=
  let nativePositive := if c.channel == .lower then !c.positive else c.positive
  if nativePositive then c.bit
  else match c.axis with
    | .uniqueness => .leftResidual (.const (c.axis.embed false)) c.bit
    | _ => .rightResidual c.bit (.const (c.axis.embed false))

def controls (v : ModVar) : List Control :=
  [.locality v true, .locality v false,
   .affinity v false true, .affinity v false false,
   .affinity v true true, .affinity v true false,
   .uniqueness v false true, .uniqueness v false false,
   .uniqueness v true true, .uniqueness v true false]

inductive Key where
  | head (type : CompareTy)
  | bottom | raised | localFloor | affineFloor | top
  | control (value : Control)
  deriving Repr, DecidableEq, BEq

structure Basis where
  head : CompareTy
  rest : List CompareTy := []
  modes : List ModVar := []
  deriving Repr

def Basis.heads (b : Basis) : List CompareTy := b.head :: b.rest

def Basis.bottom (b : Basis) : CompareTy :=
  .modal (ComparisonInterpolation.meet b.head b.rest) (.const Mode.bottom)

def Basis.top (b : Basis) : CompareTy :=
  .modal (ComparisonInterpolation.join b.head b.rest) (.const Mode.top)

def Basis.keys (b : Basis) : List Key :=
  b.heads.map Key.head ++ [.bottom, .raised, .localFloor, .affineFloor, .top] ++
    (b.modes.flatMap controls).map Key.control

def Basis.term (b : Basis) : Key → CompareTy
  | .head a => a
  | .bottom => b.bottom
  | .raised => .modal b.bottom (.const Mode.top)
  | .localFloor => .modal b.top (.const Mode.global)
  | .affineFloor => .modal b.top (.const Mode.many)
  | .top => b.top
  | .control c => .modal (if c.channel == .lower then b.bottom else b.top) c.expression

def Basis.types (b : Basis) : List CompareTy := b.keys.map b.term

def Basis.index (b : Basis) (k : Key) : Option Nat :=
  let i := b.keys.idxOf k
  if i < b.keys.length then some i else none

def Channel.lowerKey : Channel → Key
  | .lower => .bottom
  | .locality => .localFloor
  | .affinity => .affineFloor

def Channel.upperKey : Channel → Key
  | .lower => .raised
  | .locality | .affinity => .top

def atomControl (c : Channel) (i : Nat) (positive : Bool) : Option Control :=
  let v := SymbolicModes.atomVariable i
  match c, i % 3 with
  | .lower, 1 => some (.uniqueness v false positive)
  | .lower, 2 => some (.uniqueness v true positive)
  | .locality, 0 => some (.locality v positive)
  | .affinity, 1 => some (.affinity v false positive)
  | .affinity, 2 => some (.affinity v true positive)
  | _, _ => none

def liftClause (b : Basis) (c : Channel) : Clause → Option Clause
  | [] => return [(← b.index c.lowerKey, true)]
  | literals => literals.mapM fun (i, p) => do
      let control ← atomControl c i p
      return (← b.index (.control control), true)

def liftCNF (b : Basis) (c : Channel) : CNF → Option CNF
  | [] => return [[(← b.index c.upperKey, true)]]
  | clauses => clauses.mapM (liftClause b c)

def compile (fuel : Nat) (b : Basis) (c : Channel) (positive : Bool) (e : BoolExpr) : RunResult CNF := do
  let clauses ← CompactCNF.toCNF fuel positive e
  match liftCNF b c clauses with
  | some result => return result
  | none => .rejected "modality control outside its finite coordinate domain"

def low (fuel : Nat) (b : Basis) (m : ModExpr) : RunResult CNF :=
  compile fuel b .lower false m.project.uniqueness

def high (fuel : Nat) (b : Basis) (m : ModExpr) : RunResult CNF := do
  let locality ← compile fuel b .locality true m.project.locality
  let affine ← compile fuel b .affinity true m.project.affinity
  return ComparisonPropagation.meet locality affine

inductive Coordinate where
  | unaffected | locality | affinity | uniqueness
  deriving Repr, DecidableEq, BEq

def Coordinate.modalWith (c : Coordinate) (modeAtom : Nat → Nat)
    (value : BoolExpr) (m : ModExpr) : BoolExpr :=
  let rename := SymbolicCNF.substitute (fun i => .atom (modeAtom i))
  match c with
  | .unaffected => value
  | .locality => .and value (rename m.project.locality)
  | .affinity => .and value (rename m.project.affinity)
  | .uniqueness => .or value (.imp (rename m.project.uniqueness) (.const false))

def Coordinate.modal (c : Coordinate) (value : BoolExpr) (m : ModExpr) : BoolExpr :=
  c.modalWith id value m

/-- Head atoms and modality atoms occupy caller-supplied, disjoint namespaces.
Every occurrence of a supplied head remains opaque, including partial labels. -/
def Basis.formula (b : Basis) (headAtom modeAtom : Nat → Nat) (c : Coordinate) (k : Key) : BoolExpr :=
  let heads := b.heads.mapIdx fun i _ => .atom (headAtom i)
  let modal := c.modalWith modeAtom
  let bottom := modal (BoolExpr.all heads) (.const Mode.bottom)
  let top := modal (BoolExpr.any heads) (.const Mode.top)
  match k with
  | .head a => .atom (headAtom (b.heads.idxOf a))
  | .bottom => bottom
  | .raised => modal bottom (.const Mode.top)
  | .localFloor => modal top (.const Mode.global)
  | .affineFloor => modal top (.const Mode.many)
  | .top => top
  | .control q => modal (if q.channel == .lower then bottom else top) q.expression

/-- One of four coordinate theories, with explicit equations for every basis
atom. The caller separately supplies rigid inequalities and modality guards. -/
def Basis.theoryAt (b : Basis) (basisAtom headAtom modeAtom : Nat → Nat) (c : Coordinate) : BoolExpr :=
  BoolExpr.all (b.keys.mapIdx fun i k =>
    .equal (.atom (basisAtom i)) (b.formula headAtom modeAtom c k))

def Basis.theory (b : Basis) (basisAtom headAtom modeAtom : Nat → Nat) : BoolExpr :=
  BoolExpr.any ([Coordinate.unaffected, .locality, .affinity, .uniqueness].map
    (b.theoryAt basisAtom headAtom modeAtom))

end ModalityInference.ComparisonControls
