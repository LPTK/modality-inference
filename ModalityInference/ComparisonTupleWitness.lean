import ModalityInference.ComparisonControls

/-! Construct one finite type from a nominal head polynomial and three scalar
coordinate formulas, using one shared symbolic scalar substitution. -/
namespace ModalityInference.ComparisonTupleWitness

open ComparisonControls SymbolicModes

inductive Expression (α : Type) where
  | head (type : CompareTy)
  | scalar (value : α)
  | join (left right : Expression α)
  | meet (left right : Expression α)
  deriving Repr

def Expression.map (f : α → β) : Expression α → Expression β
  | .head a => .head a
  | .scalar a => .scalar (f a)
  | .join a c => .join (a.map f) (c.map f)
  | .meet a c => .meet (a.map f) (c.map f)

def literal (b : Basis) (scalars : Nat → BoolExpr) (value : Literal) : Option (Expression BoolExpr) :=
  if h : value.1 < b.heads.length then
    if value.2 then some (.head b.heads[value.1]) else none
  else some (.scalar (if value.2 then scalars value.1 else .imp (scalars value.1) (.const false)))

def clause (b : Basis) (scalars : Nat → BoolExpr) (values : Clause) : Option (Expression BoolExpr) := do
  let terms ← values.mapM (literal b scalars)
  return terms.foldr Expression.join (.scalar (.const false))

def cnf (b : Basis) (scalars : Nat → BoolExpr) (clauses : CNF) : Option (Expression BoolExpr) := do
  let terms ← clauses.mapM (clause b scalars)
  return terms.foldr Expression.meet (.scalar (.const true))

def signed (heads : Nat) (values : Nat → BoolExpr) (i : Nat) : BoolExpr :=
  if (i - heads) % 2 == 0 then values ((i - heads) / 2)
  else .imp (values ((i - heads) / 2)) (.const false)

def upper (b : Basis) : CompareTy := b.rest.foldl CompareTy.join b.head

def lower (b : Basis) : CompareTy := b.rest.foldl CompareTy.meet b.head

def nominal (b : Basis) : Expression Bool → CompareTy
  | .head a => a
  | .scalar v => if v then upper b else lower b
  | .join a c => .join (nominal b a) (nominal b c)
  | .meet a c => .meet (nominal b a) (nominal b c)

def lowerRaw (b : Basis) (axis : Axis) : Expression BoolExpr → Option CompareTy
  | .head a => some a
  | .scalar e => return .modal (upper b) (← reify axis e)
  | .join a c => return .join (← lowerRaw b axis a) (← lowerRaw b axis c)
  | .meet a c => return .meet (← lowerRaw b axis a) (← lowerRaw b axis c)

def lowerGadget (b : Basis) (axis : Axis) (e : Expression BoolExpr) : Option CompareTy := do
  return .join (← lowerRaw b axis e) (.modal (upper b) (.const (axis.embed false)))

def upperRaw (b : Basis) : Expression BoolExpr → Option CompareTy
  | .head a => some (.modal a (.const Mode.bottom))
  | .scalar e => do
    let m ← reify .uniqueness (.imp e (.const false))
    return .modal (.modal (lower b) m) (.const Mode.bottom)
  | .join a c => return .join (← upperRaw b a) (← upperRaw b c)
  | .meet a c => return .meet (← upperRaw b a) (← upperRaw b c)

def upperGadget (b : Basis) (e : Expression BoolExpr) : Option CompareTy := do
  return .meet (← upperRaw b e) (.modal (lower b) (.const ⟨false, false, false⟩))

/-- Scalar coefficients for all three ordered coordinates share `values`.
Their encoded parameter pairs preserve complementarity without case splitting. -/
def reconstructWith (b : Basis) (scalars : Nat → BoolExpr) (p l f u : CNF) : Option CompareTy := do
  let np ← cnf b (fun _ => .const false) p
  let nl ← cnf b scalars l
  let nf ← cnf b scalars f
  let nu ← cnf b scalars u
  let gl ← lowerGadget b .locality nl
  let gf ← lowerGadget b .affinity nf
  let gu ← upperGadget b nu
  return .join (.meet (.meet (nominal b (np.map (BoolExpr.eval (fun _ => false)))) gl) gf) gu

def reconstruct (b : Basis) (values : Nat → BoolExpr) (p l f u : CNF) : Option CompareTy :=
  reconstructWith b (signed b.heads.length values) p l f u

end ModalityInference.ComparisonTupleWitness
