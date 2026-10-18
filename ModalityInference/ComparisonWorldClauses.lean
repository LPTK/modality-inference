import ModalityInference.SymbolicCNF
import Mathlib.Data.Nat.Pairing

/-! Clause-wise constant selectors separate raw observation worlds. Scalar
blocks use identical local atom names after splitting, so their constraints
are solved with one common modality substitution. -/
namespace ModalityInference.ComparisonWorldClauses

abbrev WorldLiteral := Nat × ModalityInference.Literal
abbrev WorldClause := List WorldLiteral

def block (b : Nat) (c : WorldClause) : ModalityInference.Clause :=
  c.filterMap fun literal => if literal.1=b then some literal.2 else none

def blocks (c : WorldClause) : List Nat := (c.map Prod.fst).dedup

def selectorAtom (index b : Nat) : Nat := Nat.pair index b

def choices (cs : List WorldClause) : CNF :=
  cs.zipIdx.map fun (c,i) => (blocks c).map fun b => (selectorAtom i b,true)

def selected (index b : Nat) (c : WorldClause) : Clause :=
  (2 * selectorAtom index b + 1,false)::(block b c).map fun (v,p) => (2*v,p)

def nominal (cs : List WorldClause) : CNF :=
  cs.zipIdx.map fun (c,i) => selected i 0 c

def scalar (cs : List WorldClause) : CNF :=
  cs.zipIdx.flatMap fun (c,i) =>
    ((blocks c).filter (· != 0)).map fun b => selected i b c

end ModalityInference.ComparisonWorldClauses
