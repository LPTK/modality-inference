import ModalityInference.ComparisonFiniteCertificateMachineRestriction
import ModalityInference.ComparisonFiniteCertificateRestriction
import ModalityInference.ComparisonFiniteCertificateRows

/-! A finite representation of the tables needed by a supplied comparison
query. Carrier dimensions are bounded separately by the input-size theorem. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonExecutableSyntax

def queryPairs (queries : List CompareTy) : List (CompareTy × Option ModExpr) :=
  queries.map fun a => (a,none)

def retainedPrefixes (Δ : Bounds) (queries : List CompareTy) : List ModExpr :=
  literalPrefixes (queryAccesses Δ (queryPairs queries))

def retainedFrozen (Δ : Bounds) (queries : List CompareTy) : List CompareTy :=
  frozenKeys (queryAccesses Δ (queryPairs queries))

def rowBound (Δ : Bounds) (names : List ModVar) (tags : Nat) : Nat :=
  (ComparisonFiniteControlEncoding.labels Δ names).length * tags ^ 3

def Candidate.canonicalize {Δ : Bounds} {names : List ModVar}
    (C : Candidate Δ names) (queries : List CompareTy) : Candidate Δ names :=
  ((C.restrictMachine (inputTypes Δ queries)).restrictQueries (queryPairs queries)).canonicalizeRows

/-- The remaining certificate fields range over fixed input-name lists,
finite Boolean arrays, and row lists of explicitly bounded length. -/
structure CanonicalFor {Δ : Bounds} {names : List ModVar}
    (queries : List CompareTy) (C : Candidate Δ names) : Prop where
  types_eq : C.types = inputTypes Δ queries
  modes_eq : C.modes = names
  atoms_length : ∀ i, (C.machine i).atoms.length = (inputTypes Δ queries).length
  mode_values_length : ∀ i, (C.machine i).modes.length = names.length
  prodRows_length : C.prodRows.length ≤ rowBound Δ names C.tags
  sumRows_length : C.sumRows.length ≤ rowBound Δ names C.tags
  fnRows_length : C.fnRows.length ≤ rowBound Δ names C.tags
  prodLiterals_length : C.prodLiterals.length ≤ (retainedPrefixes Δ queries).length
  sumLiterals_length : C.sumLiterals.length ≤ (retainedPrefixes Δ queries).length
  prodLiteralRows_length : ∀ row ∈ C.prodLiterals, row.2.length ≤ rowBound Δ names C.tags
  sumLiteralRows_length : ∀ row ∈ C.sumLiterals, row.2.length ≤ rowBound Δ names C.tags
  prodLiterals_keys : ∀ row ∈ C.prodLiterals, row.1 ∈ retainedPrefixes Δ queries
  sumLiterals_keys : ∀ row ∈ C.sumLiterals, row.1 ∈ retainedPrefixes Δ queries
  frozen_length : C.frozen.length ≤ (retainedFrozen Δ queries).length
  frozen_keys : ∀ row ∈ C.frozen, row.1 ∈ retainedFrozen Δ queries

end ModalityInference.ComparisonFiniteCertificate
