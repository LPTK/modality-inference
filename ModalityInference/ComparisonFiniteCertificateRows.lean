import ModalityInference.ComparisonFiniteCertificate

/-! Canonical row tables enumerate the finite row universe and retain exactly
the rows present in the supplied table. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonFiniteControlEncoding ComparisonExecutableTables

def canonicalRows {Δ : Bounds} {names : List ModVar} {tags : Nat}
    (rows : List (Row (Code Δ names) (Fin tags))) : List (Row (Code Δ names) (Fin tags)) :=
  (allRows (indices Δ names) (List.finRange tags)).filter fun row => decide (row ∈ rows)

def Candidate.canonicalizeRows {Δ : Bounds} {names : List ModVar}
    (C : Candidate Δ names) : Candidate Δ names :=
  { C with
    prodRows := canonicalRows C.prodRows
    sumRows := canonicalRows C.sumRows
    fnRows := canonicalRows C.fnRows
    prodLiterals := C.prodLiterals.map fun row => (row.1, canonicalRows row.2)
    sumLiterals := C.sumLiterals.map fun row => (row.1, canonicalRows row.2) }

end ModalityInference.ComparisonFiniteCertificate
