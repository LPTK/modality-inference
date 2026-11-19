import ModalityInference.ComparisonFiniteCertificateCanonical

/-! Dense certificate tables use every input-derived literal and frozen key.
Missing entries carry the interpreter's empty-table or bottom default. -/
namespace ModalityInference.ComparisonFiniteCertificate

def Candidate.densify {Δ : Bounds} {names : List ModVar}
    (C : Candidate Δ names) (queries : List CompareTy) : Candidate Δ names :=
  { C with
    prodRows := canonicalRows C.prodRows
    sumRows := canonicalRows C.sumRows
    fnRows := canonicalRows C.fnRows
    prodLiterals := (retainedPrefixes Δ queries).map fun p =>
      (p, canonicalRows (C.prodAt (some p)))
    sumLiterals := (retainedPrefixes Δ queries).map fun p =>
      (p, canonicalRows (C.sumAt (some p)))
    frozen := (retainedFrozen Δ queries).map fun a => (a, C.data.frozenValue a) }

end ModalityInference.ComparisonFiniteCertificate
