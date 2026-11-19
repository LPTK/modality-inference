import ModalityInference.ComparisonFiniteCertificateCanonical
import ModalityInference.ComparisonFiniteCertificateBounds
import ModalityInference.Proofs.ComparisonFiniteCertificateMachineRestriction
import ModalityInference.Proofs.ComparisonFiniteCertificateRestriction
import ModalityInference.Proofs.ComparisonFiniteCertificateRows

/-! Composing machine-name restriction, query-key restriction, and row
canonicalization preserves accepted separators and bounds every list field. -/
namespace ModalityInference.ComparisonFiniteCertificate.Candidate

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names) (queries : List CompareTy)

theorem canonicalize_canonicalFor : CanonicalFor queries (C.canonicalize queries) := by
  let R := (C.restrictMachine (inputTypes Δ queries)).restrictQueries (queryPairs queries)
  refine ⟨rfl, rfl, ?_, ?_, R.canonicalizeRows_prodRows_length,
    R.canonicalizeRows_sumRows_length, R.canonicalizeRows_fnRows_length, ?_, ?_,
    (fun _ h => R.canonicalizeRows_prodLiteralRows_length h),
    (fun _ h => R.canonicalizeRows_sumLiteralRows_length h), ?_, ?_, ?_, ?_⟩
  · exact fun i => C.restrictMachine_atoms_length (inputTypes Δ queries) i
  · exact fun i => C.restrictMachine_modes_length (inputTypes Δ queries) i
  · simpa only [canonicalize, canonicalizeRows, List.length_map] using
      (C.restrictMachine (inputTypes Δ queries)).restrictQueries_prodLiterals_length_le
        (queryPairs queries)
  · simpa only [canonicalize, canonicalizeRows, List.length_map] using
      (C.restrictMachine (inputTypes Δ queries)).restrictQueries_sumLiterals_length_le
        (queryPairs queries)
  · intro row hrow
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hrow
    exact (C.restrictMachine (inputTypes Δ queries)).restrictQueries_prodLiterals_key_mem
      (queryPairs queries) (row := original) horiginal
  · intro row hrow
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hrow
    exact (C.restrictMachine (inputTypes Δ queries)).restrictQueries_sumLiterals_key_mem
      (queryPairs queries) (row := original) horiginal
  · exact (C.restrictMachine (inputTypes Δ queries)).restrictQueries_frozen_length_le
      (queryPairs queries)
  · exact fun _ h => (C.restrictMachine (inputTypes Δ queries)).restrictQueries_frozen_key_mem
      (queryPairs queries) h

theorem canonicalize_check (h : C.check = true) : (C.canonicalize queries).check = true := by
  exact ((C.restrictMachine (inputTypes Δ queries)).restrictQueries
    (queryPairs queries)).canonicalizeRows_check.trans
      ((C.restrictMachine (inputTypes Δ queries)).restrictQueries_check
        (queryPairs queries) (C.restrictMachine_check queries h))

theorem canonicalize_separates {a b : CompareTy} (ha : a ∈ queries) (hb : b ∈ queries)
    (h : C.separates a b = true) : (C.canonicalize queries).separates a b = true := by
  exact (((C.restrictMachine (inputTypes Δ queries)).restrictQueries
    (queryPairs queries)).canonicalizeRows_separates a b).trans
      ((C.restrictMachine (inputTypes Δ queries)).restrictQueries_separates
        (queryPairs queries) (List.mem_map.mpr ⟨a,ha,rfl⟩) (List.mem_map.mpr ⟨b,hb,rfl⟩)
          (C.restrictMachine_separates queries ha hb h))

@[simp] theorem canonicalize_states : (C.canonicalize queries).states = C.states := rfl

@[simp] theorem canonicalize_tags : (C.canonicalize queries).tags = C.tags := rfl

@[simp] theorem canonicalize_observations :
    (C.canonicalize queries).observations = C.observations := rfl

theorem canonicalize_withinDimensions (raw : List Ty) (definedQueries : List CompareTy) :
    ComparisonFiniteCertificateBounds.WithinDimensions raw definedQueries (C.canonicalize queries) ↔
      ComparisonFiniteCertificateBounds.WithinDimensions raw definedQueries C := Iff.rfl

end ModalityInference.ComparisonFiniteCertificate.Candidate
