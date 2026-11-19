import ModalityInference.Proofs.ComparisonFiniteCertificateBoundedCompleteness
import ModalityInference.Proofs.ComparisonFiniteCertificateCanonical

/-! Separating certificates admit a canonical representation with input-bounded
dimensions and lists. Original raw bounds and endpoint guards are preserved. -/
namespace ModalityInference.ComparisonFiniteCertificate.CanonicalCompleteness

open ComparisonFiniteCertificateBounds

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)

theorem bounded_iff_canonical (raw : List Ty) (queries : List CompareTy) {a b : CompareTy}
    (ha : a ∈ raw.map CompareTy.ofTy ++ queries) (hb : b ∈ raw.map CompareTy.ofTy ++ queries) :
    (∃ names, ∃ C : Candidate Δ names, WithinDimensions raw queries C ∧ C.separates a b = true) ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions raw queries C ∧ CanonicalFor (raw.map CompareTy.ofTy ++ queries) C ∧
          C.separates a b = true :=
  ⟨fun ⟨names,C,hC,hsep⟩ => ⟨names,C.canonicalize (raw.map CompareTy.ofTy ++ queries),
    (C.canonicalize_withinDimensions _ raw queries).mpr hC,
    C.canonicalize_canonicalFor _,C.canonicalize_separates _ ha hb hsep⟩,
    fun ⟨names,C,hC,_,hsep⟩ => ⟨names,C,hC,hsep⟩⟩

theorem of_model_nonrelation (raw : List Ty) (queries : List CompareTy) {a b : CompareTy}
    (ha : a ∈ raw.map CompareTy.ofTy ++ queries) (hb : b ∈ raw.map CompareTy.ofTy ++ queries)
    (hab : ¬ (ComparisonFiniteCertificateQueries.model hn raw queries).Related a b) :
    ∃ names, ∃ C : Candidate Δ names,
      WithinDimensions raw queries C ∧ CanonicalFor (raw.map CompareTy.ofTy ++ queries) C ∧
        C.separates a b = true :=
  (bounded_iff_canonical raw queries ha hb).mp
    (BoundedCompleteness.of_model_nonrelation hn raw queries hab)

include hn

theorem raw_non_subtype_iff (a b : Ty) :
    ¬ AlgebraSubtype Δ (.ofTy a) (.ofTy b) ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions [a,b] [] C ∧ CanonicalFor [.ofTy a,.ofTy b] C ∧
          C.separates (.ofTy a) (.ofTy b) = true :=
  (BoundedCompleteness.raw_non_subtype_iff hn a b).trans
    (bounded_iff_canonical [a,b] [] (by simp) (by simp))

theorem defined_non_subtype_iff (a b : CompareTy) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ a b ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions [] [a,b] C ∧ CanonicalFor [a,b] C ∧ C.separates a b = true :=
  (BoundedCompleteness.defined_non_subtype_iff hn a b ha hb).trans
    (bounded_iff_canonical [] [a,b] (by simp) (by simp))

theorem defined_raw_non_subtype_iff (a : CompareTy) (b : Ty) (ha : a.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ a (.ofTy b) ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions [b] [a] C ∧ CanonicalFor [.ofTy b,a] C ∧
          C.separates a (.ofTy b) = true :=
  (BoundedCompleteness.defined_raw_non_subtype_iff hn a b ha).trans
    (bounded_iff_canonical [b] [a] (by simp) (by simp))

theorem raw_defined_non_subtype_iff (a : Ty) (b : CompareTy) (hb : b.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ (.ofTy a) b ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions [a] [b] C ∧ CanonicalFor [.ofTy a,b] C ∧
          C.separates (.ofTy a) b = true :=
  (BoundedCompleteness.raw_defined_non_subtype_iff hn a b hb).trans
    (bounded_iff_canonical [a] [b] (by simp) (by simp))

end ModalityInference.ComparisonFiniteCertificate.CanonicalCompleteness
