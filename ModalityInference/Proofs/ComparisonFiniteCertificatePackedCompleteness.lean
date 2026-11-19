import ModalityInference.Proofs.ComparisonFiniteCertificatePacked
import ModalityInference.Proofs.ComparisonFiniteCertificateCanonicalCompleteness

/-! Each endpoint completeness theorem has a finite packed certificate form.
The original no-shape premise and internal endpoint guards are retained. -/
namespace ModalityInference.ComparisonFiniteCertificate.PackedCompleteness

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)

theorem of_model_nonrelation (raw : List Ty) (queries : List CompareTy) {a b : CompareTy}
    (ha : a ∈ raw.map CompareTy.ofTy ++ queries) (hb : b ∈ raw.map CompareTy.ofTy ++ queries)
    (hab : ¬ (ComparisonFiniteCertificateQueries.model hn raw queries).Related a b) :
    ∃ p : Packed.Certificate Δ raw queries, p.separates a b = true :=
  (Packed.exists_certificate_iff Δ raw queries a b).mp
    (CanonicalCompleteness.of_model_nonrelation hn raw queries ha hb hab)

include hn

theorem raw_non_subtype_iff (a b : Ty) :
    ¬ AlgebraSubtype Δ (.ofTy a) (.ofTy b) ↔
      ∃ p : Packed.Certificate Δ [a,b] [], p.separates (.ofTy a) (.ofTy b) = true :=
  (CanonicalCompleteness.raw_non_subtype_iff hn a b).trans
    (Packed.exists_certificate_iff Δ [a,b] [] (.ofTy a) (.ofTy b))

theorem defined_non_subtype_iff (a b : CompareTy) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ a b ↔
      ∃ p : Packed.Certificate Δ [] [a,b], p.separates a b = true :=
  (CanonicalCompleteness.defined_non_subtype_iff hn a b ha hb).trans
    (Packed.exists_certificate_iff Δ [] [a,b] a b)

theorem defined_raw_non_subtype_iff (a : CompareTy) (b : Ty) (ha : a.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ a (.ofTy b) ↔
      ∃ p : Packed.Certificate Δ [b] [a], p.separates a (.ofTy b) = true :=
  (CanonicalCompleteness.defined_raw_non_subtype_iff hn a b ha).trans
    (Packed.exists_certificate_iff Δ [b] [a] a (.ofTy b))

theorem raw_defined_non_subtype_iff (a : Ty) (b : CompareTy) (hb : b.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ (.ofTy a) b ↔
      ∃ p : Packed.Certificate Δ [a] [b], p.separates (.ofTy a) b = true :=
  (CanonicalCompleteness.raw_defined_non_subtype_iff hn a b hb).trans
    (Packed.exists_certificate_iff Δ [a] [b] (.ofTy a) b)

end ModalityInference.ComparisonFiniteCertificate.PackedCompleteness
