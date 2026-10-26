import ModalityInference.Proofs.ComparisonFiniteCertificateSource
import ModalityInference.Proofs.ComparisonFiniteCertificateQueries
import ModalityInference.Proofs.ComparisonFiniteCertificateSoundness

/-! The finite separating models serialize to certificates accepted by the
actual Boolean checker. Reflection covers raw endpoints and defined internal
endpoints, in all four combinations, under the explicit shape hypothesis. -/
namespace ModalityInference.ComparisonFiniteCertificate.Completeness

open ComparisonFiniteCertificateQueries ComparisonObserverShadowModel ComparisonRawHeadTrace

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)

theorem of_model_nonrelation (raw : List Ty) (queries : List CompareTy) {a b : CompareTy}
    (hab : ¬ (ComparisonFiniteCertificateQueries.model hn raw queries).Related a b) :
    ∃ names, ∃ C : Candidate Δ names, C.separates a b = true := by
  let R := realization hn raw queries
  let T := table hn raw queries
  let sites := ComparisonObserverShadowQuerySupport.sites Δ raw queries
  obtain ⟨tags,observations,S,hS⟩ := SourceConstruction.exists_source R T
    (context_names Δ sites) sites (siteTag R) (description hn raw queries)
  refine ⟨_,S.candidate,S.separates_of_not_related ?_ ?_⟩
  · intro x y hxy
    exact (hS _ _).mpr (sound hn raw queries (.shaped (.bound hxy)))
  · exact fun h => hab ((hS a b).mp h)

include hn

theorem raw_non_subtype_iff (a b : Ty) :
    ¬ AlgebraSubtype Δ (.ofTy a) (.ofTy b) ↔
      ∃ names, ∃ C : Candidate Δ names, C.separates (.ofTy a) (.ofTy b) = true := by
  constructor
  · intro hab
    apply of_model_nonrelation hn [a,b] []
    intro h
    exact hab ((ComparisonFiniteCertificateQueries.raw_iff hn [a,b] []
      (a := a) (b := b) (by simp) (by simp)).mp h)
  · rintro ⟨names,C,h⟩
    exact C.separates_sound h

theorem defined_non_subtype_iff (a b : CompareTy) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ a b ↔ ∃ names, ∃ C : Candidate Δ names, C.separates a b = true := by
  constructor
  · intro hab
    apply of_model_nonrelation hn [] [a,b]
    intro h
    exact hab ((ComparisonFiniteCertificateQueries.defined_iff hn [] [a,b]
      (a := a) (b := b) (by simp) (by simp) ha hb).mp h)
  · rintro ⟨names,C,h⟩
    exact C.separates_sound h

theorem defined_raw_non_subtype_iff (a : CompareTy) (b : Ty) (ha : a.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ a (.ofTy b) ↔
      ∃ names, ∃ C : Candidate Δ names, C.separates a (.ofTy b) = true := by
  constructor
  · intro hab
    apply of_model_nonrelation hn [b] [a]
    intro h
    exact hab ((ComparisonFiniteCertificateQueries.defined_raw_iff hn [b] [a]
      (a := a) (b := b) (by simp) (by simp) ha).mp h)
  · rintro ⟨names,C,h⟩
    exact C.separates_sound h

theorem raw_defined_non_subtype_iff (a : Ty) (b : CompareTy) (hb : b.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ (.ofTy a) b ↔
      ∃ names, ∃ C : Candidate Δ names, C.separates (.ofTy a) b = true := by
  constructor
  · intro hab
    apply of_model_nonrelation hn [a] [b]
    intro h
    exact hab ((ComparisonFiniteCertificateQueries.raw_defined_iff hn [a] [b]
      (a := a) (b := b) (by simp) (by simp) hb).mp h)
  · rintro ⟨names,C,h⟩
    exact C.separates_sound h

end ModalityInference.ComparisonFiniteCertificate.Completeness
