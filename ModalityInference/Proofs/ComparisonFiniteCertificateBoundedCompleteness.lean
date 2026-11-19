import ModalityInference.Proofs.ComparisonFiniteCertificateBounds
import ModalityInference.Proofs.ComparisonFiniteCertificateCompleteness

/-! Separating certificates can be chosen within input-derived carrier and
control-name bounds. This does not bound the structural rank of unknown images. -/
namespace ModalityInference.ComparisonFiniteCertificate.BoundedCompleteness

open ComparisonFiniteCertificateQueries ComparisonObserverShadowModel ComparisonRawHeadTrace
  ComparisonFiniteCertificateBounds

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)

theorem of_model_nonrelation (raw : List Ty) (queries : List CompareTy) {a b : CompareTy}
    (hab : ¬ (ComparisonFiniteCertificateQueries.model hn raw queries).Related a b) :
    ∃ names, ∃ C : Candidate Δ names,
      WithinDimensions raw queries C ∧ C.separates a b = true := by
  let R := realization hn raw queries
  let T := table hn raw queries
  let sites := ComparisonObserverShadowQuerySupport.sites Δ raw queries
  obtain ⟨tags,observations,ht,ho,S,hS⟩ := Dimensions.exists_source_bounded R T
    (context_names Δ sites) sites (siteTag R) (description hn raw queries)
  refine ⟨_,S.candidate,?_,S.separates_of_not_related ?_ ?_⟩
  · have hh : (boundary Δ sites).heads.length ≤ inputNodes Δ raw queries := by
      simpa only [boundary,ComparisonRawHeadFiniteOrbits.Boundary.ofRaw,rawHeads,List.length_map]
        using ComparisonFiniteCertificateQuerySize.sites_length Δ raw queries
    have ht' : Dimensions.tagBound Δ (modeNames Δ sites) (boundary Δ sites).heads.length R.count ≤
        tagsBound Δ raw queries :=
      Nat.add_le_add (Nat.pow_le_pow_right (by decide) (realization_count_le hn raw queries))
        (Nat.mul_le_mul hh (source_labels_length Δ raw queries))
    exact ⟨source_names_length Δ raw queries,
      ComparisonFiniteCertificateSupport.input_modeNames_support Δ raw queries,
      realization_count_le hn raw queries,ht.trans ht',
      ho.trans (Nat.pow_le_pow_right (by decide) ht')⟩
  · intro x y hxy
    exact (hS _ _).mpr (sound hn raw queries (.shaped (.bound hxy)))
  · exact fun h => hab ((hS a b).mp h)

include hn

theorem raw_non_subtype_iff (a b : Ty) :
    ¬ AlgebraSubtype Δ (.ofTy a) (.ofTy b) ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions [a,b] [] C ∧ C.separates (.ofTy a) (.ofTy b) = true :=
  ⟨fun hab => of_model_nonrelation hn [a,b] [] (fun h => hab
    ((ComparisonFiniteCertificateQueries.raw_iff hn [a,b] []
      (a := a) (b := b) (by simp) (by simp)).mp h)),
    fun ⟨_,C,_,h⟩ => C.separates_sound h⟩

theorem defined_non_subtype_iff (a b : CompareTy) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ a b ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions [] [a,b] C ∧ C.separates a b = true :=
  ⟨fun hab => of_model_nonrelation hn [] [a,b] (fun h => hab
    ((ComparisonFiniteCertificateQueries.defined_iff hn [] [a,b]
      (a := a) (b := b) (by simp) (by simp) ha hb).mp h)),
    fun ⟨_,C,_,h⟩ => C.separates_sound h⟩

theorem defined_raw_non_subtype_iff (a : CompareTy) (b : Ty) (ha : a.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ a (.ofTy b) ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions [b] [a] C ∧ C.separates a (.ofTy b) = true :=
  ⟨fun hab => of_model_nonrelation hn [b] [a] (fun h => hab
    ((ComparisonFiniteCertificateQueries.defined_raw_iff hn [b] [a]
      (a := a) (b := b) (by simp) (by simp) ha).mp h)),
    fun ⟨_,C,_,h⟩ => C.separates_sound h⟩

theorem raw_defined_non_subtype_iff (a : Ty) (b : CompareTy) (hb : b.DefinedUnder Δ) :
    ¬ AlgebraSubtype Δ (.ofTy a) b ↔
      ∃ names, ∃ C : Candidate Δ names,
        WithinDimensions [a] [b] C ∧ C.separates (.ofTy a) b = true :=
  ⟨fun hab => of_model_nonrelation hn [a] [b] (fun h => hab
    ((ComparisonFiniteCertificateQueries.raw_defined_iff hn [a] [b]
      (a := a) (b := b) (by simp) (by simp) hb).mp h)),
    fun ⟨_,C,_,h⟩ => C.separates_sound h⟩

end ModalityInference.ComparisonFiniteCertificate.BoundedCompleteness
