import ModalityInference.Proofs.ComparisonRankedBasis
import ModalityInference.Proofs.ComparisonStructuralWitness

/-! A single finite generator level represents an entire admissible comparison
witness when the declared shape equations have no finite model. The replacement
retains every original guard, shared mode image, and substitution key. -/
namespace ModalityInference.ComparisonRankedBasis

open ComparisonAlgebra ComparisonControls ComparisonStructuralLattice
open ComparisonInterpolation ComparisonWitnessRestriction ComparisonPreparation

/-- Simultaneous normalization uses one finite generator level for all images.
The level is derived from the given finite witness, not from a semantic fixed
point or an input-only stopping bound. -/
theorem prepared_ranked_witness {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (hn : ¬∃ρ, ComparisonShape.Models p.assumptions ρ)
    (hw : PreparedWitnessUnder p σ) (hsp : Supported p σ) :
    ∃n τ, PreparedWitnessUnder p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧ τ.modes = σ.modes ∧
      Supported p τ ∧ ComparisonStructuralBasis.Replacement p.assumptions σ τ ∧
      ∀v∈inputTypes p,
        LatticeForm (basis (inputTypes p).toList (inputModes p).toList n).types (τ.type v) ∧
        Representable p.assumptions .unit (τ.type v) := by
  classical
  let names := (inputTypes p).toList
  let modes := (inputModes p).toList
  let n := (inputTypes p).sup (fun v => rank (σ.type v))
  have hnormal (v : TypeVar) (hv : v∈inputTypes p) :
      Normal p.assumptions names modes n (σ.type v) := by
    apply (normal_of_supported hn names modes (hw.2.1.types v)
      ((hsp.type hv).mono (fun _ h => Finset.mem_toList.mpr h)
        (fun _ h => Finset.mem_toList.mpr h))).mono
    exact Finset.le_sup (f := fun v => rank (σ.type v)) hv
  have hchoose : ∀v, ∃a, Equiv p.assumptions (σ.type v) a ∧
      a.DefinedUnder p.assumptions ∧
      (v∈inputTypes p → LatticeForm (basis names modes n).types a ∧
        Representable p.assumptions .unit a) ∧
      (v∉inputTypes p → a=σ.type v) := by
    intro v
    by_cases hv : v∈inputTypes p
    · obtain ⟨a, ha, har, hae⟩ := hnormal v hv
      exact ⟨a, hae, har.2.1, fun _ => ⟨ha,har⟩, fun h => (h hv).elim⟩
    · exact ⟨σ.type v, .refl (hw.1.2.1.type v), hw.2.1.types v,
        fun h => (hv h).elim, fun _ => rfl⟩
  choose images hi using hchoose
  let τ := ComparisonPartialCarrier.reimage σ images
  have hreplace : ComparisonStructuralBasis.Replacement p.assumptions σ τ := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
      · exact he ▸ (hi v).1
      · change Equiv p.assumptions (σ.type v) ((ComparisonPartialCarrier.reimage σ images).type v)
        rw [he.1]
        exact .refl (hw.1.2.1.type v)
    · intro v
      rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
      · exact he ▸ (hi v).2.1
      · exact he.1 ▸ hw.2.1.types v
    · intro v
      cases v <;> rfl
  have hshaped : τ.WellShaped p.assumptions :=
    ComparisonPartialCarrier.reimage_wellShaped (fun v => (hi v).1.1.wellShaped_right)
  have hsupported : Supported p τ := by
    refine ⟨?_, hsp.2⟩
    intro entry he
    change entry∈(σ.types.map Prod.fst).map (fun n => (n, images (.flex n))) at he
    obtain ⟨key, hk, rfl⟩ := List.mem_map.mp he
    by_cases hv : TypeVar.flex key∈inputTypes p
    · have hf := ((hi (.flex key)).2.2.1 hv).1
      exact (ComparisonStructuralBasis.lattice_support hf (types_support names modes n)).mono
        (fun _ h => Finset.mem_toList.mp h) (fun _ h => Finset.mem_toList.mp h)
    · change Supports (·∈inputTypes p) (·∈inputModes p) (images (.flex key))
      rw [(hi (.flex key)).2.2.2 hv]
      exact ComparisonStructuralBasis.supported_type_of_key hsp hk
  refine ⟨n, τ, hreplace.prepared rfl hw
    (ComparisonPartialCarrier.reimage_domainsAbove hw.1.1 images) hshaped,
    ComparisonPartialCarrier.reimage_keys σ images, rfl, hsupported, hreplace, ?_⟩
  intro v hv
  rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
  · change LatticeForm (basis names modes n).types ((ComparisonPartialCarrier.reimage σ images).type v) ∧ _
    rw [he]
    exact (hi v).2.2.1 hv
  · change LatticeForm (basis names modes n).types ((ComparisonPartialCarrier.reimage σ images).type v) ∧ _
    rw [he.1, he.2]
    have hatom : CompareTy.var v∈(basis names modes 0).heads := by
      simp only [basis, Basis.heads, List.mem_cons, List.mem_map]
      exact .inr (.inr ⟨v, Finset.mem_toList.mpr hv, rfl⟩)
    have ht := types_mono (names := names) (modes := modes) (Nat.zero_le n) (head_mem_types hatom)
    exact ⟨.atom ht, types_representable hn names modes n _ ht⟩

/-- No image-support hypothesis is imposed on an admissible witness: restriction
to the finite input names is performed once, before simultaneous normalization.
The resulting witness keeps exactly the original type and mode key lists. -/
theorem prepared_ranked_complete {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (hn : ¬∃ρ, ComparisonShape.Models p.assumptions ρ)
    (hw : PreparedWitnessUnder p σ) :
    ∃n τ, PreparedWitnessUnder p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧
      τ.modes.map Prod.fst = σ.modes.map Prod.fst ∧ Supported p τ ∧
      ∀v∈inputTypes p,
        LatticeForm (basis (inputTypes p).toList (inputModes p).toList n).types (τ.type v) ∧
        Representable p.assumptions .unit (τ.type v) := by
  obtain ⟨action, ha, ht, hm, hsp⟩ := prepared_supported_under hw
  obtain ⟨n, τ, hw, htypes, hmodes, hs, _, hnormal⟩ := prepared_ranked_witness hn ha hsp
  exact ⟨n, τ, hw, htypes.trans ht, by simpa only [hmodes] using hm, hs, hnormal⟩

/-- The common level exposes executable positive-CNF certificates for every
observed image. Their reconstructed finite terms are equivalent to the shared
admissible witness under the original declared bounds. -/
theorem prepared_polynomial_complete {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (hn : ¬∃ρ, ComparisonShape.Models p.assumptions ρ)
    (hw : PreparedWitnessUnder p σ) :
    ∃n τ, PreparedWitnessUnder p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧
      τ.modes.map Prod.fst = σ.modes.map Prod.fst ∧ Supported p τ ∧
      ∀v∈inputTypes p, ∃clauses t,
        Polynomial (basis (inputTypes p).toList (inputModes p).toList n) clauses ∧
        ComparisonLatticeCompiler.compile (basis (inputTypes p).toList (inputModes p).toList n)
          (τ.type v) = some clauses ∧
        ComparisonPropagation.reify (basis (inputTypes p).toList (inputModes p).toList n).types
          clauses = some t ∧ Representable p.assumptions .unit t ∧
        Equiv p.assumptions (τ.type v) t := by
  obtain ⟨n, τ, hw, ht, hm, hs, hnormal⟩ := prepared_ranked_complete hn hw
  refine ⟨n, τ, hw, ht, hm, hs, ?_⟩
  intro v hv
  obtain ⟨clauses, hc⟩ := ComparisonLatticeCompiler.compile_complete (hnormal v hv).1
  obtain ⟨t, htr, hrep, he⟩ := ComparisonLatticeCompiler.compile_correct
    (types_representable hn (inputTypes p).toList (inputModes p).toList n) hc
  exact ⟨clauses, t, (ComparisonLatticeCompiler.compile_polynomial hc).2, hc, htr, hrep, he.symm⟩

end ModalityInference.ComparisonRankedBasis
