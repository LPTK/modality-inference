import ModalityInference.ComparisonFiniteCertificateBounds
import ModalityInference.Proofs.ComparisonFiniteCertificateDimensions
import ModalityInference.Proofs.ComparisonFiniteCertificateSupport
import ModalityInference.Proofs.ComparisonFiniteCertificateQuerySize
import ModalityInference.Proofs.ComparisonFiniteCertificateDiagramSupport

/-! Explicit input bounds for the realized finite comparison certificate. -/
namespace ModalityInference.ComparisonFiniteCertificateBounds

open ComparisonFiniteControlEncoding ComparisonRawHeadTrace

theorem controlBound_mono : Monotone controlBound := by
  intro a b h
  exact Nat.pow_le_pow_right (by decide)
    (Nat.add_le_add (Nat.pow_le_pow_right (by decide) h)
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 h))))

theorem labels_length_le (Δ : Bounds) (names : List ModVar) :
    (labels Δ names).length ≤ controlBound names.length := by
  exact (List.pwFilter_sublist (ComparisonControlForms.representatives names)).length_le.trans_eq
    (ComparisonControlForms.representatives_length names)

theorem source_names_length (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    (modeNames Δ (ComparisonObserverShadowQuerySupport.sites Δ raw queries)).length ≤
      nameBound Δ raw queries :=
  (ComparisonFiniteCertificateSupport.input_modeNames_length Δ raw queries).trans
    (Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_left 2
      (ComparisonFiniteCertificateQuerySize.sites_length Δ raw queries)) 1))

theorem source_labels_length (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    (labels Δ (modeNames Δ (ComparisonObserverShadowQuerySupport.sites Δ raw queries))).length ≤
      controlsBound Δ raw queries :=
  (labels_length_le _ _).trans (controlBound_mono (source_names_length Δ raw queries))

theorem source_control_card (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    Nat.card (ComparisonFiniteControls.Control Δ
      (modeNames Δ (ComparisonObserverShadowQuerySupport.sites Δ raw queries))) ≤
      controlsBound Δ raw queries := by
  rw [ComparisonFiniteCertificate.Dimensions.control_card]
  exact source_labels_length Δ raw queries

theorem realization_count_le {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (raw : List Ty) (queries : List CompareTy) :
    (ComparisonFiniteCertificateQueries.realization hn raw queries).count ≤ stateBound Δ raw queries := by
  let sites := ComparisonObserverShadowQuerySupport.sites Δ raw queries
  let names := modeNames Δ sites
  letI : Fintype (ComparisonFiniteControls.Control Δ names) := Fintype.ofFinite _
  let B := ComparisonRawHeadTrace.boundary Δ sites
  let base := ComparisonObserverShadowAnchorRows.freshBase (rawHeads sites)
  let extra := ComparisonObserverShadowModel.RawInput.extraRows hn
    (ComparisonObserverShadowQuerySupport.rawInputs raw queries)
  have hc := (ComparisonObserverShadowQueryDescriptions.exists_realization hn B names base extra queries).choose_spec.1
  apply hc.trans
  apply Nat.pow_le_pow_right (by decide)
  apply Nat.add_le_add
  · apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_left
    apply Finset.card_le_card
    apply ComparisonFiniteCertificate.DiagramSupport.diagram_names Finset.subset_union_left
      (ComparisonFiniteCertificateSupport.input_modeNames_support Δ raw queries)
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact ComparisonFiniteCertificate.DiagramSupport.anchor_rows_modes
          (ComparisonFiniteCertificateSupport.rawHeads_support
            (ComparisonFiniteCertificateSupport.sites_input_support Δ raw queries)) hr
      · exact ComparisonFiniteCertificate.DiagramSupport.constructor_rows_modes
          (ComparisonFiniteCertificateSupport.input_modeNames_support Δ raw queries) hr
    · intro a ha
      exact (ComparisonObserverBoundary.modes_subset (List.mem_append_right _ ha)).trans
        Finset.subset_union_right
  · exact ComparisonFiniteCertificateQuerySize.source_boundary_length hn raw queries
      (controlsBound Δ raw queries) (by
        simpa only [Nat.card_eq_fintype_card] using source_control_card Δ raw queries)

end ModalityInference.ComparisonFiniteCertificateBounds
