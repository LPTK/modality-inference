import ModalityInference.Proofs.ComparisonSelectedRealizer
import ModalityInference.Proofs.ComparisonShapeSelectionBounds
import ModalityInference.Proofs.ComparisonPreparedCarrierNormalization
import ModalityInference.Proofs.ComparisonShapeRetractionSupport

namespace ModalityInference.ComparisonShapeRetraction

open ComparisonShapeSolver ComparisonSkeleton ComparisonWitnessRestriction ComparisonPreparation

theorem inputTypes_bounded (ambient : Bounds) (source target : Scheme) {v : TypeVar}
    (hv : v ∈ inputTypes (SchemePreparation.prepare ambient source target)) :
    v.index < (SchemePreparation.prepare ambient source target).nextType := by
  simp only [inputTypes, Finset.mem_union] at hv
  rcases hv with ((hv | hv) | hv) | hv
  · exact ((Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_assumptions_bounded ambient source target)).1 v hv
  · exact ((Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceBounds_bounded ambient source target)).1 v hv
  · exact ((TypeExpr.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_sourceType_bounded ambient source target)).1 v hv
  · exact ((TypeExpr.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_targetType_bounded ambient source target)).1 v hv

variable {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {σ : CompareSubstitution}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved solved))
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)

def selectedImage (v : TypeVar) : CompareTy :=
  let p := SchemePreparation.prepare ambient source target
  if hv : v.index < p.nextType then
    Cut.templateType (shapeChoices p solved) (normalizedRealizer p σ solved) (solved.resolveAll v)
      (prepared_template_valid h σ _) (σ.type v) (hw.1.2.1.type v) (hw.2.1.types v)
      (normalizedRealizer_realizes h hw.1 v hv)
  else σ.type v

theorem selectedImage_shaped (v : TypeVar) :
    (selectedImage h hw v).WellShaped (SchemePreparation.prepare ambient source target).assumptions := by
  unfold selectedImage
  dsimp only
  split
  · exact Cut.templateType_shaped _ _ _ _ _ _ _ _
  · exact hw.1.2.1.type v

theorem selectedImage_defined (v : TypeVar) :
    (selectedImage h hw v).DefinedUnder (SchemePreparation.prepare ambient source target).assumptions := by
  unfold selectedImage
  dsimp only
  split
  · exact Cut.templateType_defined _ _ _ _ _ _ _ _
  · exact hw.2.1.types v

def selectedAction : CompareSubstitution :=
  ComparisonPartialCarrier.reimage σ (selectedImage h hw)

theorem selectedAction_keys : (selectedAction h hw).types.map Prod.fst = σ.types.map Prod.fst :=
  ComparisonPartialCarrier.reimage_keys σ _

theorem selectedAction_modes : (selectedAction h hw).modes = σ.modes := rfl

theorem selectedAction_mode (v : ModVar) : (selectedAction h hw).mode v = σ.mode v := by
  cases v <;> rfl

theorem selectedAction_shaped :
    (selectedAction h hw).WellShaped (SchemePreparation.prepare ambient source target).assumptions :=
  ComparisonPartialCarrier.reimage_wellShaped (selectedImage_shaped h hw)

theorem selectedAction_domains :
    (selectedAction h hw).DomainsAbove (SchemePreparation.prepare ambient source target).firstType
      (SchemePreparation.prepare ambient source target).firstMode :=
  ComparisonPartialCarrier.reimage_domainsAbove hw.1.1 _

theorem selectedAction_defined :
    (selectedAction h hw).WellFormedUnder
      (SchemePreparation.prepare ambient source target).assumptions := by
  constructor
  · intro v
    rcases ComparisonPartialCarrier.reimage_type_cases σ (selectedImage h hw) v with he | he
    · change ((ComparisonPartialCarrier.reimage σ (selectedImage h hw)).type v).DefinedUnder _
      rw [he]
      exact selectedImage_defined h hw v
    · change ((ComparisonPartialCarrier.reimage σ (selectedImage h hw)).type v).DefinedUnder _
      rw [he.1]
      exact hw.2.1.types v
  · intro v
    rw [selectedAction_mode h hw]
    exact hw.2.1.modes v

theorem selectedImage_of_var (v : TypeVar)
    (hn : v ∈ inputTypes (SchemePreparation.prepare ambient source target))
    (he : σ.type v = .var v) : selectedImage h hw v = σ.type v := by
  unfold selectedImage
  dsimp only
  split
  · rename_i hv
    exact Cut.templateType_of_retained _ _ _ _ _ _ _ _
      (retained_variable_image h hw.1 v hv hn he)
  · rfl

theorem selectedAction_type_of_input (v : TypeVar)
    (hn : v ∈ inputTypes (SchemePreparation.prepare ambient source target)) :
    (selectedAction h hw).type v = selectedImage h hw v := by
  rcases ComparisonPartialCarrier.reimage_type_cases σ (selectedImage h hw) v with he | he
  · exact he
  · exact he.1.trans (selectedImage_of_var h hw v hn he.2).symm

theorem selectedAction_selected :
    let p := SchemePreparation.prepare ambient source target
    Selected (shapeChoices p solved) (normalizedRealizer p σ solved)
      (prepared_template_valid h σ) solved.resolveAll σ (selectedAction h hw) (inputTypes p) := by
  refine ⟨hw.1.2.1, ?_, ?_, selectedAction_mode h hw⟩
  · intro v hv
    exact normalizedRealizer_realizes h hw.1 v (inputTypes_bounded ambient source target hv)
  · intro v hv hd
    rw [selectedAction_type_of_input h hw v hv]
    simp only [selectedImage, dif_pos (inputTypes_bounded ambient source target hv)]

/-- Shape selection preserves the entire prepared comparison under the
unchanged declared bounds, including every original definedness guard. -/
theorem selectedAction_prepared :
    PreparedWitnessUnder (SchemePreparation.prepare ambient source target) (selectedAction h hw) := by
  have hs := selectedAction_selected h hw
  refine ⟨⟨selectedAction_domains h hw, selectedAction_shaped h hw, ?_, ?_⟩,
    selectedAction_defined h hw, ?_⟩
  · apply hs.bounds _ (fun _ hv => by simp [inputTypes, hv])
    · intro pair hp
      exact (prepare_sound h).2 pair (List.mem_append_left _ hp)
    · exact hw.1.2.2.1
  · exact hs.body (fun _ hv => by simp [inputTypes, hv])
      (retained_source_body h hw.1) hw.2.2 hw.1.2.2.2
  · exact hs.ty_defined _ (fun _ hv => by simp [inputTypes, hv]) hw.2.2

theorem selectedAction_shape {v : TypeVar}
    (hv : v ∈ inputTypes (SchemePreparation.prepare ambient source target)) :
    let p := SchemePreparation.prepare ambient source target
    ComparisonShape.Equivalent p.assumptions ((selectedAction h hw).type v).shape
      ((solved.resolveAll v).subst (choose (shapeChoices p solved) (normalizedRealizer p σ solved))) :=
  (selectedAction_selected h hw).type_shape hv (hw.2.1.types v)

theorem selectedImage_support {P : TypeVar → Prop} {Q : ModVar → Prop} (v : TypeVar)
    (hs : ComparisonInterpolation.Supports P Q (σ.type v)) :
    ComparisonInterpolation.Supports P Q (selectedImage h hw v) := by
  unfold selectedImage
  dsimp only
  split
  · exact Cut.templateType_support _ _ _ _ _ _ _ _ hs
  · exact hs

theorem selectedAction_supported
    (hs : Supported (SchemePreparation.prepare ambient source target) σ) :
    Supported (SchemePreparation.prepare ambient source target) (selectedAction h hw) := by
  refine ⟨?_, hs.2⟩
  rintro entry he
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
  apply selectedImage_support h hw
  cases hl : σ.types.lookup n with
  | none =>
    obtain ⟨entry, he, hn⟩ := List.mem_map.mp hn
    have hh := List.lookup_eq_none_iff.mp hl entry he
    simp [hn] at hh
  | some a =>
    obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp hl
    simpa only [CompareSubstitution.type, hl, Option.getD_some] using hs.1 (n, a) (by simp [hx])

end ModalityInference.ComparisonShapeRetraction
