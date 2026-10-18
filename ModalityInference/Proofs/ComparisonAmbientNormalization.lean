import ModalityInference.ComparisonAmbientNormalization
import ModalityInference.Proofs.ComparisonRawContext
import ModalityInference.Proofs.SchemeInstance

namespace ModalityInference.ComparisonAmbientNormalization
open ComparisonRawContext

@[simp] theorem names_modes (Δ : Bounds) (η : ModVar → Mode) : ModeModels (names Δ) η := by
  intro c hc
  rcases List.mem_append.mp hc with hc|hc
  · obtain ⟨_,_,rfl⟩ := List.mem_map.mp hc
    trivial
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hc
    exact ⟨η v,η v,rfl,rfl,Mode.le_refl _⟩

@[simp] theorem names_shapes (Δ : Bounds) (ρ : TypeVar → ComparisonShape) :
    ComparisonShape.Models (names Δ) ρ := by
  intro p hp
  obtain ⟨c,hc,hp⟩ := List.mem_flatMap.mp hp
  rcases List.mem_append.mp hc with hc|hc
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hc
    obtain rfl := List.mem_singleton.mp hp
    rfl
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hc
    cases hp

@[simp] theorem modeModels_normalize (Δ : Bounds) (η : ModVar → Mode) :
    ModeModels (normalize Δ) η ↔ ModeModels Δ η := by
  simp only [normalize,ModeModels,List.mem_append,or_imp,forall_and]
  exact ⟨fun h => (modeModels_prune _ _).mp h.1,
    fun h => ⟨(modeModels_prune _ _).mpr h,names_modes _ _⟩⟩

@[simp] theorem shapeModels_normalize (Δ : Bounds) (ρ : TypeVar → ComparisonShape) :
    ComparisonShape.Models (normalize Δ) ρ ↔ ComparisonShape.Models Δ ρ := by
  simp only [normalize,ComparisonShape.Models,ComparisonShape.pairs,List.flatMap_append,
    List.mem_append,or_imp,forall_and]
  exact ⟨fun h => (shapeModels_prune _ _).mp h.1,
    fun h => ⟨(shapeModels_prune _ _).mpr h,names_shapes _ _⟩⟩

theorem forward (Δ : Bounds) : Hom Δ (normalize Δ) where
  modes η := (modeModels_normalize _ _).mp
  shapes ρ := (shapeModels_normalize _ _).mp
  bounds a b hb := by
    by_cases hab : a=b
    · subst b;exact .refl (CompareTy.wellShaped_ofTy _ _)
    · exact .shaped (.bound (List.mem_append_left _ (List.mem_filter.mpr
        ⟨hb,by simpa only [keep,decide_eq_true_eq]⟩)))

theorem backward (Δ : Bounds) : Hom (normalize Δ) Δ where
  modes η := (modeModels_normalize _ _).mpr
  shapes ρ := (shapeModels_normalize _ _).mpr
  bounds a b hb := by
    rcases List.mem_append.mp hb with hb|hb
    · exact .shaped (.bound (prune_subset _ hb))
    · rcases List.mem_append.mp hb with hb|hb
      · obtain ⟨v,_,he⟩ := List.mem_map.mp hb
        cases he
        exact .refl (CompareTy.wellShaped_ofTy _ _)
      · obtain ⟨v,_,he⟩ := List.mem_map.mp hb
        cases he

theorem typeVariables_names (Δ : Bounds) (v : TypeVar) :
    v∈(names Δ).typeVariables ↔ v∈Δ.typeVariables := by
  simp [names,Bounds.typeVariables,Constraint.typeVariables,TypeExpr.typeVariables,
    List.mem_flatMap,eq_comm]

theorem modeVariables_names (Δ : Bounds) (v : ModVar) :
    v∈(names Δ).modeVariables ↔ v∈Δ.modeVariables := by
  simp [names,Bounds.modeVariables,Constraint.modeVariables,TypeExpr.modeVariables,
    ModExpr.freeVariables,List.mem_flatMap,eq_comm]

theorem typeVariables_prune_subset (Δ : Bounds) : (prune Δ).typeVariables⊆Δ.typeVariables := by
  intro v hv
  simp only [Bounds.typeVariables,List.mem_dedup,List.mem_flatMap] at hv ⊢
  obtain ⟨c,hc,hv⟩ := hv
  exact ⟨c,prune_subset _ hc,hv⟩

theorem modeVariables_prune_subset (Δ : Bounds) : (prune Δ).modeVariables⊆Δ.modeVariables := by
  intro v hv
  simp only [Bounds.modeVariables,List.mem_dedup,List.mem_flatMap] at hv ⊢
  obtain ⟨c,hc,hv⟩ := hv
  exact ⟨c,prune_subset _ hc,hv⟩

@[simp] theorem typeVariables_normalize (Δ : Bounds) (v : TypeVar) :
    v∈(normalize Δ).typeVariables ↔ v∈Δ.typeVariables := by
  have he : v∈(normalize Δ).typeVariables ↔ v∈(prune Δ).typeVariables ∨
      v∈(names Δ).typeVariables := by
    simp only [normalize,Bounds.typeVariables,List.flatMap_append,List.mem_dedup,List.mem_append]
  rw [he,typeVariables_names]
  exact ⟨fun h => h.elim (fun hv => typeVariables_prune_subset Δ hv) id,Or.inr⟩

@[simp] theorem modeVariables_normalize (Δ : Bounds) (v : ModVar) :
    v∈(normalize Δ).modeVariables ↔ v∈Δ.modeVariables := by
  have he : v∈(normalize Δ).modeVariables ↔ v∈(prune Δ).modeVariables ∨
      v∈(names Δ).modeVariables := by
    simp only [normalize,Bounds.modeVariables,List.flatMap_append,List.mem_dedup,List.mem_append]
  rw [he,modeVariables_names]
  exact ⟨fun h => h.elim (fun hv => modeVariables_prune_subset Δ hv) id,Or.inr⟩

@[simp] theorem freshTypeIndex_normalize (Δ : Bounds) :
    (normalize Δ).freshTypeIndex=Δ.freshTypeIndex := by
  have he (n : Nat) : (normalize Δ).freshTypeIndex≤n ↔ Δ.freshTypeIndex≤n := by
    simp only [Bounds.freshTypeIndex,freshFold_le_iff,typeVariables_normalize]
  exact Nat.le_antisymm ((he _).mpr (Nat.le_refl _)) ((he _).mp (Nat.le_refl _))

@[simp] theorem freshModeIndex_normalize (Δ : Bounds) :
    (normalize Δ).freshModeIndex=Δ.freshModeIndex := by
  have he (n : Nat) : (normalize Δ).freshModeIndex≤n ↔ Δ.freshModeIndex≤n := by
    simp only [Bounds.freshModeIndex,freshFold_le_iff,modeVariables_normalize]
  exact Nat.le_antisymm ((he _).mpr (Nat.le_refl _)) ((he _).mp (Nat.le_refl _))

@[simp] theorem subsumptionIndices_normalize (Δ : Bounds) (source target : Scheme) :
    source.subsumptionIndices (normalize Δ) target=source.subsumptionIndices Δ target := by
  simp only [Scheme.subsumptionIndices,freshTypeIndex_normalize,freshModeIndex_normalize]


theorem hom_of_subset {Δ Γ : Bounds} (h : Δ⊆Γ) : Hom Δ Γ where
  modes _ hη c hc := hη c (h hc)
  shapes _ hρ p hp := by
    obtain ⟨c,hc,hp⟩ := List.mem_flatMap.mp hp
    exact hρ p (List.mem_flatMap.mpr ⟨c,h hc,hp⟩)
  bounds _ _ hb := .shaped (.bound (h hb))

theorem append_right {Δ Γ : Bounds} (h : Hom Δ Γ) (Θ : Bounds) : Hom (Δ++Θ) (Γ++Θ) where
  modes η hη c hc := by
    rcases List.mem_append.mp hc with hc|hc
    · exact h.modes η (fun c hc => hη c (List.mem_append_left _ hc)) c hc
    · exact hη c (List.mem_append_right _ hc)
  shapes ρ hρ p hp := by
    have he {A B : Bounds} : ComparisonShape.Models (A++B) ρ ↔
        ComparisonShape.Models A ρ ∧ ComparisonShape.Models B ρ := by
      simp only [ComparisonShape.Models,ComparisonShape.pairs,List.flatMap_append,
        List.mem_append,or_imp,forall_and]
    exact (he.mpr ⟨h.shapes ρ (he.mp hρ).1,(he.mp hρ).2⟩) p hp
  bounds a b hb := by
    rcases List.mem_append.mp hb with hb|hb
    · exact (hom_of_subset (Δ := Γ) (Γ := Γ++Θ)
        (fun _ hc => List.mem_append_left _ hc)).algebra (h.bounds a b hb)
    · exact .shaped (.bound (List.mem_append_right _ hb))

/-- Names retain exactly the original fresh indices, so only the prepared raw
assumptions change. Source/target renamings and all finite domains stay literal. -/
theorem prepare_eq (Δ : Bounds) (source target : Scheme) :
    SchemePreparation.prepare (normalize Δ) source target =
      {SchemePreparation.prepare Δ source target with
        assumptions := normalize Δ ++
          ((SchemePreparation.prepare Δ source target).targetRenaming.bounds target.bounds).assumptions} := by
  simp only [SchemePreparation.prepare,subsumptionIndices_normalize]

theorem prepared_forward (Δ : Bounds) (source target : Scheme) :
    Hom (SchemePreparation.prepare Δ source target).assumptions
      (SchemePreparation.prepare (normalize Δ) source target).assumptions := by
  simpa only [SchemePreparation.prepare,subsumptionIndices_normalize] using
    append_right (forward Δ)
      (((SchemePreparation.prepare Δ source target).targetRenaming.bounds target.bounds).assumptions)

theorem prepared_backward (Δ : Bounds) (source target : Scheme) :
    Hom (SchemePreparation.prepare (normalize Δ) source target).assumptions
      (SchemePreparation.prepare Δ source target).assumptions := by
  simpa only [SchemePreparation.prepare,subsumptionIndices_normalize] using
    append_right (backward Δ)
      (((SchemePreparation.prepare Δ source target).targetRenaming.bounds target.bounds).assumptions)

theorem prepared_witness_iff (Δ : Bounds) (source target : Scheme) (σ : CompareSubstitution) :
    ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare (normalize Δ) source target) σ ↔
      ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare Δ source target) σ := by
  constructor
  · intro h
    have hh := (prepared_backward Δ source target).witness h
    simpa only [SchemePreparation.prepare,subsumptionIndices_normalize] using hh
  · intro h
    have hh := (prepared_forward Δ source target).witness h
    simpa only [SchemePreparation.prepare,subsumptionIndices_normalize] using hh

theorem subsumes_iff (Δ : Bounds) (source target : Scheme) :
    AlgebraSubsumesUnder (normalize Δ) source target ↔ AlgebraSubsumesUnder Δ source target := by
  rw [ComparisonPreparation.prepare_algebra_under_iff,
    ComparisonPreparation.prepare_algebra_under_iff]
  exact exists_congr (prepared_witness_iff Δ source target)

@[simp] theorem normalize_nil : normalize []=[] := rfl

end ModalityInference.ComparisonAmbientNormalization
