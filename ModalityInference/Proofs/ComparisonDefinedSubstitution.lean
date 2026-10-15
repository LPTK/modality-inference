import ModalityInference.Proofs.ComparisonTypes

/-! Defined comparison images retain symbolic modality expressions together
with the ambient guards needed to interpret them. -/
namespace ModalityInference

theorem CompareSubstitution.wellFormedUnder_of_images {σ : CompareSubstitution} {Δ : Bounds}
    (ht : ∀ entry ∈ σ.types, entry.2.DefinedUnder Δ)
    (hm : ∀ entry ∈ σ.modes, Entails Δ (.defined entry.2)) :
    σ.WellFormedUnder Δ := by
  constructor
  · rintro (n | n)
    · cases he : σ.types.lookup n with
      | none => simp [type, he, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
      | some a =>
        obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
        simpa only [type, he, Option.getD_some] using ht (n, a) (by simp [hx])
    · simp [type, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
  · rintro (n | n)
    · cases he : σ.modes.lookup n with
      | none => simp [mode, he, Entails, ModExpr.WellFormed, ModExpr.eval]
      | some m =>
        obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
        simpa only [mode, he, Option.getD_some] using hm (n, m) (by simp [hx])
    · simp [mode, Entails, ModExpr.WellFormed, ModExpr.eval]

theorem Substitution.WellFormedUnder.to_compare {σ : Substitution} {Δ : Bounds}
    (h : σ.WellFormedUnder Δ) : (CompareSubstitution.ofSubstitution σ).WellFormedUnder Δ := by
  constructor
  · intro v
    simpa only [CompareSubstitution.ofSubstitution_type, CompareTy.definedUnder_ofTy] using h.types v
  · exact h.modes

theorem InstantiatesUnder.to_compare {Δ : Bounds} {s : Scheme} {σ : Substitution}
    (h : InstantiatesUnder Δ s σ) :
    CompareInstantiatesUnder Δ s (CompareSubstitution.ofSubstitution σ) := by
  refine ⟨h.domain.to_compare, h.images.to_compare, ?_⟩
  simpa only [CompareSubstitution.ofSubstitution_ty, CompareTy.definedUnder_ofTy] using h.body

theorem CompareSubstitution.WellFormedUnder.of_models {σ : CompareSubstitution} {Δ Ξ : Bounds}
    (h : σ.WellFormedUnder Δ) (hmodels : ∀ η, ModeModels Ξ η → ModeModels Δ η) :
    σ.WellFormedUnder Ξ := by
  exact ⟨fun v η hη => h.types v η (hmodels η hη),
    fun v η hη => h.modes v η (hmodels η hη)⟩

theorem CompareSubstitution.wellFormedUnder_iff_quantified {σ : CompareSubstitution}
    {Δ : Bounds} {s : Scheme} (hσ : CompareInstantiates s σ) :
    σ.WellFormedUnder Δ ↔
      (∀ n ∈ s.typeParams, (σ.type (.flex n)).DefinedUnder Δ) ∧
      (∀ n ∈ s.modParams, Entails Δ (.defined (σ.mode (.flex n)))) := by
  constructor
  · exact fun h => ⟨fun n _ => h.types (.flex n), fun n _ => h.modes (.flex n)⟩
  · rintro ⟨ht, hm⟩
    constructor
    · rintro (n | n)
      · cases he : σ.types.lookup n with
        | none => simp [type, he, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
        | some a =>
          apply ht n
          apply hσ.1.mem_iff.mp
          obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
          exact List.mem_map.mpr ⟨(n, a), by simp [hx], rfl⟩
      · simp [type, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
    · rintro (n | n)
      · cases he : σ.modes.lookup n with
        | none => simp [mode, he, Entails, ModExpr.WellFormed, ModExpr.eval]
        | some m =>
          apply hm n
          apply hσ.2.mem_iff.mp
          obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
          exact List.mem_map.mpr ⟨(n, m), by simp [hx], rfl⟩
      · simp [mode, Entails, ModExpr.WellFormed, ModExpr.eval]

end ModalityInference
