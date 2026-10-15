import ModalityInference.Proofs.ComparisonDefinedSubstitution
import ModalityInference.Proofs.ComparisonAlgebra
import ModalityInference.Proofs.ComparisonAlgebraPreparation
import ModalityInference.Proofs.SchemeInstance

/-! Explicit source obligations characterize comparison witnesses with defined
images and a defined instantiated body. -/
namespace ModalityInference

theorem AlgebraSubsumesUnder.to_algebra {Δ : Bounds} {source target : Scheme}
    (h : AlgebraSubsumesUnder Δ source target) : AlgebraSubsumes Δ source target := by
  obtain ⟨σ, hi, hs, _, _, hb, ht⟩ := h
  exact ⟨σ, hi, hs, hb, ht⟩

/-- Every admissible ordinary witness is an admissible algebraic witness. -/
theorem SubsumesUnder.to_algebra {Δ : Bounds} {source target : Scheme}
    (h : SubsumesUnder Δ source target) : AlgebraSubsumesUnder Δ source target := by
  obtain ⟨σ, hi, hb, ht⟩ := h
  have hc := hi.to_compare
  refine ⟨.ofSubstitution σ, hc.domain,
    CompareSubstitution.wellShaped_ofSubstitution _ _, hc.images, hc.body, ?_, ?_⟩
  · simpa only [CompareSubstitution.ofSubstitution_bounds] using hb.to_shaped.to_algebra
  · simpa only [CompareSubstitution.ofSubstitution_ty] using AlgebraSubtype.shaped ht.to_shaped

theorem CompareSubstitution.body_guards_iff {Δ : Bounds} {σ : CompareSubstitution}
    (ht : ∀ v, (σ.type v).DefinedUnder Δ) (a : Ty) :
    (σ.ty a).DefinedUnder Δ ↔ AlgebraEntailsAll Δ (σ.bounds a.wellFormedBounds) := by
  induction a with
  | var v =>
    simp only [ty, CompareTy.ofTy, CompareTy.subst, TypeExpr.wellFormedBounds,
      bounds, List.map_nil, AlgebraEntailsAll, List.not_mem_nil, false_implies,
      implies_true, iff_true]
    exact ht v
  | unit | credit =>
    simp [ty, CompareTy.ofTy, CompareTy.subst, CompareTy.DefinedUnder,
      CompareTy.wellFormedBounds, TypeExpr.wellFormedBounds, ModeModels,
      bounds, AlgebraEntailsAll]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simpa only [ty, CompareTy.ofTy, CompareTy.subst, CompareTy.DefinedUnder,
      CompareTy.wellFormedBounds, TypeExpr.wellFormedBounds, ModeModels,
      bounds, List.map_append, AlgebraEntailsAll, List.mem_append,
      or_imp, forall_and] using and_congr iha ihb
  | modal a m ih =>
    simpa only [ty, CompareTy.ofTy, CompareTy.subst, CompareTy.DefinedUnder,
      CompareTy.wellFormedBounds, TypeExpr.wellFormedBounds, ModeModels,
      bounds, List.map_append, List.map_cons, List.map_nil, AlgebraEntailsAll,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
      forall_eq, constraint, AlgebraEntails, ModeSatisfies] using
      and_congr ih (Iff.rfl : Entails Δ (.defined (m.subst σ.mode)) ↔ _)

theorem CompareSubstitution.self_bound_iff {Δ : Bounds} {σ : CompareSubstitution}
    (hs : σ.WellShaped Δ) (v : TypeVar) :
    AlgebraEntails Δ (σ.constraint (.sub (.var v) (.var v))) ↔
      (σ.type v).DefinedUnder Δ := by
  change (AlgebraSubtype Δ (σ.type v) (σ.type v) ∧
    (σ.type v).DefinedUnder Δ ∧ (σ.type v).DefinedUnder Δ) ↔ _
  exact ⟨fun h => h.2.1, fun h => ⟨.refl (hs.type v), h, h⟩⟩

theorem CompareSubstitution.instance_guards_iff {Δ : Bounds} {σ : CompareSubstitution}
    {s : Scheme} (hi : CompareInstantiates s σ) (hs : σ.WellShaped Δ) :
    AlgebraEntailsAll Δ (σ.bounds s.instanceGuards) ↔
      σ.WellFormedUnder Δ ∧ (σ.ty s.body).DefinedUnder Δ := by
  have he : AlgebraEntailsAll Δ (σ.bounds s.instanceGuards) ↔
      AlgebraEntailsAll Δ (σ.bounds s.body.wellFormedBounds) ∧
        (∀ n ∈ s.typeParams, (σ.type (.flex n)).DefinedUnder Δ) ∧
        (∀ n ∈ s.modParams, Entails Δ (.defined (σ.mode (.flex n)))) := by
    simp only [Scheme.instanceGuards, bounds, List.map_append, AlgebraEntailsAll,
      List.mem_append, or_imp, forall_and, List.forall_mem_map]
    simp only [self_bound_iff hs]
    simp only [constraint, ModExpr.subst, AlgebraEntails, Entails, and_assoc]
  rw [he]
  constructor
  · rintro ⟨hb, ht, hm⟩
    have hσ := (wellFormedUnder_iff_quantified hi).mpr ⟨ht, hm⟩
    exact ⟨hσ, (body_guards_iff hσ.types s.body).mpr hb⟩
  · rintro ⟨hσ, hb⟩
    exact ⟨(body_guards_iff hσ.types s.body).mp hb,
      (wellFormedUnder_iff_quantified hi).mp hσ⟩

theorem algebraSubsumes_requireDefinedInstances_iff
    (Δ : Bounds) (source target : Scheme) :
    AlgebraSubsumes Δ source.requireDefinedInstances target ↔
      AlgebraSubsumesUnder Δ source target := by
  simp only [AlgebraSubsumes, AlgebraSubsumesUnder,
    Scheme.requireDefinedInstances_subsumptionIndices]
  generalize source.subsumptionIndices Δ target = indices
  rcases indices with ⟨nt, nm⟩
  dsimp only
  apply exists_congr
  intro σ
  constructor
  · rintro ⟨hi, hs, hb, ht⟩
    have hg : AlgebraEntailsAll (Δ ++ (target.instantiate nt nm true).1.assumptions)
        (σ.bounds source.bounds) ∧
        AlgebraEntailsAll (Δ ++ (target.instantiate nt nm true).1.assumptions)
          (σ.bounds source.instanceGuards) := by
      simpa only [Scheme.requireDefinedInstances, CompareSubstitution.bounds,
        List.map_append, AlgebraEntailsAll, List.mem_append, or_imp, forall_and] using hb
    obtain ⟨hw, hd⟩ := (σ.instance_guards_iff (s := source) hi hs).mp hg.2
    exact ⟨hi, hs, hw, hd, hg.1, ht⟩
  · rintro ⟨hi, hs, hw, hd, hb, ht⟩
    refine ⟨hi, hs, ?_, ht⟩
    have hg := (σ.instance_guards_iff hi hs).mpr ⟨hw, hd⟩
    simpa only [Scheme.requireDefinedInstances, CompareSubstitution.bounds,
      List.map_append, AlgebraEntailsAll, List.mem_append, or_imp, forall_and] using
      And.intro hb hg

end ModalityInference
