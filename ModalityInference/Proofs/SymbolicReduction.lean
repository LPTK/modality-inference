import ModalityInference.Proofs.SymbolicInversion
import ModalityInference.Proofs.GeneralizationTransport

/-! Constraint reductions preserve defined symbolic solutions under residual
ambient type assumptions. -/
namespace ModalityInference

theorem ConstraintReduction.entails_forward_residual {cs ds Δ}
    (hΔ : Residual Δ) (h : ConstraintReduction cs ds) (hs : EntailsAll Δ cs) :
    EntailsAll Δ ds := by
  have hg : ∀ ρ, GroundModels ρ cs ↔ GroundModels ρ ds := fun _ => h.groundModels
  induction h
  case pair a b c d l r | sum a b c d l r =>
    simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Entails, TypeExpr.definedUnder_modal,
      TypeExpr.definedUnder_prod, TypeExpr.definedUnder_sum] at hs ⊢
    refine ⟨⟨?_, ⟨hs.2.1.1.1, hs.2.1.2⟩, hs.2.2.1.1, hs.2.2.2⟩,
      ⟨?_, ⟨hs.2.1.1.2, hs.2.1.2⟩, hs.2.2.1.2, hs.2.2.2⟩, ?_⟩
    all_goals first
      | exact SymbolicInversion.subtype_pairChild hΔ hs.1 (Or.inl rfl) false
      | exact SymbolicInversion.subtype_pairChild hΔ hs.1 (Or.inr rfl) false
      | exact SymbolicInversion.subtype_pairChild hΔ hs.1 (Or.inl rfl) true
      | exact SymbolicInversion.subtype_pairChild hΔ hs.1 (Or.inr rfl) true
      | exact SymbolicInversion.subtype_structural_mode hΔ hs.1
          (by simpa only [TypeExpr.definedUnder_modal, TypeExpr.definedUnder_prod,
            TypeExpr.definedUnder_sum] using hs.2.1)
          (by simpa only [TypeExpr.definedUnder_modal, TypeExpr.definedUnder_prod,
            TypeExpr.definedUnder_sum] using hs.2.2)
          (by simp [SymbolicInversion.tag, ComparisonShape.ofTy, ComparisonStructuralProjection.rootTag])
          (by simp [SymbolicInversion.tag, ComparisonShape.ofTy, ComparisonStructuralProjection.rootTag])
          (by intros _ _ h; cases h) (by intros _ _ h; cases h)
  case fn a b c d l r =>
    simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Entails, TypeExpr.definedUnder_modal,
      TypeExpr.definedUnder_fn] at hs ⊢
    exact ⟨⟨SymbolicInversion.subtype_fnChild hΔ hs.1 rfl true,
        hs.2.2.1.1, hs.2.1.1.1⟩,
      ⟨SymbolicInversion.subtype_fnChild hΔ hs.1 rfl false,
        hs.2.1.1.2, hs.2.2.1.2⟩,
      SymbolicInversion.subtype_function_mode hΔ hs.1
        (TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_fn.mpr hs.2.1.1, hs.2.1.2⟩)
        (TypeExpr.definedUnder_modal.mpr ⟨TypeExpr.definedUnder_fn.mpr hs.2.2.1, hs.2.2.2⟩)⟩
  case unit l r | credit l r =>
    simp only [EntailsAll, List.mem_singleton, forall_eq, Entails] at hs ⊢
    exact SymbolicInversion.subtype_structural_mode hΔ hs.1 hs.2.1 hs.2.2
      (by decide) (by decide) (by intros _ _ h; cases h) (by intros _ _ h; cases h)
  case context xs ys before after h ih =>
    simp only [EntailsAll, List.mem_append, or_imp, forall_and] at hs ⊢
    exact ⟨⟨hs.1.1, ih hs.1.2 (fun _ => h.groundModels)⟩, hs.2⟩
  all_goals
    have hm : ∀ η, ModeModels Δ η → ModeModels _ η := fun η hη =>
      (GroundModels.modeModels ((hg ⟨fun _ => .unit Mode.identity, η⟩).mp
        (by simpa only [GroundModels, GroundSatisfies, ModeModels, ModeSatisfies,
          List.mem_singleton, forall_eq]
          using hs.modeModels hη)))
    simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Entails]
    repeat' apply And.intro
    all_goals first
      | exact Submode.valid fun η hη => hm η hη (.mode _ _) (by simp)
      | exact fun η hη => hm η hη (.defined _) (by simp)

theorem ConstraintReduction.substitute (h : ConstraintReduction cs ds) (σ : Substitution) :
    ConstraintReduction (σ.bounds cs) (σ.bounds ds) := by
  induction h
  all_goals simp only [Substitution.bounds, List.map_cons, List.map_nil, List.map_append,
    Substitution.constraint, Constraint.subst, TypeExpr.subst, ModExpr.subst]
  all_goals first
    | exact .pair | exact .sum | exact .fn | exact .unit | exact .credit
    | exact .join | exact .meet | exact .sub | exact .imp | exact .left | exact .right
    | exact .close | exact .context ‹_›

theorem Entails.consequence_substitute {cs c Δ} {σ : Substitution}
    (hc : ∀ Γ, EntailsAll Γ cs → Entails Γ c) (hw : σ.WellFormedUnder Δ)
    (hs : EntailsAll Δ (σ.bounds cs)) : Entails Δ (σ.constraint c) :=
  (σ.constraint_subst_entails c Δ).mpr
    ((hw.judgmentMap hs.subst_assumptions).entails
      (hc cs.assumptions cs.assumptions_entails))

theorem Constraint.normalize_substitute {c Δ} {σ : Substitution}
    (hw : σ.WellFormedUnder Δ) :
    Entails Δ (σ.constraint c.normalize) ↔ Entails Δ (σ.constraint c) := by
  constructor <;> intro h
  · exact Entails.consequence_substitute (cs := [c.normalize])
      (fun Γ hΓ => (c.normalize_entails Γ).mp (hΓ _ (by simp))) hw
      (by simpa [Substitution.bounds, EntailsAll] using h)
  · exact Entails.consequence_substitute (cs := [c])
      (fun Γ hΓ => (c.normalize_entails Γ).mpr (hΓ _ (by simp))) hw
      (by simpa [Substitution.bounds, EntailsAll] using h)

end ModalityInference
