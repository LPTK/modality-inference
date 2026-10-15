import ModalityInference.Proofs.ComparisonGuardedTotal
import ModalityInference.Proofs.ComparisonPreparationComplete
import ModalityInference.Proofs.ComparisonCapsuleTotality

/-! Guarded classification preserves the entire original prepared witness. -/

namespace ModalityInference.ComparisonGuardedTotal

theorem prepared_scalarBounds_iff {p : SchemePreparation.Prepared} {action : CompareSubstitution} :
    ComparisonPreparation.PreparedWitness
      { p with sourceBounds := scalarBounds p.sourceBounds ++ p.sourceBounds } action ↔
      ComparisonPreparation.PreparedWitness p action := by
  constructor
  · intro h
    refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
    intro c hc
    exact h.2.2.1 c (by simpa only [CompareSubstitution.bounds, List.map_append] using
      List.mem_append_right (action.bounds (scalarBounds p.sourceBounds)) hc)
  · intro h
    refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
    intro c hc
    simp only [CompareSubstitution.bounds, List.map_append, List.mem_append] at hc
    rcases hc with hc | hc
    · exact scalarBounds_entails h.2.2.1 c hc
    · exact h.2.2.1 c hc

/-- A successful conditional certification recognizes exactly the total queried
expressions; the finite residual traversal does not weaken its semantics. -/
theorem classifier_exact {fuel : Nat} {Δ guards : Bounds} {expressions known : List ModExpr}
    (h : ComparisonBody.knownTotal fuel (Δ ++ guards.assumptions) expressions = .success known)
    (m : ModExpr)
    (hm : ComparisonBody.residuals m ⊆ expressions.flatMap ComparisonBody.residuals) :
    ComparisonBody.isTotal known m = true ↔ Entails (Δ ++ guards.assumptions) (.defined m) :=
  ⟨ComparisonBody.isTotal_defined (ComparisonBody.knownTotal_sound h),
    ComparisonBody.knownTotal_isTotal_complete h m hm⟩

theorem classified_subst {fuel : Nat} {Δ guards : Bounds} {σ : CompareSubstitution}
    {expressions known : List ModExpr} {m : ModExpr}
    (hk : ComparisonBody.knownTotal fuel (Δ ++ guards.assumptions) expressions = .success known)
    (hc : ComparisonBody.residuals m ⊆ expressions.flatMap ComparisonBody.residuals)
    (ht : Entails (Δ ++ guards.assumptions) (.defined m))
    (hb : AlgebraEntailsAll Δ (σ.bounds guards))
    (hf : ∀ v ∈ Δ.modVars, σ.mode v = .var v)
    (hm : ∀ v ∈ m.vars, v ∉ guards.modVars → Entails Δ (.defined (σ.mode v))) :
    ComparisonBody.isTotal known m = true ∧ Entails Δ (.defined (m.subst σ.mode)) :=
  ⟨(classifier_exact hk m hc).mpr ht, defined_subst ht hb hf hm⟩

end ModalityInference.ComparisonGuardedTotal
