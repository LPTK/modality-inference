import ModalityInference.Proofs.ComparisonRawHeadLocality
import ModalityInference.Proofs.ComparisonDefinedPreparation

/-! Admissible prepared witnesses use a finite whole-head boundary determined
by the input. All substitution images and definedness obligations are preserved. -/
namespace ModalityInference.ComparisonRawHeadRestriction

open ComparisonPreparation

def RestrictedEntails (Δ : Bounds) (H : Set CompareTy) : CompareConstraint → Prop
  | .sub a b => Derivation Δ H a b ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ
  | .mode a b => Submode Δ a b
  | .defined a => ∀ σ, ModeModels Δ σ → a.WellFormed σ
  | .equal v t => Derivation Δ H (.var v) t ∧ Derivation Δ H t (.var v) ∧ t.DefinedUnder Δ
  | .equiv a b => Derivation Δ H a b ∧ Derivation Δ H b a ∧
      a.DefinedUnder Δ ∧ b.DefinedUnder Δ

def RestrictedEntailsAll (Δ : Bounds) (H : Set CompareTy) (cs : CompareBounds) : Prop :=
  ∀ c ∈ cs, RestrictedEntails Δ H c

theorem entails_iff_restricted {Δ H} (hc : Covers Δ H) (c : CompareConstraint) :
    AlgebraEntails Δ c ↔ RestrictedEntails Δ H c := by
  cases c with
  | sub a b => exact ⟨fun h => ⟨(algebra_iff_derivation_defined hc h.2.1 h.2.2).mp h.1,h.2⟩,
      fun h => ⟨h.1.algebra,h.2⟩⟩
  | mode | defined => exact Iff.rfl
  | equal v t =>
      have hv : CompareTy.DefinedUnder (.var v) Δ := by
        simp [CompareTy.DefinedUnder,CompareTy.wellFormedBounds,ModeModels]
      exact ⟨fun h => ⟨(algebra_iff_derivation_defined hc hv h.2.2).mp h.1,
        (algebra_iff_derivation_defined hc h.2.2 hv).mp h.2.1,h.2.2⟩,
        fun h => ⟨h.1.algebra,h.2.1.algebra,h.2.2⟩⟩
  | equiv a b => exact ⟨fun h => ⟨(algebra_iff_derivation_defined hc h.2.2.1 h.2.2.2).mp h.1,
      (algebra_iff_derivation_defined hc h.2.2.2 h.2.2.1).mp h.2.1,h.2.2⟩,
      fun h => ⟨h.1.algebra,h.2.1.algebra,h.2.2⟩⟩

theorem entailsAll_iff_restricted {Δ H} (hc : Covers Δ H) (cs : CompareBounds) :
    AlgebraEntailsAll Δ cs ↔ RestrictedEntailsAll Δ H cs :=
  ⟨fun h c hm => (entails_iff_restricted hc c).mp (h c hm),
    fun h c hm => (entails_iff_restricted hc c).mpr (h c hm)⟩

def RestrictedPreparedWitness (p : SchemePreparation.Prepared) (H : Set CompareTy)
    (σ : CompareSubstitution) : Prop :=
  σ.DomainsAbove p.firstType p.firstMode ∧ σ.WellShaped p.assumptions ∧
    RestrictedEntailsAll p.assumptions H (σ.bounds p.sourceBounds) ∧
    Derivation p.assumptions H (σ.ty p.sourceType) (.ofTy p.targetType)

def preparedInputBoundary (p : SchemePreparation.Prepared) : Set CompareTy :=
  boundary p.assumptions .unit (.ofTy p.targetType)

theorem preparedInputBoundary_finite (p : SchemePreparation.Prepared) :
    (preparedInputBoundary p).Finite := boundary_finite _ _ _

theorem prepared_witnessUnder_iff_restricted (p : SchemePreparation.Prepared)
    (σ : CompareSubstitution) :
    PreparedWitnessUnder p σ ↔
      RestrictedPreparedWitness p (preparedInputBoundary p) σ ∧
      σ.WellFormedUnder p.assumptions ∧ (σ.ty p.sourceType).DefinedUnder p.assumptions :=
  ⟨fun h => ⟨⟨h.1.1,h.1.2.1,
      (entailsAll_iff_restricted (boundary_covers _ _ _) _).mp h.1.2.2.1,
      (defined_raw_algebra_iff_derivation p.targetType (boundary_covers _ _ _)
        h.2.2 (boundary_right _ _ _)).mp h.1.2.2.2⟩,h.2⟩,
    fun h => ⟨⟨h.1.1,h.1.2.1,
      (entailsAll_iff_restricted (boundary_covers _ _ _) _).mpr h.1.2.2.1,
      h.1.2.2.2.algebra⟩,h.2⟩⟩

theorem prepared_witnessUnder_restriction {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : PreparedWitnessUnder p σ) :
    ∃ H : Set CompareTy, H.Finite ∧ Covers p.assumptions H ∧ RestrictedPreparedWitness p H σ ∧
      σ.WellFormedUnder p.assumptions ∧ (σ.ty p.sourceType).DefinedUnder p.assumptions :=
  ⟨preparedInputBoundary p,preparedInputBoundary_finite p,boundary_covers _ _ _,
    (prepared_witnessUnder_iff_restricted p σ).mp h⟩

end ModalityInference.ComparisonRawHeadRestriction
