import ModalityInference.Proofs.ComparisonRawCarrierSoundness
import ModalityInference.Proofs.ComparisonDefinedPreparation

/-! The capsule restriction preserves prepared witnesses literally, including
all type and mode images and the separate guards on source constraints. -/
namespace ModalityInference.ComparisonRawCarrierRestriction

open ComparisonPreparation

def RestrictedEntails (Δ : Bounds) (K : Set Token) : CompareConstraint → Prop
  | .sub a b => Derivation Δ K a b ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ
  | .mode a b => Submode Δ a b
  | .defined a => ∀ σ, ModeModels Δ σ → a.WellFormed σ
  | .equal v t => Derivation Δ K (.var v) t ∧ Derivation Δ K t (.var v) ∧
      t.DefinedUnder Δ
  | .equiv a b => Derivation Δ K a b ∧ Derivation Δ K b a ∧
      a.DefinedUnder Δ ∧ b.DefinedUnder Δ

def RestrictedEntailsAll (Δ : Bounds) (K : Set Token) (cs : CompareBounds) : Prop :=
  ∀ c ∈ cs, RestrictedEntails Δ K c

theorem entails_iff_restricted {Δ K} (hc : Covers Δ K) (c : CompareConstraint) :
    AlgebraEntails Δ c ↔ RestrictedEntails Δ K c := by
  cases c with
  | sub a b => exact ⟨fun h => ⟨(algebra_iff_derivation hc
      (carrier_defined h.2.1) (carrier_defined h.2.2)).mp h.1, h.2⟩,
      fun h => ⟨h.1.algebra, h.2⟩⟩
  | mode | defined => exact Iff.rfl
  | equal v t =>
    have hv : Carrier Δ K (.var v) := by
      simp only [Carrier, support, ComparisonPartialStructuredCapsule.Suffix.apply,
        ComparisonPartialCapsule.observe, Set.empty_subset]
    exact ⟨fun h => ⟨(algebra_iff_derivation hc hv (carrier_defined h.2.2)).mp h.1,
      (algebra_iff_derivation hc (carrier_defined h.2.2) hv).mp h.2.1,
      h.2.2⟩, fun h => ⟨h.1.algebra, h.2.1.algebra, h.2.2⟩⟩
  | equiv a b => exact ⟨fun h => ⟨(algebra_iff_derivation hc
      (carrier_defined h.2.2.1) (carrier_defined h.2.2.2)).mp h.1,
      (algebra_iff_derivation hc (carrier_defined h.2.2.2)
        (carrier_defined h.2.2.1)).mp h.2.1, h.2.2⟩,
      fun h => ⟨h.1.algebra, h.2.1.algebra, h.2.2⟩⟩

theorem entailsAll_iff_restricted {Δ K} (hc : Covers Δ K) (cs : CompareBounds) :
    AlgebraEntailsAll Δ cs ↔ RestrictedEntailsAll Δ K cs :=
  ⟨fun h c hc' => (entails_iff_restricted hc c).mp (h c hc'),
    fun h c hc' => (entails_iff_restricted hc c).mpr (h c hc')⟩

def RestrictedPreparedWitness (p : SchemePreparation.Prepared) (K : Set Token)
    (σ : CompareSubstitution) : Prop :=
  σ.DomainsAbove p.firstType p.firstMode ∧ σ.WellShaped p.assumptions ∧
    RestrictedEntailsAll p.assumptions K (σ.bounds p.sourceBounds) ∧
    Derivation p.assumptions K (σ.ty p.sourceType) (.ofTy p.targetType)

def preparedBoundary (p : SchemePreparation.Prepared) (σ : CompareSubstitution) : Set Token :=
  boundary p.assumptions (σ.ty p.sourceType) (.ofTy p.targetType)

theorem preparedBoundary_finite (p : SchemePreparation.Prepared) (σ : CompareSubstitution) :
    (preparedBoundary p σ).Finite := boundary_finite _ _ _

theorem prepared_witness_iff_restricted (p : SchemePreparation.Prepared)
    (σ : CompareSubstitution) :
    PreparedWitness p σ ↔ RestrictedPreparedWitness p (preparedBoundary p σ) σ := by
  simp only [PreparedWitness, RestrictedPreparedWitness,
    entailsAll_iff_restricted (boundary_covers p.assumptions (σ.ty p.sourceType) (.ofTy p.targetType)),
    algebra_iff_boundary_derivation, preparedBoundary]

theorem prepared_witness_restriction {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : PreparedWitness p σ) :
    ∃ K : Set Token, K.Finite ∧ Covers p.assumptions K ∧ RestrictedPreparedWitness p K σ :=
  ⟨preparedBoundary p σ, preparedBoundary_finite p σ,
    boundary_covers _ _ _, (prepared_witness_iff_restricted p σ).mp h⟩

/-- Admissibility makes the substituted source body defined, so its capsule
support is empty. The boundary therefore depends only on the prepared input. -/
def preparedInputBoundary (p : SchemePreparation.Prepared) : Set Token :=
  boundary p.assumptions .unit (.ofTy p.targetType)

theorem preparedInputBoundary_finite (p : SchemePreparation.Prepared) :
    (preparedInputBoundary p).Finite := boundary_finite _ _ _

theorem prepared_witnessUnder_iff_restricted (p : SchemePreparation.Prepared)
    (σ : CompareSubstitution) :
    PreparedWitnessUnder p σ ↔
      RestrictedPreparedWitness p (preparedInputBoundary p) σ ∧
      σ.WellFormedUnder p.assumptions ∧ (σ.ty p.sourceType).DefinedUnder p.assumptions :=
  ⟨fun h => ⟨⟨h.1.1, h.1.2.1,
      (entailsAll_iff_restricted (boundary_covers _ _ _) _).mp h.1.2.2.1,
      (algebra_iff_derivation (boundary_covers _ _ _) (carrier_defined h.2.2)
        (boundary_right _ _ _)).mp h.1.2.2.2⟩, h.2⟩,
    fun h => ⟨⟨h.1.1, h.1.2.1,
      (entailsAll_iff_restricted (boundary_covers _ _ _) _).mpr h.1.2.2.1,
      h.1.2.2.2.algebra⟩, h.2⟩⟩

theorem prepared_witnessUnder_restriction {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : PreparedWitnessUnder p σ) :
    ∃ K : Set Token, K.Finite ∧ Covers p.assumptions K ∧ RestrictedPreparedWitness p K σ ∧
      σ.WellFormedUnder p.assumptions ∧ (σ.ty p.sourceType).DefinedUnder p.assumptions :=
  ⟨preparedInputBoundary p, preparedInputBoundary_finite p, boundary_covers _ _ _,
    (prepared_witnessUnder_iff_restricted p σ).mp h⟩

end ModalityInference.ComparisonRawCarrierRestriction
