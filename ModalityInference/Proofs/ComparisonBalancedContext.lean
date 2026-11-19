import ModalityInference.Proofs.ComparisonBalancedDerivation
import ModalityInference.Proofs.ComparisonRawContext
import ModalityInference.Proofs.ComparisonAmbientNormalization

/-! Transport for defined comparisons can omit partial declared edges once
defined derivations have been extracted. Scalar and shape information is still
transported from the complete original context. -/
namespace ModalityInference.ComparisonBalancedContext

open ComparisonBalancedDerivation ComparisonTotalDerivation

structure Hom (Δ Γ : Bounds) : Prop extends ComparisonRawContext.Frame Δ Γ where
  bounds : ∀ a b, Constraint.sub a b ∈ Δ →
    (CompareTy.ofTy a).DefinedUnder Δ → (CompareTy.ofTy b).DefinedUnder Δ →
    AlgebraSubtype Γ (.ofTy a) (.ofTy b)

theorem Hom.total {Δ Γ a b} (h : Hom Δ Γ) (hab : Derivation Δ a b) :
    AlgebraSubtype Γ a b := by
  induction hab
  all_goals first
    | exact .refl (h.toFrame.wellShaped ‹_›)
    | exact h.bounds _ _ ‹_› ‹_› ‹_›
    | exact .identity (h.toFrame.wellShaped ‹_›)
    | exact .identityRev (h.toFrame.wellShaped ‹_›)
    | exact .compose (h.toFrame.wellShaped ‹_›)
    | exact .composeRev (h.toFrame.wellShaped ‹_›)
    | exact .trans ‹_› ‹_›
    | exact .congr ‹_› (h.toFrame.submode ‹_›)
    | exact .prod ‹_› ‹_›
    | exact .sum ‹_› ‹_›
    | exact .fn ‹_› ‹_› (h.toFrame.submode ‹_›)
    | exact .shaped (.joinLeft (h.toFrame.compatible ‹_›).1)
    | exact .shaped (.joinRight (h.toFrame.compatible ‹_›).1)
    | exact .joinLeast ‹_› ‹_›
    | exact .shaped (.meetLeft (h.toFrame.compatible ‹_›).1)
    | exact .shaped (.meetRight (h.toFrame.compatible ‹_›).1)
    | exact .meetGreatest ‹_› ‹_›
    | exact .equation (h.toFrame.equation ‹_›)
    | exact .equationRev (h.toFrame.equation ‹_›)
    | exact .clamp (h.toFrame.compatible ‹_›) (h.toFrame.compatible ‹_›)
        (h.toFrame.mode_defined ‹_›) ‹_› ‹_›
    | exact .clampRev (h.toFrame.compatible ‹_›) (h.toFrame.compatible ‹_›)
        (h.toFrame.mode_defined ‹_›) ‹_› ‹_›

theorem Hom.algebra {Δ Γ a b} (h : Hom Δ Γ) (hΔ : Balanced Δ)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ)
    (hab : AlgebraSubtype Δ a b) : AlgebraSubtype Γ a b :=
  h.total (ComparisonBalancedDerivation.derivation hΔ ha hb hab)

private theorem defined_var (Δ : Bounds) (v : TypeVar) :
    (CompareTy.var v).DefinedUnder Δ := fun _ _ _ hc => False.elim (List.not_mem_nil hc)

theorem Hom.entails {Δ Γ} (h : Hom Δ Γ) (hΔ : Balanced Δ) {c : CompareConstraint}
    (hc : AlgebraEntails Δ c) : AlgebraEntails Γ c := by
  cases c
  all_goals first
    | exact ⟨h.algebra hΔ hc.2.1 hc.2.2 hc.1,
        h.toFrame.defined hc.2.1, h.toFrame.defined hc.2.2⟩
    | exact h.toFrame.submode hc
    | exact h.toFrame.mode_defined hc
    | exact ⟨h.algebra hΔ (defined_var _ _) hc.2.2 hc.1,
        h.algebra hΔ hc.2.2 (defined_var _ _) hc.2.1, h.toFrame.defined hc.2.2⟩
    | exact ⟨h.algebra hΔ hc.2.2.1 hc.2.2.2 hc.1,
        h.algebra hΔ hc.2.2.2 hc.2.2.1 hc.2.1,
        h.toFrame.defined hc.2.2.1, h.toFrame.defined hc.2.2.2⟩

/-- Preserve the literal shared witness, including exact domains and every
body, bound, and quantified-image guard. Target definedness is derived. -/
theorem Hom.witness {p : SchemePreparation.Prepared} {Γ : Bounds}
    (h : Hom p.assumptions Γ) (hΔ : Balanced p.assumptions) {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder p σ) :
    ComparisonPreparation.PreparedWitnessUnder {p with assumptions := Γ} σ := by
  obtain ⟨⟨hd, hs, hb, ht⟩, hi, hbody⟩ := hw
  exact ⟨⟨hd, fun entry he => h.toFrame.wellShaped (hs entry he),
    fun c hc => h.entails hΔ (hb c hc), h.algebra hΔ hbody
      ((CompareTy.definedUnder_ofTy _ _).mpr (public_defined_right hΔ hbody ht)) ht⟩,
    hi.of_models h.modes, h.toFrame.defined hbody⟩

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Retain every scalar and non-subtype assumption. This mathematical projection
does not decide the guards or supply a comparison algorithm. -/
def keep (Δ : Bounds) : Constraint → Bool
  | .sub a b => decide (a.DefinedUnder Δ ∧ b.DefinedUnder Δ)
  | _ => true

def prune (Δ : Bounds) : Bounds := Δ.filter (keep Δ)

theorem prune_subset (Δ : Bounds) : prune Δ ⊆ Δ := fun _ h => (List.mem_filter.mp h).1

@[simp] theorem sub_mem_prune (Δ : Bounds) (a b : Ty) :
    Constraint.sub a b ∈ prune Δ ↔
      Constraint.sub a b ∈ Δ ∧ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp only [prune, List.mem_filter, keep, decide_eq_true_eq]

theorem modeModels_prune (Δ : Bounds) (η : ModVar → Mode) :
    ModeModels (prune Δ) η ↔ ModeModels Δ η := by
  constructor
  · intro h c hc
    cases c
    all_goals first | exact True.intro | exact h _ (List.mem_filter.mpr ⟨hc, rfl⟩)
  · exact fun h c hc => h c (prune_subset Δ hc)

theorem prune_defined (Δ : Bounds) : (prune Δ).TypeBoundsDefined :=
  fun a b h => ⟨fun η hη => ((sub_mem_prune Δ a b).mp h).2.1 η
    ((modeModels_prune Δ η).mp hη), fun η hη => ((sub_mem_prune Δ a b).mp h).2.2 η
      ((modeModels_prune Δ η).mp hη)⟩

theorem prune_hom (Δ : Bounds)
    (hs : ∀ ρ, ComparisonShape.Models (prune Δ) ρ → ComparisonShape.Models Δ ρ) :
    Hom Δ (prune Δ) where
  modes η := (modeModels_prune Δ η).mp
  shapes := hs
  bounds a b h ha hb := .shaped (.bound ((sub_mem_prune Δ a b).mpr
    ⟨h, (CompareTy.definedUnder_ofTy _ _).mp ha, (CompareTy.definedUnder_ofTy _ _).mp hb⟩))

theorem unprune_hom (Δ : Bounds) : ComparisonRawContext.Hom (prune Δ) Δ :=
  ComparisonAmbientNormalization.hom_of_subset (prune_subset Δ)

/-- Partial subtype edges are irrelevant to defined endpoint order when they
do not cross definedness and deleting them preserves structural information. -/
theorem algebra_prune_iff {Δ : Bounds} (hΔ : Balanced Δ)
    (hs : ∀ ρ, ComparisonShape.Models (prune Δ) ρ → ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    AlgebraSubtype (prune Δ) a b ↔ AlgebraSubtype Δ a b :=
  ⟨(unprune_hom Δ).algebra, (prune_hom Δ hs).algebra hΔ ha hb⟩

end

end ModalityInference.ComparisonBalancedContext
