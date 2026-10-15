import ModalityInference.Proofs.ComparisonCapsuleExtraction
import ModalityInference.Proofs.ComparisonCarrierBodyReduction

namespace ModalityInference.ComparisonPartialCapsule

theorem Normal.not_defined {Δ : Bounds} {a : CompareTy} (s : Normal Δ a) :
    ¬a.DefinedUnder Δ := by
  intro hd
  have he := observe_defined hd
  rw [s.observation] at he
  exact Set.singleton_ne_empty _ he

end ModalityInference.ComparisonPartialCapsule

namespace ModalityInference.ComparisonPartialCapsuleScalar

open ComparisonPartialCapsule ComparisonPartialCarrier ComparisonInterpolation

/-- A mixed partial atomic image admits one input-supported capsule that
preserves all of its carrier bounds, including the carrier requests introduced
by structural factorization of a surrounding public type context. -/
theorem mixed_carrier_replacement
    {P : TypeVar → Prop} {Q : ModVar → Prop} {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b W : CompareTy} (hca : Carrier Δ a) (hcb : Carrier Δ b)
    (sa : Normal Δ a) (sb : Normal Δ b)
    (ha : Atomic (a.shape.subst ρ)) {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hl : AlgebraSubtype Δ a (.modal W m))
    (hu : AlgebraSubtype Δ (.modal W n) b)
    (hs : Supports P Q W) :
    ∃ q, project Δ sa.token W = some q ∧ (∀ v ∈ q.vars, Q v) ∧
      Entails Δ (.defined q) ∧
      (∀ c, Carrier Δ c → AlgebraSubtype Δ c W →
        AlgebraSubtype Δ c (.modal (.modal sa.token.1 sa.token.2) q)) ∧
      (∀ c, Carrier Δ c → AlgebraSubtype Δ W c →
        AlgebraSubtype Δ (.modal (.modal sa.token.1 sa.token.2) q) c) := by
  obtain ⟨q, hp, hsupport, hq, hlo, hup⟩ :=
    mixed_normal_scalar_reconstruction_supported hΔ hρ sa sb ha hm hn hl hu hs
  have hW : Atomic (W.shape.subst ρ) := by
    change Atomic ((.modal W m : CompareTy).shape.subst ρ)
    rw [← hl.shape_equivalent ρ hρ]
    exact ha
  have heps : Entails Δ (.defined .epsilon) := by intro η _; rfl
  have hshape : (CompareTy.modal sa.token.1 sa.token.2).WellShaped Δ :=
    sa.forward.wellShaped_right
  refine ⟨q, hp, hsupport, hq, ?_, ?_⟩
  · intro c hc hcW
    have hpartial : ¬c.DefinedUnder Δ := by
      intro hd
      have hd' := CompareTy.definedUnder_modal_iff.mpr ⟨hd, hn⟩
      exact sb.not_defined (hcb.defined_of_above hΔ hd'
        ((AlgebraSubtype.congr hcW (.refl hn)).trans hu))
    have hcatom : Atomic (c.shape.subst ρ) := by
      rw [hcW.shape_equivalent ρ hρ]
      exact hW
    obtain ⟨sc⟩ := carrier_partial_normal hc hcW.wellShaped_left hcatom hpartial
    have hacted : AlgebraSubtype Δ c (.modal W .epsilon) :=
      hcW.trans (.identityRev hcW.wellShaped_right)
    obtain ⟨he, hscalar⟩ := hlo c sc .epsilon heps hacted
    have hforward : AlgebraSubtype Δ c (.modal (.modal sa.token.1 sa.token.2) sc.suffix) := by
      rw [← he]
      exact .shaped sc.forward
    exact (hforward.trans (.congr (.refl hshape) hscalar)).trans
      ((AlgebraSubtype.shaped (.composeRev (a := .modal sa.token.1 sa.token.2) hshape)).trans
        (.identity hshape))
  · intro c hc hWc
    have hpartial : ¬c.DefinedUnder Δ := by
      intro hd
      have hd' := CompareTy.definedUnder_modal_iff.mpr ⟨hd, hm⟩
      exact sa.not_defined (hca.defined_of_below hΔ hd'
        (hl.trans (.congr hWc (.refl hm))))
    have hcatom : Atomic (c.shape.subst ρ) := by
      rw [← hWc.shape_equivalent ρ hρ]
      exact hW
    obtain ⟨sc⟩ := carrier_partial_normal hc hWc.wellShaped_right hcatom hpartial
    have hacted : AlgebraSubtype Δ (.modal W .epsilon) c :=
      (AlgebraSubtype.identity hWc.wellShaped_left).trans hWc
    obtain ⟨he, hscalar⟩ := hup c sc .epsilon heps hacted
    have hbackward : AlgebraSubtype Δ (.modal (.modal sa.token.1 sa.token.2) sc.suffix) c := by
      rw [← he]
      exact .shaped sc.backward
    exact ((AlgebraSubtype.identityRev (a := .modal (.modal sa.token.1 sa.token.2) q) hshape).trans
      (.shaped (.compose (a := .modal sa.token.1 sa.token.2) hshape))).trans
        ((AlgebraSubtype.congr (.refl hshape) hscalar).trans hbackward)

end ModalityInference.ComparisonPartialCapsuleScalar
