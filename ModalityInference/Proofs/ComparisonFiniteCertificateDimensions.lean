import ModalityInference.Proofs.ComparisonFiniteCertificateSource
import Mathlib.SetTheory.Cardinal.Finite

/-! Explicit finite dimensions for the source model serialized into a checked
comparison certificate. The bounds depend on the realized state count, the
written boundary heads, and the executable finite control presentation. -/
namespace ModalityInference.ComparisonFiniteCertificate.Dimensions

open ComparisonFiniteControlEncoding ComparisonFiniteControls ComparisonRawHeadFiniteOrbits
  ComparisonObserverShadowActions ComparisonObserverShadowModel ComparisonObserverShadowPresentation
  ComparisonObserverShadowActionRows ComparisonObserverShadowQueryDescriptions
  ComparisonRelativeIntervals ComparisonRelativeSyntax Serialization SourceConstruction

noncomputable section

variable {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
  {B : Boundary Δ} {names : List ModVar} {base : Nat}
  {extra : List (RawRow hn (assign hn B names base))}

def tagBound (Δ : Bounds) (names : List ModVar) (heads states : Nat) : Nat :=
  2 ^ states + heads * (labels Δ names).length

def observationBound (Δ : Bounds) (names : List ModVar) (heads states : Nat) : Nat :=
  2 ^ tagBound Δ names heads states

theorem control_card (Δ : Bounds) (names : List ModVar) :
    Nat.card (Control Δ names) = (labels Δ names).length := by
  rw [← Nat.card_congr (orderIso Δ names).toEquiv]
  exact (Nat.card_congr (⟨Code.index,Code.mk,fun x => by cases x; rfl,fun _ => rfl⟩ :
    Code Δ names ≃ Fin (labels Δ names).length)).trans (by simp [Nat.card_eq_fintype_card])

theorem point_card (B : Boundary Δ) (names : List ModVar) :
    Nat.card (Point B names) = B.heads.length * (labels Δ names).length := by
  have h := Nat.card_congr (⟨fun p => (p.head,p.control),fun x => ⟨x.1,x.2⟩,
    fun _ => rfl,fun _ => rfl⟩ : Point B names ≃ Fin B.heads.length × Control Δ names)
  simpa only [Nat.card_prod,control_card,Nat.card_eq_fintype_card,Fintype.card_fin] using h

theorem observation_card_le {D P : Type*} [Lattice D] [Preorder P]
    [Fintype D] [Fintype P] (I : IntervalData D P) :
    Nat.card I.Observation ≤ 2 ^ (Nat.card D + Nat.card P) := by
  classical
  suffices h : Function.Injective (IntervalData.Observation.value (I := I)) by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_sum,Fintype.card_bool] using
      Nat.card_le_card_of_injective _ h
  exact fun a b h => IntervalData.Observation.ext
    (DFunLike.ext _ _ (fun x => congrFun h (.inl x))) (funext fun p => congrFun h (.inr p))

theorem tags_card_le (R : Realization hn B names base extra) :
    Nat.card (ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) ≤
      tagBound Δ names B.heads.length R.count := by
  rw [Nat.card_sum,point_card,tagBound]
  exact Nat.add_le_add_right (by simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using
    ComparisonObserverFiniteRange.card_value (nodes := R.machine)) _

theorem observations_card_le (R : Realization hn B names base extra) :
    Nat.card R.interval.Observation ≤ observationBound Δ names B.heads.length R.count := by
  apply (observation_card_le R.interval).trans
  exact Nat.pow_le_pow_right (by decide) (by simpa only [Nat.card_sum] using tags_card_le R)

theorem exists_source_bounded (R : Realization hn B names base extra) (T : Tables R)
    (hnames : Δ.modVars ⊆ names.toFinset) (sites : List RawSite)
    (tag : RawSite → ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names)
    {queries : List CompareTy} (description : Described hn B names base R queries) :
    ∃ tags observations,
      tags ≤ tagBound Δ names B.heads.length R.count ∧
      observations ≤ observationBound Δ names B.heads.length R.count ∧
      ∃ source : Source Δ names R.count tags observations,
        ∀ a b, source.model.Related a b ↔ (T.model hnames sites tag).Related a b := by
  letI : Fintype (ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) := Fintype.ofFinite _
  letI : Fintype R.interval.Observation := Fintype.ofFinite _
  refine ⟨_,_,?_,?_,source_of_indices R T hnames sites tag
    (Fintype.equivFin (ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names)).symm
    (Fintype.equivFin R.interval.Observation).symm description⟩
  · simpa only [Nat.card_eq_fintype_card] using tags_card_le R
  · simpa only [Nat.card_eq_fintype_card] using observations_card_le R

end
end ModalityInference.ComparisonFiniteCertificate.Dimensions
