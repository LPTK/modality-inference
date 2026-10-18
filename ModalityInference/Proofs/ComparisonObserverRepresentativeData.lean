import ModalityInference.Proofs.ComparisonObserverRepresentatives

/-! Root data extracted from a genuine child retains that child's literal
transition, including its values on uninhabited Boolean fibers. -/
namespace ModalityInference.ComparisonObserverRepresentatives

open ComparisonAlgebra ComparisonObserverGluing

noncomputable def data {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (g : Child Δ) : Data Δ :=
  { extracted hn g.observer with transition := g.transition }

theorem data_represents {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (g : Child Δ) : Represents (data hn g) g.observer := by
  intro a ha
  induction a with
  | var | unit | credit => rfl
  | prod a b | sum a b | fn a b => exact extracted_represents hn g.observer _ ha
  | modal a m ih =>
    have hd := CompareTy.definedUnder_modal_iff.mp ha
    change g.transition.apply m ((data hn g).value a) = _
    rw [ih hd.1]
    exact g.action m hd.2 a (representable hn hd.1)
  | join a b iha ihb =>
    have hd := CompareTy.definedUnder_join_iff.mp ha
    exact congrArg₂ (· || ·) (iha hd.1) (ihb hd.2)
  | meet a b iha ihb =>
    have hd := CompareTy.definedUnder_meet_iff.mp ha
    exact congrArg₂ (· && ·) (iha hd.1) (ihb hd.2)

theorem data_coherent {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (g : Child Δ) : Coherent (data hn g) :=
  (data_represents hn g).coherent hn

theorem data_bounds {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Bounds.TypeBoundsDefined Δ) (g : Child Δ) : BoundsHold (data hn g) :=
  (data_represents hn g).bounds hn hΔ

theorem data_range {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (g : Child Δ) {a : CompareTy} (ha : a.DefinedUnder Δ) :
    g.Range ((data hn g).value a) :=
  (data_represents hn g a ha).symm ▸ g.range_value (representable hn ha)

end ModalityInference.ComparisonObserverRepresentatives
