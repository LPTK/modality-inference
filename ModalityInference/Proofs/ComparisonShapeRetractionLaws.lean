import ModalityInference.Proofs.ComparisonShapeRetraction
import ModalityInference.Proofs.ComparisonUnanchoredRoot

/-! A single certified shape cut preserves algebraic order and commutes with
all modalities defined by the unchanged declared context. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeletonCoordinates
open ComparisonUnanchoredProjection

private theorem acted_absorb {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ)
    (m n : GuardedMode Δ) :
    AlgebraSubtype Δ (.modal (.modal a m.expression) (Scalar.compose n m).expression)
        (.modal a (Scalar.compose n m).expression) ∧
      AlgebraSubtype Δ (.modal a (Scalar.compose n m).expression)
        (.modal (.modal a m.expression) (Scalar.compose n m).expression) := by
  have he : Scalar.equivalent (Scalar.compose m (Scalar.compose n m)) (Scalar.compose n m) :=
    ⟨fun η _ => by simp only [Scalar.compose, Mode.compose_absorb_right]; exact Mode.le_refl _,
     fun η _ => by simp only [Scalar.compose, Mode.compose_absorb_right]; exact Mode.le_refl _⟩
  exact ⟨(AlgebraSubtype.shaped (.compose ha)).trans (.congr (.refl ha) (Scalar.submode he.1)),
    (AlgebraSubtype.congr (.refl ha) (Scalar.submode he.2)).trans (.shaped (.composeRev ha))⟩

theorem pair_act (isSum : Bool) {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) (n m : GuardedMode Δ) :
    pair isSum (m.act a) (m.act b) (Scalar.compose n m) ≤ m.act (pair isSum a b n) ∧
      m.act (pair isSum a b n) ≤ pair isSum (m.act a) (m.act b) (Scalar.compose n m) := by
  have ha := acted_absorb a.shaped m n
  have hb := acted_absorb b.shaped m n
  cases isSum
  · exact ⟨(AlgebraSubtype.prod ha.1 hb.1).trans
      (.shaped (.composeRev ⟨a.shaped, b.shaped⟩)),
      (AlgebraSubtype.shaped (.compose (a := .prod a.type b.type)
        ⟨a.shaped, b.shaped⟩)).trans (.prod ha.2 hb.2)⟩
  · exact ⟨(AlgebraSubtype.sum ha.1 hb.1).trans
      (.shaped (.composeRev ⟨a.shaped, b.shaped⟩)),
      (AlgebraSubtype.shaped (.compose (a := .sum a.type b.type)
        ⟨a.shaped, b.shaped⟩)).trans (.sum ha.2 hb.2)⟩

theorem function_act {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) (n m : GuardedMode Δ) :
    function a b (Scalar.compose n m) ≤ m.act (function a b n) ∧
      m.act (function a b n) ≤ function a b (Scalar.compose n m) :=
  ⟨.shaped (.composeRev ⟨a.shaped, b.shaped⟩), .shaped (.compose ⟨a.shaped, b.shaped⟩)⟩

theorem absorbing_act {Δ : Bounds} (m : GuardedMode Δ) :
    absorbing Δ ≤ m.act (absorbing Δ) ∧ m.act (absorbing Δ) ≤ absorbing Δ := by
  have h := Scalar.absorbing_compose m
  exact ⟨(AlgebraSubtype.congr (.refl (a := .unit) trivial) (Scalar.submode h.1)).trans
      (.shaped (.composeRev trivial)),
    (AlgebraSubtype.shaped (.compose (a := .unit) trivial)).trans (.congr (.refl trivial) (Scalar.submode h.2))⟩


/-- The same cut commutes with every modality defined under the declared
context. Retained subtrees and erased leaves share the original action. -/
theorem Cut.retract_modal {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (c : Cut) (hc : c.Valid Δ ρ) (a : Carrier Δ c.source) (m : GuardedMode Δ) :
    c.retract hc (m.act a) ≤ m.act (c.retract hc a) ∧
      m.act (c.retract hc a) ≤ c.retract hc (m.act a) := by
  induction c with
  | keep s => exact ⟨le_refl _, le_refl _⟩
  | erase s => exact absorbing_act m
  | prod c d ih₁ ih₂ =>
    have h₁ := ih₁ hc.2.1 (pairLeft false hc.1 a)
    have h₂ := ih₂ hc.2.2 (pairRight false hc.1 a)
    have hm := rootGuarded_modal a.type a.defined m
    have hp := pair_act false (c.retract hc.2.1 (pairLeft false hc.1 a))
      (d.retract hc.2.2 (pairRight false hc.1 a)) (rootGuarded a.type a.defined) m
    simp only [Cut.retract, pairLeft_act, pairRight_act]
    exact ⟨(pair_mono false h₁.1 h₂.1 hm.1).trans hp.1,
      hp.2.trans (pair_mono false h₁.2 h₂.2 hm.2)⟩
  | sum c d ih₁ ih₂ =>
    have h₁ := ih₁ hc.2.1 (pairLeft true hc.1 a)
    have h₂ := ih₂ hc.2.2 (pairRight true hc.1 a)
    have hm := rootGuarded_modal a.type a.defined m
    have hp := pair_act true (c.retract hc.2.1 (pairLeft true hc.1 a))
      (d.retract hc.2.2 (pairRight true hc.1 a)) (rootGuarded a.type a.defined) m
    simp only [Cut.retract, pairLeft_act, pairRight_act]
    exact ⟨(pair_mono true h₁.1 h₂.1 hm.1).trans hp.1,
      hp.2.trans (pair_mono true h₁.2 h₂.2 hm.2)⟩
  | fn c d ih₁ ih₂ =>
    have hm := rootGuarded_modal_future a.type a.defined m
    have hp := function_act (c.retract hc.2.1 (functionDomain hc.1 a))
      (d.retract hc.2.2 (functionCodomain hc.1 a)) (rootGuarded a.type a.defined) m
    simp only [Cut.retract, functionDomain_act, functionCodomain_act]
    exact ⟨(function_mono (le_refl _) (le_refl _) hm.1).trans hp.1,
      hp.2.trans (function_mono (le_refl _) (le_refl _) hm.2)⟩


/-- A valid cut preserves all comparisons at once. No declared bound at a
retained subtree is decomposed. -/
theorem Cut.retract_mono {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (c : Cut) (hc : c.Valid Δ ρ) {a b : Carrier Δ c.source} (h : a ≤ b) :
    c.retract hc a ≤ c.retract hc b := by
  induction c with
  | keep s => exact h
  | erase s => exact le_refl _
  | prod c d ih₁ ih₂ =>
    exact pair_mono false (ih₁ hc.2.1 (pairLeft_mono false hc.1 h))
      (ih₂ hc.2.2 (pairRight_mono false hc.1 h))
      (ComparisonUnanchoredRoot.rootGuarded_le hc.1 h (a.shape_eq ρ hc.1.models)
        a.defined b.defined (by simp [ComparisonShape.subst, rootTag]))
  | sum c d ih₁ ih₂ =>
    exact pair_mono true (ih₁ hc.2.1 (pairLeft_mono true hc.1 h))
      (ih₂ hc.2.2 (pairRight_mono true hc.1 h))
      (ComparisonUnanchoredRoot.rootGuarded_le hc.1 h (a.shape_eq ρ hc.1.models)
        a.defined b.defined (by simp [ComparisonShape.subst, rootTag]))
  | fn c d ih₁ ih₂ =>
    exact function_mono (ih₁ hc.2.1 (functionDomain_mono hc.1 h))
      (ih₂ hc.2.2 (functionCodomain_mono hc.1 h))
      (ComparisonUnanchoredRoot.rootGuarded_futureLe hc.1 h (a.shape_eq ρ hc.1.models)
        a.defined b.defined rfl)

end ModalityInference.ComparisonShapeRetraction
