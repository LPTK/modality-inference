import ModalityInference.Proofs.ComparisonShapeSelectionContext

/-! Shape selection preserves the free names of each substituted type image. -/

namespace ModalityInference.ComparisonShapeRetraction

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeletonCoordinates
open ComparisonInterpolation

theorem pairChild_support {P : TypeVar → Prop} {Q : ModVar → Prop}
    {a : CompareTy} (h : Supports P Q a) (right : Bool) : Supports P Q (pairChild right a) := by
  induction a with
  | prod a b ih₁ ih₂ | sum a b ih₁ ih₂ => cases right <;> first | exact h.1 | exact h.2
  | modal a m ih => exact ⟨ih h.1, h.2⟩
  | join a b ih₁ ih₂ | meet a b ih₁ ih₂ => exact ⟨ih₁ h.1, ih₂ h.2⟩
  | var | unit | credit | fn => trivial

theorem fnChild_support {P : TypeVar → Prop} {Q : ModVar → Prop}
    {a : CompareTy} (h : Supports P Q a) (contra : Bool) : Supports P Q (fnChild contra a) := by
  induction a with
  | fn a b ih₁ ih₂ => cases contra <;> first | exact h.1 | exact h.2
  | modal a m ih => exact ih h.1
  | join a b ih₁ ih₂ | meet a b ih₁ ih₂ =>
    cases contra <;> exact ⟨ih₁ h.1, ih₂ h.2⟩
  | var | unit | credit | prod | sum => trivial

theorem rootExpr_support {P : TypeVar → Prop} {Q : ModVar → Prop}
    {a : CompareTy} (h : Supports P Q a) : ∀ v ∈ (rootExpr a).vars, Q v := by
  induction a with
  | modal a m ih =>
    intro v hv
    exact (Finset.mem_union.mp hv).elim (ih h.1 v) (h.2 v)
  | join a b ih₁ ih₂ | meet a b ih₁ ih₂ =>
    intro v hv
    exact (Finset.mem_union.mp hv).elim (ih₁ h.1 v) (ih₂ h.2 v)
  | var | unit | credit | prod | sum | fn =>
    intro v hv
    cases hv

/-- Shape retraction introduces no free type or modality names. -/
theorem Cut.retract_support {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (c : Cut) (hc : c.Valid Δ φ) (a : Carrier Δ c.source) (h : Supports P Q a.type) :
    Supports P Q (c.retract hc a).type := by
  induction c with
  | keep s => exact h
  | erase s => exact ⟨trivial, fun _ hv => by cases hv⟩
  | prod c d ih₁ ih₂ =>
    exact ⟨⟨ih₁ hc.2.1 (pairLeft false hc.1 a) (pairChild_support h false),
      ih₂ hc.2.2 (pairRight false hc.1 a) (pairChild_support h true)⟩, rootExpr_support h⟩
  | sum c d ih₁ ih₂ =>
    exact ⟨⟨ih₁ hc.2.1 (pairLeft true hc.1 a) (pairChild_support h false),
      ih₂ hc.2.2 (pairRight true hc.1 a) (pairChild_support h true)⟩, rootExpr_support h⟩
  | fn c d ih₁ ih₂ =>
    exact ⟨⟨ih₁ hc.2.1 (functionDomain hc.1 a) (fnChild_support h true),
      ih₂ hc.2.2 (functionCodomain hc.1 a) (fnChild_support h false)⟩, rootExpr_support h⟩

theorem Cut.templateType_support {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    {P : TypeVar → Prop} {Q : ModVar → Prop}
    (choices : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hc : (Cut.ofTemplate choices ρ s).Valid Δ φ) (a : CompareTy)
    (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape (s.subst ρ)) (h : Supports P Q a) :
    Supports P Q (Cut.templateType choices ρ s hc a hs hd he) :=
  Cut.retract_support (Cut.ofTemplate choices ρ s) hc
    ⟨a, hs, hd, by simpa only [Cut.ofTemplate_source] using he⟩ h

end ModalityInference.ComparisonShapeRetraction
