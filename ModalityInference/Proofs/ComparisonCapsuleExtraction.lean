import ModalityInference.Proofs.ComparisonCapsuleGroups
import ModalityInference.Proofs.ComparisonProductProjection

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonCapsuleIntervals ComparisonDefinedCovers ComparisonStructuralProjection

def ContextHolds (Δ : Bounds) (types : TypeVar → CompareTy) (modes : ModVar → ModExpr)
    (lower : Bool) (source target : Ty) (sm tm : ModExpr) : Prop :=
  Refines Δ lower (.modal (.ofTy target) tm)
    (.modal ((CompareTy.ofTy source).subst types modes) (sm.subst modes))

private theorem ContextHolds.source_modal {Δ : Bounds} {types : TypeVar → CompareTy}
    {modes : ModVar → ModExpr} {lower : Bool} {a target : Ty} {m sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower (.modal a m) target sm tm) :
    ContextHolds Δ types modes lower a target (.compose m sm) tm := by
  cases lower
  · exact (AlgebraSubtype.shaped (.composeRev (a := (CompareTy.ofTy a).subst types modes)
      h.wellShaped_left)).trans h
  · exact h.trans (.shaped (.compose (a := (CompareTy.ofTy a).subst types modes)
      h.wellShaped_right))

private theorem ContextHolds.target_modal {Δ : Bounds} {types : TypeVar → CompareTy}
    {modes : ModVar → ModExpr} {lower : Bool} {source a : Ty} {m sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower source (.modal a m) sm tm) :
    ContextHolds Δ types modes lower source a sm (.compose m tm) := by
  cases lower
  · exact h.trans (.shaped (.compose (a := .ofTy a) h.wellShaped_right))
  · exact (AlgebraSubtype.shaped (.composeRev (a := .ofTy a) h.wellShaped_left)).trans h

private theorem ContextHolds.prod {Δ : Bounds} (hΔ : Residual Δ)
    {types : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    {lower : Bool} {a b c d : Ty} {sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower (.prod a b) (.prod c d) sm tm) :
    ContextHolds Δ types modes lower a c sm tm ∧
      ContextHolds Δ types modes lower b d sm tm := by
  cases lower <;> exact product_inversion hΔ h

private theorem ContextHolds.sum {Δ : Bounds} (hΔ : Residual Δ)
    {types : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    {lower : Bool} {a b c d : Ty} {sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower (.sum a b) (.sum c d) sm tm) :
    ContextHolds Δ types modes lower a c sm tm ∧
      ContextHolds Δ types modes lower b d sm tm := by
  cases lower <;> exact sum_inversion hΔ h

private theorem ContextHolds.fn {Δ : Bounds} (hΔ : Residual Δ)
    {types : TypeVar → CompareTy} {modes : ModVar → ModExpr}
    {lower : Bool} {a b c d : Ty} {sm tm : ModExpr}
    (h : ContextHolds Δ types modes lower (.fn a b) (.fn c d) sm tm) :
    ContextHolds Δ types modes (!lower) a c .epsilon .epsilon ∧
      ContextHolds Δ types modes lower b d .epsilon .epsilon := by
  cases lower
  · have hs := function_inversion hΔ h
    exact ⟨.congr hs.1 (.refl (by intro η _; rfl)),
      .congr hs.2 (.refl (by intro η _; rfl))⟩
  · have hs := function_inversion hΔ h
    exact ⟨.congr hs.1 (.refl (by intro η _; rfl)),
      .congr hs.2 (.refl (by intro η _; rfl))⟩

/-- Every emitted interval is a consequence of the original comparison.
The modality images and internal type images may be partial; totality is needed
only when reconstructing a replacement from the resulting scalar intervals. -/
theorem requests_algebra {p : Prepared} {types : TypeVar → CompareTy}
    {modes : ModVar → ModExpr} (hΔ : Residual p.assumptions) (total : ModExpr → Bool)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    (h : ContextHolds p.assumptions types modes lower source target sm tm) :
    ∀ r ∈ requests p total fuel lower source target sm tm,
      (r.mapAction modes).AlgebraHolds p.assumptions (types (.flex r.name)) := by
  induction fuel generalizing lower source target sm tm with
  | zero => simp [requests]
  | succ fuel ih =>
    cases source with
    | var v =>
      cases v with
      | flex n =>
        simp only [requests]
        split
        · intro r hr
          obtain rfl := List.mem_singleton.mp hr
          exact h
        · simp
      | rigid n =>
        cases target <;> simp only [requests]
        case modal a m => exact ih lower (.var (.rigid n)) a sm (.compose m tm) h.target_modal
        all_goals simp
    | modal a m =>
      simp only [requests]
      split
      · exact ih lower a target (.compose m sm) tm h.source_modal
      · simp
    | unit =>
      cases target <;> simp only [requests]
      case modal a m => exact ih lower .unit a sm (.compose m tm) h.target_modal
      all_goals simp
    | credit =>
      cases target <;> simp only [requests]
      case modal a m => exact ih lower .credit a sm (.compose m tm) h.target_modal
      all_goals simp
    | prod a b =>
      cases target <;> simp only [requests]
      case modal c m => exact ih lower (.prod a b) c sm (.compose m tm) h.target_modal
      case prod c d =>
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact ih lower a c sm tm (h.prod hΔ).1 r hr
        · exact ih lower b d sm tm (h.prod hΔ).2 r hr
      all_goals simp
    | sum a b =>
      cases target <;> simp only [requests]
      case modal c m => exact ih lower (.sum a b) c sm (.compose m tm) h.target_modal
      case sum c d =>
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact ih lower a c sm tm (h.sum hΔ).1 r hr
        · exact ih lower b d sm tm (h.sum hΔ).2 r hr
      all_goals simp
    | fn a b =>
      cases target <;> simp only [requests]
      case modal c m => exact ih lower (.fn a b) c sm (.compose m tm) h.target_modal
      case fn c d =>
        intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact ih (!lower) a c .epsilon .epsilon (h.fn hΔ).1 r hr
        · exact ih lower b d .epsilon .epsilon (h.fn hΔ).2 r hr
      all_goals simp

/-- The executable collection preserves every original body witness, including
arbitrary partial images and shared source modality expressions. -/
theorem collect_algebra {p : Prepared} {types : TypeVar → CompareTy}
    {modes : ModVar → ModExpr} (hΔ : Residual p.assumptions) (total : ModExpr → Bool)
    (h : AlgebraSubtype p.assumptions ((CompareTy.ofTy p.sourceType).subst types modes)
      (.ofTy p.targetType)) :
    ∀ r ∈ collect p total,
      (r.mapAction modes).AlgebraHolds p.assumptions (types (.flex r.name)) :=
  requests_algebra hΔ total _ _ _ _ _ _ (.congr h (.refl (by intro η _; rfl)))

end ModalityInference.ComparisonCapsuleContext
