import ModalityInference.ComparisonCapsuleContext
import ModalityInference.Proofs.ComparisonCapsuleSupport
import ModalityInference.Proofs.ComparisonCapsuleDichotomy

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonBody ComparisonCapsuleIntervals

private theorem target_residuals (a : Ty) (m : ModExpr) :
    typeResiduals (.modal a m) = residuals m ++ typeResiduals a := rfl

/-- Every request endpoint uses only residual operations from its input target
and inherited target action. Root composition does not introduce residuals. -/
theorem requests_endpoint_residuals (p : Prepared) (total : ModExpr → Bool)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    {r : Request} (hr : r ∈ requests p total fuel lower source target sm tm) :
    typeResiduals r.endpoint ⊆ typeResiduals target ++ residuals tm := by
  induction fuel generalizing lower source target sm tm with
  | zero => simp [requests] at hr
  | succ fuel ih =>
    cases source with
    | modal a m =>
      simp only [requests] at hr
      split at hr
      · exact ih _ _ _ _ _ hr
      · simp at hr
    | var v =>
      cases v with
      | flex n =>
        simp only [requests] at hr
        split at hr
        · cases List.mem_singleton.mp hr
          intro m hm
          simpa only [target_residuals, List.mem_append, or_comm] using hm
        · simp at hr
      | rigid n =>
        cases target <;> simp only [requests] at hr
        all_goals try simp at hr
        case modal b m =>
          intro v hv
          have h := ih _ _ _ _ _ hr hv
          simpa only [target_residuals, residuals, List.mem_append, or_assoc,
            or_left_comm] using h
    | unit | credit =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      case modal b m =>
        intro v hv
        have h := ih _ _ _ _ _ hr hv
        simpa only [target_residuals, residuals, List.mem_append, or_assoc,
          or_left_comm] using h
    | prod a b | sum a b | fn a b =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      case modal c m =>
        intro v hv
        have h := ih _ _ _ _ _ hr hv
        simpa only [target_residuals, residuals, List.mem_append, or_assoc,
          or_left_comm] using h
      all_goals
        rcases hr with hr | hr
        all_goals
          intro v hv
          have h := ih _ _ _ _ _ hr hv
          simp only [typeResiduals, ComparisonAnnotations.expressions, List.flatMap_append,
            List.mem_append, residuals, ModExpr.epsilon, List.not_mem_nil, or_false] at h ⊢
          tauto

/-- Collected endpoint residuals were all queried by the original body pass. -/
theorem collect_endpoint_residuals (p : Prepared) (total : ModExpr → Bool)
    {r : Request} (hr : r ∈ collect p total) :
    typeResiduals r.endpoint ⊆ typeResiduals p.targetType := by
  simpa only [ModExpr.epsilon, residuals, List.append_nil] using
    requests_endpoint_residuals p total _ _ _ _ _ _ hr

theorem collect_residuals_covered (p : Prepared) (total : ModExpr → Bool)
    {r : Request} (hr : r ∈ collect p total) :
    typeResiduals r.endpoint ⊆
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType).flatMap residuals := by
  intro m hm
  rw [List.flatMap_append]
  exact List.mem_append_right _ (collect_endpoint_residuals p total hr hm)

/-- Request actions use source names; endpoint syntax uses only target names. -/
theorem requests_support (p : Prepared) (total : ModExpr → Bool)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    {r : Request} (hr : r ∈ requests p total fuel lower source target sm tm) :
    ComparisonInstance.typeAllowed p (.flex r.name) = true ∧
      r.action.vars ⊆ source.modVars ∪ sm.vars ∧
      r.endpoint.modVars ⊆ target.modVars ∪ tm.vars ∧
      r.endpoint.typeVars ⊆ target.typeVars := by
  induction fuel generalizing lower source target sm tm with
  | zero => simp [requests] at hr
  | succ fuel ih =>
    cases source with
    | modal a m =>
      simp only [requests] at hr
      split at hr
      · have h := ih _ _ _ _ _ hr
        refine ⟨h.1, ?_, h.2.2.1, h.2.2.2⟩
        intro v hv
        have hh := h.2.1 hv
        simpa only [TypeExpr.modVars, ModExpr.vars, Finset.mem_union, or_assoc] using hh
      · simp at hr
    | var v =>
      cases v with
      | flex n =>
        simp only [requests] at hr
        split at hr
        · next ha =>
          cases List.mem_singleton.mp hr
          refine ⟨ha, ?_, ?_, ?_⟩
          · exact Finset.subset_union_right
          · exact Finset.Subset.refl _
          · exact Finset.Subset.refl _
        · simp at hr
      | rigid n =>
        cases target <;> simp only [requests] at hr
        all_goals try simp at hr
        case modal b m =>
          have h := ih _ _ _ _ _ hr
          refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
          intro v hv
          have hh := h.2.2.1 hv
          simpa only [TypeExpr.modVars, ModExpr.vars, Finset.mem_union, or_assoc] using hh
    | unit | credit =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      case modal b m =>
        have h := ih _ _ _ _ _ hr
        refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
        intro v hv
        have hh := h.2.2.1 hv
        simpa only [TypeExpr.modVars, ModExpr.vars, Finset.mem_union, or_assoc] using hh
    | prod a b | sum a b | fn a b =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      case modal c m =>
        have h := ih _ _ _ _ _ hr
        refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
        intro v hv
        have hh := h.2.2.1 hv
        simpa only [TypeExpr.modVars, ModExpr.vars, Finset.mem_union, or_assoc] using hh
      all_goals
        rcases hr with hr | hr
        all_goals
          have h := ih _ _ _ _ _ hr
          refine ⟨h.1, ?_, ?_, ?_⟩
          · intro v hv
            have hh := h.2.1 hv
            simp only [TypeExpr.modVars, ModExpr.vars, ModExpr.epsilon, Finset.mem_union,
              Finset.notMem_empty, or_false] at hh ⊢
            tauto
          · intro v hv
            have hh := h.2.2.1 hv
            simp only [TypeExpr.modVars, ModExpr.vars, ModExpr.epsilon, Finset.mem_union,
              Finset.notMem_empty, or_false] at hh ⊢
            tauto
          · intro v hv
            have hh := h.2.2.2 hv
            simp only [TypeExpr.typeVars, Finset.mem_union] at hh ⊢
            tauto

theorem collect_support (p : Prepared) (total : ModExpr → Bool)
    {r : Request} (hr : r ∈ collect p total) :
    ComparisonInstance.typeAllowed p (.flex r.name) = true ∧
      r.action.vars ⊆ p.sourceType.modVars ∧
      r.endpoint.modVars ⊆ p.targetType.modVars ∧
      r.endpoint.typeVars ⊆ p.targetType.typeVars := by
  simpa only [ModExpr.epsilon, ModExpr.vars, Finset.union_empty] using
    requests_support p total _ _ _ _ _ _ hr

/-- A collected occurrence carries only certified total source actions. -/
theorem requests_action_total {Δ : Bounds} (p : Prepared) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Entails Δ (.defined m))
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    (hsm : Entails Δ (.defined sm))
    {r : Request} (hr : r ∈ requests p total fuel lower source target sm tm) :
    Entails Δ (.defined r.action) := by
  induction fuel generalizing lower source target sm tm with
  | zero => simp [requests] at hr
  | succ fuel ih =>
    cases source with
    | modal a m =>
      simp only [requests] at hr
      split at hr
      · next hm =>
          exact ih _ _ _ _ _
            (Entails.defined_compose_iff.mpr ⟨htotal m hm, hsm⟩) hr
      · simp at hr
    | var v =>
      cases v with
      | flex n =>
        simp only [requests] at hr
        split at hr
        · cases List.mem_singleton.mp hr; exact hsm
        · simp at hr
      | rigid n =>
        cases target <;> simp only [requests] at hr
        all_goals try simp at hr
        exact ih _ _ _ _ _ hsm hr
    | unit | credit =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      exact ih _ _ _ _ _ hsm hr
    | prod a b | sum a b | fn a b =>
      cases target <;> simp only [requests] at hr
      all_goals try simp at hr
      case modal c m => exact ih _ _ _ _ _ hsm hr
      all_goals
        rcases hr with hr | hr
        all_goals exact ih _ _ _ _ _ (by first | exact hsm | exact fun _ _ => rfl) hr

theorem collect_action_total {Δ : Bounds} (p : Prepared) (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Entails Δ (.defined m))
    {r : Request} (hr : r ∈ collect p total) : Entails Δ (.defined r.action) :=
  requests_action_total p total htotal _ false p.sourceType p.targetType
    .epsilon .epsilon (fun _ _ => rfl) hr

/-- All annotations needed by a collected partial atomic interval are certified
by the production totality pass on the original pair of bodies. -/
theorem collect_peel_normal {p : Prepared} {ρ : TypeVar → ComparisonShape}
    (hΔ : p.assumptions.TypeBoundsDefined) (hρ : ComparisonShape.Models p.assumptions ρ)
    {fuel : Nat} {known : List ModExpr}
    (hknown : knownTotal fuel p.assumptions
      (ComparisonAnnotations.expressions p.sourceType ++
        ComparisonAnnotations.expressions p.targetType) = .success known)
    {r : Request} (hr : r ∈ collect p (isTotal known))
    (hatom : ComparisonPartialCapsule.Atomic ((CompareTy.ofTy r.endpoint).shape.subst ρ))
    (hpartial : ¬(CompareTy.ofTy r.endpoint).DefinedUnder p.assumptions) :
    Nonempty (ParsedNormal p.assumptions (isTotal known) r.endpoint) :=
  peel_normal_known hΔ hρ hknown r.endpoint hatom hpartial
    (collect_residuals_covered p _ hr)

end ModalityInference.ComparisonCapsuleContext
