import ModalityInference.ComparisonCompoundSpine
import ModalityInference.Proofs.ComparisonModalSpine
import ModalityInference.Proofs.ComparisonContextSupport

namespace ModalityInference.ComparisonCompoundSpine

theorem requests_support (p : Prepared) {source target : Ty} {request : Request}
    (h : request ∈ requests p source target) : request.2.vars ⊆ target.modVars := by
  induction source generalizing target with
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    cases target <;> simp only [requests, List.mem_append, List.not_mem_nil] at h
    all_goals
      intro v hv
      rcases h with h | h
      · exact Finset.mem_union_left _ (ia h hv)
      · exact Finset.mem_union_right _ (ib h hv)
  | modal a m ia =>
    simp only [requests] at h
    split at h
    · cases hf : ComparisonModalSpine.factor a target with
      | none => simp [hf] at h
      | some ms =>
        simp only [hf, List.mem_singleton] at h
        subst request
        exact ComparisonModalSpine.factor_recompose_support hf
    · cases target <;> simp only [List.not_mem_nil] at h
      intro v hv
      exact Finset.mem_union_left _ (ia h hv)
  | var | unit | credit => simp [requests] at h

theorem requests_bounded (p : Prepared) {source target : Ty}
    (ht : target.Bounded p.nextType p.nextMode) :
    ∀ request ∈ requests p source target, request.2.Bounded p.nextMode := by
  intro request hr
  apply (ModExpr.bounded_iff _ _).mpr
  intro v hv
  exact ((TypeExpr.bounded_iff _ _ _).mp ht).2 v (requests_support p hr hv)

theorem independent_bounded {p : Prepared}
    (ht : p.targetType.Bounded p.nextType p.nextMode) :
    (independent p).Bounded p.nextType p.nextMode := by
  apply ComparisonContext.solvePriorityComponents_property _ _ _ _ _
    (Substitution.Bounded p.nextType p.nextMode)
    (fun request : Request => request.2.Bounded p.nextMode)
    (Substitution.bounded_empty _ _) (requests_bounded p ht)
  intro request hreq before after hb hm
  exact ComparisonInstance.matchMode_bounded hm hreq hb

theorem prepare_spec {p : Prepared} {action : Substitution}
    (h : prepare p = some action) :
    ComparisonInstance.targetFresh p = true ∧ independent p = action ∧
      ComparisonExactContext.Scoped p action := by
  unfold prepare at h
  split at h
  · contradiction
  · next hf =>
    dsimp only at h
    split at h
    · next hk =>
      cases h
      exact ⟨by simpa using hf, rfl, (ComparisonExactContext.scopeCheck_iff p _).mp hk⟩
    · contradiction

theorem prepare_scoped {p : Prepared} {action : Substitution}
    (h : prepare p = some action) : ComparisonExactContext.Scoped p action :=
  (prepare_spec h).2.2

theorem prepare_bounded {p : Prepared} {action : Substitution}
    (h : prepare p = some action) (ht : p.targetType.Bounded p.nextType p.nextMode) :
    action.Bounded p.nextType p.nextMode := (prepare_spec h).2.1 ▸ independent_bounded ht

end ModalityInference.ComparisonCompoundSpine
