import ModalityInference.ComparisonFrozenContext
import ModalityInference.Proofs.ComparisonContextSupport

namespace ModalityInference.ComparisonFrozenContext

theorem sourceTotal_subst_eq {p : Prepared} {total : ModExpr → Bool}
    {m : ModExpr} {ms : ModVar → ModExpr}
    (hf : ∀ v, ComparisonInstance.modeAllowed p v = false → ms v = .var v)
    (hm : sourceTotal p total m = true) : m.subst ms = m := by
  have hh := (Bool.and_eq_true_iff.mp hm).2
  simp only [ComparisonExactContext.fixedMode, List.all_eq_true, Bool.not_eq_true'] at hh
  simpa only [ModExpr.subst_id] using
    (ModExpr.subst_congr m (fun v hv => hf v (hh v ((m.mem_freeVariables v).mpr hv))))

theorem normalizeOuterFuel_bounded (fuel : Nat) {t : Ty} {nt nm : Nat}
    (ht : t.Bounded nt nm) :
    (ComparisonPartialModes.normalizeOuterFuel fuel t).Bounded nt nm := by
  induction fuel generalizing t with
  | zero => exact ht
  | succ fuel ih =>
    cases t with
    | modal a m =>
      cases m with
      | compose m n => exact ih ⟨⟨ht.1, ht.2.1⟩, ht.2.2⟩
      | _ =>
        simp only [ComparisonPartialModes.normalizeOuterFuel]
        split
        · exact ih ht.1
        · exact ht
    | _ => exact ht

theorem normalizeOuter_bounded {t : Ty} {nt nm : Nat} (ht : t.Bounded nt nm) :
    (ComparisonPartialModes.normalizeOuter t).Bounded nt nm := normalizeOuterFuel_bounded _ ht

theorem peelFuel_bounded (total : ModExpr → Bool) (fuel : Nat) {t : Ty} {nt nm : Nat}
    (ht : t.Bounded nt nm) : (ComparisonBody.peelFuel total fuel t).base.Bounded nt nm := by
  induction fuel generalizing t with
  | zero => exact ht
  | succ fuel ih =>
    have hn := normalizeOuter_bounded ht
    generalize he : ComparisonPartialModes.normalizeOuter t = a at hn ⊢
    cases a with
    | modal a m =>
      simp only [ComparisonBody.peelFuel, he]
      split
      · exact ih hn.1
      · exact hn
    | _ => simpa only [ComparisonBody.peelFuel, he] using hn

theorem peel_bounded (total : ModExpr → Bool) {t : Ty} {nt nm : Nat}
    (ht : t.Bounded nt nm) : (ComparisonBody.peel total t).base.Bounded nt nm :=
  peelFuel_bounded total _ ht

theorem requestsStep_bounded (p : Prepared) (total : ModExpr → Bool)
    (next : Ty → Ty → List Request) {nt nm : Nat}
    (ih : ∀ source target, target.Bounded nt nm →
      ∀ request ∈ next source target, request.2.Bounded nt nm)
    (source target : Ty) (ht : target.Bounded nt nm) :
    ∀ request ∈ requestsStep p total next source target, request.2.Bounded nt nm := by
  intro request hr
  cases source with
  | var v =>
    cases v with
    | rigid n => simp [requestsStep] at hr
    | flex n =>
      simp only [requestsStep] at hr
      split at hr
      · obtain rfl := List.mem_singleton.mp hr; exact ht
      · exact (List.not_mem_nil hr).elim
  | unit | credit => simp [requestsStep] at hr
  | modal a m =>
    cases target <;> simp only [requestsStep] at hr
    all_goals try exact (List.not_mem_nil hr).elim
    split at hr
    · obtain rfl := List.mem_singleton.mp hr; exact ht
    · exact (List.not_mem_nil hr).elim
  | prod a b | sum a b | fn a b =>
    cases target <;> simp only [requestsStep] at hr
    all_goals try exact (List.not_mem_nil hr).elim
    all_goals rcases List.mem_append.mp hr with hr | hr
    all_goals first | exact ih _ _ ht.1 _ hr | exact ih _ _ ht.2 _ hr

theorem requests_bounded (p : Prepared) (total : ModExpr → Bool) (fuel : Nat)
    (source target : Ty) {nt nm : Nat} (ht : target.Bounded nt nm) :
    ∀ request ∈ requests p total fuel source target, request.2.Bounded nt nm := by
  induction fuel generalizing source target with
  | zero => simp [requests]
  | succ fuel ih =>
    exact requestsStep_bounded p total _ (fun s t ht => ih s t ht) _ _ (peel_bounded total ht)

theorem independent_bounded {p : Prepared} {total : ModExpr → Bool}
    (ht : p.targetType.Bounded p.nextType p.nextMode) :
    (independent p total).Bounded p.nextType p.nextMode := by
  apply ComparisonContext.solvePriorityComponents_property _ _ _ _ _
    (Substitution.Bounded p.nextType p.nextMode)
    (fun request : Request => request.2.Bounded p.nextType p.nextMode)
    (by constructor <;> simp)
    (requests_bounded p total _ _ _ ht)
  intro request hreq before after hb hm
  exact ComparisonInstance.matchType_bounded hm hreq hb

theorem prepare_spec {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) :
    ComparisonInstance.targetFresh p = true ∧ independent p total = action ∧
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

theorem prepare_scoped {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) : ComparisonExactContext.Scoped p action :=
  (prepare_spec h).2.2

theorem prepare_bounded {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) (ht : p.targetType.Bounded p.nextType p.nextMode) :
    action.Bounded p.nextType p.nextMode := (prepare_spec h).2.1 ▸ independent_bounded ht

end ModalityInference.ComparisonFrozenContext
