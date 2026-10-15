import ModalityInference.ComparisonContext
import ModalityInference.Proofs.Substitution
import ModalityInference.Proofs.SubstitutionSupport
import ModalityInference.Proofs.SyntacticEquality

namespace ModalityInference.ComparisonContext

/-- Context images only replace source binders and contain no source binders. -/
def Scoped (p : Prepared) (action : Substitution) : Prop :=
  action.types = [] ∧ ∀ name image, (name, image) ∈ action.modes →
    ComparisonInstance.modeAllowed p (.flex name) = true ∧
      ∀ v ∈ image.vars, ComparisonInstance.modeAllowed p v = false

theorem scopeCheck_iff (p : Prepared) (action : Substitution) :
    scopeCheck p action = true ↔ Scoped p action := by
  simp [scopeCheck, Scoped, List.all_eq_true]

theorem prepare_scoped {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) : Scoped p action := by
  unfold prepare at h
  split at h
  · dsimp only at h
    split at h
    · next hs =>
      cases h
      exact (scopeCheck_iff p _).mp hs
    · contradiction
  · contradiction

theorem prepare_types {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) : action.types = [] := (prepare_scoped h).1

theorem prepare_keys {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) {name : Nat} (hn : name ∈ action.modes.map Prod.fst) :
    ComparisonInstance.modeAllowed p (.flex name) = true := by
  obtain ⟨⟨n, m⟩, hm, hn⟩ := List.mem_map.mp hn
  cases hn
  exact ((prepare_scoped h).2 n m hm).1

theorem prepare_image_fresh {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) {name : Nat} {image : ModExpr}
    (hi : (name, image) ∈ action.modes) :
    ∀ v ∈ image.vars, ComparisonInstance.modeAllowed p v = false :=
  ((prepare_scoped h).2 name image hi).2

theorem prepare_fixed {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) (v : ModVar)
    (hv : ComparisonInstance.modeAllowed p v = false) : action.mode v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply Substitution.mode_fresh
    exact fun hn => Bool.noConfusion (hv.symm.trans (prepare_keys h hn))

theorem finish_mode (before : Substitution) (after : CompareSubstitution) (v : ModVar) :
    (finish before after).mode v = (before.mode v).subst after.mode :=
  Substitution.mode_compose v before { modes := after.modes }

theorem finish_ty {before : Substitution} (hb : before.types = [])
    (after : CompareSubstitution) (t : Ty) :
    (finish before after).ty t = after.ty (before.ty t) := by
  have ht : before.type = TypeExpr.var := by
    funext v
    cases v <;> simp [Substitution.type, hb]
  have hm (m : ModExpr) : m.subst (finish before after).mode =
      (m.subst before.mode).subst after.mode :=
    (ModExpr.subst_compose m before { modes := after.modes }).symm
  induction t <;> simp_all [Substitution.ty, TypeExpr.subst, CompareSubstitution.ty,
    CompareTy.ofTy, CompareTy.subst]
  rfl

theorem finish_constraint {before : Substitution} (hb : before.types = [])
    (after : CompareSubstitution) (c : Constraint) :
    (finish before after).constraint c = after.constraint (before.constraint c) := by
  have hm (m : ModExpr) : m.subst (finish before after).mode =
      (m.subst before.mode).subst after.mode :=
    (ModExpr.subst_compose m before { modes := after.modes }).symm
  cases c <;> simp only [Substitution.constraint, Constraint.subst,
    CompareSubstitution.constraint, finish_ty hb, hm]
  all_goals try rfl
  rename_i v t
  cases v <;> simp [hb, finish]

/-- Composition retains every original source constraint, including its guards. -/
theorem finish_bounds {before : Substitution} (hb : before.types = [])
    (after : CompareSubstitution) (cs : Bounds) :
    (finish before after).bounds cs = after.bounds (before.bounds cs) := by
  simp only [CompareSubstitution.bounds, Substitution.bounds, List.map_map, Function.comp_def]
  exact List.map_congr_left fun c _ => finish_constraint hb after c

/-- The prepass transforms the body and bounds together without changing the
fixed assumptions or the source binder domains. -/
theorem rewrite_spec (p : Prepared) (action : Substitution) :
    (rewrite p action).sourceType = action.ty p.sourceType ∧
    (rewrite p action).sourceBounds = action.bounds p.sourceBounds ∧
    (rewrite p action).assumptions = p.assumptions ∧
    (rewrite p action).firstType = p.firstType ∧
    (rewrite p action).nextType = p.nextType ∧
    (rewrite p action).firstMode = p.firstMode ∧
    (rewrite p action).nextMode = p.nextMode := by
  simp [rewrite]

theorem prepare_target_fresh {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) : ComparisonInstance.targetFresh p = true := by
  unfold prepare at h
  split at h
  · assumption
  · contradiction

theorem prepare_target_fixed {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) : action.ty p.targetType = p.targetType := by
  suffices he : p.targetType.subst action.type action.mode =
      p.targetType.subst TypeExpr.var ModExpr.var by simpa [Substitution.ty] using he
  apply TypeExpr.subst_congr
  · intro v _
    cases v <;> simp [Substitution.type, prepare_types h]
  · intro v hv
    apply prepare_fixed h v
    have hm := (Bool.and_eq_true_iff.mp (prepare_target_fresh h)).2
    simp only [List.all_eq_true, Bool.not_eq_true', TypeExpr.mem_modeVariables] at hm
    exact hm v hv

end ModalityInference.ComparisonContext
