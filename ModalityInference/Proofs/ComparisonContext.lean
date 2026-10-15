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

private theorem bindMode_scoped {p : Prepared} {name : Nat} {image : ModExpr}
    {before after : Substitution} (hb : Scoped p before)
    (hn : ComparisonInstance.modeAllowed p (.flex name) = true)
    (hi : ∀ v ∈ image.vars, ComparisonInstance.modeAllowed p v = false)
    (h : ComparisonInstance.bindMode name image before = some after) : Scoped p after := by
  cases hl : before.modes.lookup name <;> simp [ComparisonInstance.bindMode, hl] at h
  · subst after
    refine ⟨hb.1, ?_⟩
    intro n m hm
    rcases List.mem_cons.mp hm with he | hm
    · rcases Prod.mk.inj he with ⟨rfl, rfl⟩
      exact ⟨hn, hi⟩
    · exact hb.2 n m hm
  · exact h.2 ▸ hb

private theorem matchMode_scoped {p : Prepared} {source target : ModExpr}
    {before after : Substitution} (hb : Scoped p before)
    (ht : ∀ v ∈ target.vars, ComparisonInstance.modeAllowed p v = false)
    (h : ComparisonInstance.matchMode p source target before = some after) : Scoped p after := by
  induction source generalizing target before after with
  | var v =>
    cases v with
    | flex n =>
      simp only [ComparisonInstance.matchMode] at h
      split at h
      · next hn => exact bindMode_scoped hb hn ht h
      · split at h
        · cases h
          exact hb
        · contradiction
    | rigid n =>
      cases target <;> try { simp only [ComparisonInstance.matchMode] at h; contradiction }
      case var v =>
        cases v <;> simp [ComparisonInstance.matchMode] at h
        exact h.2 ▸ hb
  | compose a b ia ib | meet a b ia ib | join a b ia ib
  | leftResidual a b ia ib | rightResidual a b ia ib =>
    cases target <;> simp [ComparisonInstance.matchMode] at h
    obtain ⟨middle, hm, ha⟩ := Option.bind_eq_some_iff.mp h
    simp only [ModExpr.vars, Finset.mem_union, or_imp, forall_and] at ht
    exact ib (ia hb ht.1 hm) ht.2 ha
  | const m =>
    cases target <;> simp [ComparisonInstance.matchMode] at h
    exact h.2 ▸ hb
  | close a ia | closeInv a ia | future a ia | capture a ia =>
    cases target <;> simp [ComparisonInstance.matchMode] at h
    exact ia hb (by simpa only [ModExpr.vars] using ht) h

private theorem collect_scoped {p : Prepared} {total : ModExpr → Bool} {source target : Ty}
    {before after : Substitution} (hb : Scoped p before)
    (ht : ∀ v ∈ target.modVars, ComparisonInstance.modeAllowed p v = false)
    (h : collect p total source target before = some after) : Scoped p after := by
  induction source generalizing target before after with
  | var v | unit | credit =>
    cases target <;> simp only [collect, Option.some.injEq] at h <;> exact h ▸ hb
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    cases target <;> simp only [collect, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    all_goals try exact h ▸ hb
    obtain ⟨middle, hm, ha⟩ := h
    simp only [TypeExpr.modVars, Finset.mem_union, or_imp, forall_and] at ht
    exact ib (ia hb ht.1 hm) ht.2 ha
  | modal a m ia =>
    cases target <;> simp only [collect, bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    all_goals try exact h ▸ hb
    obtain ⟨middle, hm, ha⟩ := h
    simp only [TypeExpr.modVars, Finset.mem_union, or_imp, forall_and] at ht
    split at ha
    · cases ha
      exact ia hb ht.1 hm
    · exact matchMode_scoped (ia hb ht.1 hm) ht.2 ha

theorem prepare_scoped {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) : Scoped p action := by
  unfold prepare at h
  split at h
  · next hf =>
    apply collect_scoped (by simp [Scoped]) _ h
    have hm := (Bool.and_eq_true_iff.mp hf).2
    simpa only [List.all_eq_true, Bool.not_eq_true', TypeExpr.mem_modeVariables] using hm
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
