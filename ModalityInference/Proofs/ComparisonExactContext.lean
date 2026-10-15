import ModalityInference.ComparisonExactContext
import ModalityInference.Proofs.ComparisonTypes
import ModalityInference.Proofs.SubstitutionSupport

/-! Fixed support and exact composition for positive context instantiation. -/
namespace ModalityInference.ComparisonExactContext

/-- Each image is fixed, and each replaced identifier is a source binder. -/
def Scoped (p : Prepared) (action : Substitution) : Prop :=
  (∀ name image, (name, image) ∈ action.types →
    ComparisonInstance.typeAllowed p (.flex name) = true ∧
      (∀ v ∈ image.typeVars, ComparisonInstance.typeAllowed p v = false) ∧
      ∀ v ∈ image.modVars, ComparisonInstance.modeAllowed p v = false) ∧
  ∀ name image, (name, image) ∈ action.modes →
    ComparisonInstance.modeAllowed p (.flex name) = true ∧
      ∀ v ∈ image.vars, ComparisonInstance.modeAllowed p v = false

theorem scopeCheck_iff (p : Prepared) (action : Substitution) :
    scopeCheck p action = true ↔ Scoped p action := by
  simp [scopeCheck, Scoped, fixedType, fixedMode, List.all_eq_true]

theorem prepare_spec {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) :
    ComparisonInstance.targetFresh p = true ∧
      collect p total p.sourceType p.targetType {} = some action ∧ Scoped p action := by
  unfold prepare at h
  split at h
  · contradiction
  · next hf =>
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨selected, hc, hs⟩ := h
    split at hs
    · next hk =>
      cases hs
      exact ⟨by simpa using hf, hc, (scopeCheck_iff p action).mp hk⟩
    · contradiction

theorem prepare_scoped {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) : Scoped p action := (prepare_spec h).2.2

theorem Scoped.type_keys {p : Prepared} {action : Substitution} (h : Scoped p action)
    {name : Nat} (hn : name ∈ action.types.map Prod.fst) :
    ComparisonInstance.typeAllowed p (.flex name) = true := by
  obtain ⟨⟨n, t⟩, ht, hn⟩ := List.mem_map.mp hn
  cases hn
  exact (h.1 n t ht).1

theorem Scoped.mode_keys {p : Prepared} {action : Substitution} (h : Scoped p action)
    {name : Nat} (hn : name ∈ action.modes.map Prod.fst) :
    ComparisonInstance.modeAllowed p (.flex name) = true := by
  obtain ⟨⟨n, m⟩, hm, hn⟩ := List.mem_map.mp hn
  cases hn
  exact (h.2 n m hm).1

theorem Scoped.type_fixed {p : Prepared} {action : Substitution} (h : Scoped p action)
    (v : TypeVar) (hv : ComparisonInstance.typeAllowed p v = false) :
    action.type v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply Substitution.type_fresh
    exact fun hn => Bool.noConfusion (hv.symm.trans (h.type_keys hn))

theorem Scoped.mode_fixed {p : Prepared} {action : Substitution} (h : Scoped p action)
    (v : ModVar) (hv : ComparisonInstance.modeAllowed p v = false) :
    action.mode v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply Substitution.mode_fresh
    exact fun hn => Bool.noConfusion (hv.symm.trans (h.mode_keys hn))

theorem prepare_target_fixed {p : Prepared} {total : ModExpr → Bool} {action : Substitution}
    (h : prepare p total = some action) : action.ty p.targetType = p.targetType := by
  suffices he : p.targetType.subst action.type action.mode =
      p.targetType.subst TypeExpr.var ModExpr.var by simpa [Substitution.ty] using he
  apply TypeExpr.subst_congr
  · intro v hv
    apply (prepare_scoped h).type_fixed v
    have ht := (Bool.and_eq_true_iff.mp (prepare_spec h).1).1
    simp only [List.all_eq_true, Bool.not_eq_true', TypeExpr.mem_typeVariables] at ht
    exact ht v hv
  · intro v hv
    apply (prepare_scoped h).mode_fixed v
    have hm := (Bool.and_eq_true_iff.mp (prepare_spec h).1).2
    simp only [List.all_eq_true, Bool.not_eq_true', TypeExpr.mem_modeVariables] at hm
    exact hm v hv

private theorem lookup_filter_keys (xs : List (Nat × A)) (keys : List Nat) (n : Nat) :
    (xs.filter (fun p => !keys.contains p.1)).lookup n =
      if keys.contains n then none else xs.lookup n := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    rcases p with ⟨k, v⟩
    cases h : (n == k) <;> cases hn : keys.contains n <;> cases hk : keys.contains k <;>
      simp only [List.lookup_cons, List.filter_cons, hn, hk, h, Bool.not_true,
        Bool.not_false, Bool.false_eq_true, ↓reduceIte, ih]
    all_goals simp_all only [beq_iff_eq, Bool.false_eq_true, Bool.true_eq_false]

private theorem contains_keys (xs : List (Nat × A)) (n : Nat) :
    (xs.map Prod.fst).contains n = (xs.lookup n).isSome := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, v⟩
    cases h : (n == k) <;>
      simp only [List.map_cons, List.contains_cons, List.lookup_cons, h, ih,
        Bool.false_or, Bool.true_or, Option.isSome_some]

private theorem lookup_finish (before : Substitution) (after : CompareSubstitution) (n : Nat) :
    (finish before after).types.lookup n =
      ((before.types.lookup n).map after.ty).or (after.types.lookup n) := by
  change ((before.types.map (fun (pair : Nat × Ty) => (pair.1, after.ty pair.2))) ++
    after.types.filter (fun (pair : Nat × CompareTy) =>
      !(before.types.map Prod.fst).contains pair.1)).lookup n = _
  rw [List.lookup_append, lookup_map_values, lookup_filter_keys, contains_keys]
  cases before.types.lookup n <;> rfl

theorem finish_type (before : Substitution) (after : CompareSubstitution) (v : TypeVar) :
    (finish before after).type v = after.ty (before.type v) := by
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [CompareSubstitution.type, Substitution.type, lookup_finish]
    cases before.types.lookup n <;> rfl

theorem finish_mode (before : Substitution) (after : CompareSubstitution) (v : ModVar) :
    (finish before after).mode v = (before.mode v).subst after.mode :=
  Substitution.mode_compose v before { modes := after.modes }

theorem finish_modality (before : Substitution) (after : CompareSubstitution) (m : ModExpr) :
    m.subst (finish before after).mode = (m.subst before.mode).subst after.mode := by
  induction m <;> simp_all [ModExpr.subst, finish_mode]

theorem finish_ty (before : Substitution) (after : CompareSubstitution) (t : Ty) :
    (finish before after).ty t = after.ty (before.ty t) := by
  induction t <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    Substitution.ty, TypeExpr.subst, finish_type, finish_modality]

private theorem subst_eq_ty (action : Substitution) (t : Ty) :
    t.subst action.type action.mode = action.ty t := rfl

theorem finish_constraint (before : Substitution) (after : CompareSubstitution) (c : Constraint) :
    (finish before after).constraint c = after.constraint (before.constraint c) := by
  cases c <;> simp only [CompareSubstitution.constraint, Substitution.constraint,
    Constraint.subst, subst_eq_ty, finish_ty, finish_modality]
  rename_i v t
  cases v with
  | rigid n => rfl
  | flex n =>
    cases hb : before.types.lookup n <;> cases ha : after.types.lookup n <;>
      simp [lookup_finish, hb, ha]

theorem finish_bounds (before : Substitution) (after : CompareSubstitution) (bounds : Bounds) :
    (finish before after).bounds bounds = after.bounds (before.bounds bounds) := by
  simp only [CompareSubstitution.bounds, Substitution.bounds, List.map_map,
    Function.comp_def]
  exact List.map_congr_left fun c _ => finish_constraint before after c

theorem finish_rewrite_type (p : Prepared) (before : Substitution) (after : CompareSubstitution) :
    (finish before after).ty p.sourceType = after.ty (rewrite p before).sourceType :=
  finish_ty before after p.sourceType

theorem finish_rewrite_bounds (p : Prepared) (before : Substitution)
    (after : CompareSubstitution) :
    (finish before after).bounds p.sourceBounds = after.bounds (rewrite p before).sourceBounds :=
  finish_bounds before after p.sourceBounds

theorem rewrite_spec (p : Prepared) (action : Substitution) :
    (rewrite p action).sourceType = action.ty p.sourceType ∧
    (rewrite p action).sourceBounds = action.bounds p.sourceBounds ∧
    (rewrite p action).targetType = p.targetType ∧
    (rewrite p action).assumptions = p.assumptions ∧
    (rewrite p action).firstType = p.firstType ∧
    (rewrite p action).nextType = p.nextType ∧
    (rewrite p action).firstMode = p.firstMode ∧
    (rewrite p action).nextMode = p.nextMode := by
  simp [rewrite]

end ModalityInference.ComparisonExactContext
