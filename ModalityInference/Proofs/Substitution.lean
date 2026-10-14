import ModalityInference.Core.Syntax

/-! Composition of simultaneous type and modality substitutions. -/
namespace ModalityInference

theorem lookup_map_values (xs : List (Nat × A)) (f : A → B) (n : Nat) :
    (xs.map (fun (k, v) => (k, f v))).lookup n = (xs.lookup n).map f := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, v⟩
    cases h : (n == k) <;> simp [List.lookup_cons, h, ih]

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

private theorem lookup_compose (old : List (Nat × A)) (new : List (Nat × B))
    (f : A → B) (n : Nat) :
    ((old.map (fun (p : Nat × A) => (p.1, f p.2))) ++
      new.filter (fun (p : Nat × B) => !(old.map Prod.fst).contains p.1)).lookup n =
      ((old.lookup n).map f).or (new.lookup n) := by
  rw [List.lookup_append, lookup_map_values, lookup_filter_keys, contains_keys]
  cases old.lookup n <;> rfl

theorem Substitution.type_compose (v : TypeVar) (σ τ : Substitution) :
    (τ.compose σ).type v = τ.ty (σ.type v) := by
  cases v with
  | flex n =>
    simp only [Substitution.type, Substitution.compose, lookup_compose]
    cases σ.types.lookup n <;> rfl
  | rigid n => rfl

theorem Substitution.mode_compose (v : ModVar) (σ τ : Substitution) :
    (τ.compose σ).mode v = (σ.mode v).subst τ.mode := by
  cases v with
  | flex n =>
    simp only [Substitution.mode, Substitution.compose, lookup_compose]
    cases σ.modes.lookup n <;> rfl
  | rigid n => rfl

theorem ModExpr.subst_compose (m : ModExpr) (σ τ : Substitution) :
    (m.subst σ.mode).subst τ.mode = m.subst (τ.compose σ).mode := by
  induction m <;> simp_all [ModExpr.subst, Substitution.mode_compose]

theorem Substitution.ty_compose (t : Ty) (σ τ : Substitution) :
    τ.ty (σ.ty t) = (τ.compose σ).ty t := by
  induction t <;>
    simp_all [Substitution.ty, TypeExpr.subst, Substitution.type_compose, ModExpr.subst_compose]

private theorem subst_eq_ty (σ : Substitution) (t : Ty) :
    t.subst σ.type σ.mode = σ.ty t := rfl

private theorem lookup_types_compose (σ τ : Substitution) (n : Nat) :
    (τ.compose σ).types.lookup n = ((σ.types.lookup n).map τ.ty).or (τ.types.lookup n) :=
  lookup_compose σ.types τ.types τ.ty n

theorem Substitution.constraint_compose (c : Constraint) (σ τ : Substitution) :
    τ.constraint (σ.constraint c) = (τ.compose σ).constraint c := by
  cases c <;>
    simp only [Substitution.constraint, Constraint.subst, subst_eq_ty,
      Substitution.ty_compose, ModExpr.subst_compose]
  rename_i v t
  cases v with
  | rigid n => simp [Substitution.ty_compose]
  | flex n =>
    cases hs : σ.types.lookup n <;> cases ht : τ.types.lookup n <;>
      simp [lookup_types_compose, hs, ht, Substitution.ty_compose]

theorem Substitution.bounds_compose (cs : Bounds) (σ τ : Substitution) :
    τ.bounds (σ.bounds cs) = (τ.compose σ).bounds cs := by
  simp only [Substitution.bounds, List.map_map, Function.comp_def, Substitution.constraint_compose]

theorem Scheme.subst_body_action (s : Scheme) (σ : Substitution) :
    (s.subst σ).body = (s.substitutionAction σ).ty s.body := by
  simp only [Scheme.subst, Scheme.substitutionAction, Scheme.binderRenaming,
    Scheme.instantiate, Substitution.ty_compose]

theorem Scheme.subst_bounds_action (s : Scheme) (σ : Substitution) :
    (s.subst σ).bounds = (s.substitutionAction σ).bounds s.bounds := by
  simp only [Scheme.subst, Scheme.substitutionAction, Scheme.binderRenaming,
    Scheme.instantiate, Substitution.bounds_compose]

end ModalityInference
