import ModalityInference.Core.Scoping
import ModalityInference.Proofs.VariableOccurrences

/-! Syntactic support and fixed points of simultaneous substitutions. -/
namespace ModalityInference

@[simp] theorem ModExpr.subst_id (m : ModExpr) : m.subst ModExpr.var = m := by
  induction m <;> simp_all [ModExpr.subst]

theorem ModExpr.subst_congr (m : ModExpr) {σ τ : ModVar → ModExpr}
    (h : ∀ v ∈ m.vars, σ v = τ v) : m.subst σ = m.subst τ := by
  induction m <;> simp_all [ModExpr.subst, ModExpr.vars, or_imp, forall_and]

@[simp] theorem TypeExpr.subst_id (a : Ty) : a.subst TypeExpr.var ModExpr.var = a := by
  induction a <;> simp_all [TypeExpr.subst]

theorem TypeExpr.subst_congr (a : Ty) {σ τ : TypeVar → Ty} {μ ν : ModVar → ModExpr}
    (ht : ∀ v ∈ a.typeVars, σ v = τ v) (hm : ∀ v ∈ a.modVars, μ v = ν v) :
    a.subst σ μ = a.subst τ ν := by
  induction a <;> simp_all [TypeExpr.subst, TypeExpr.typeVars, TypeExpr.modVars,
    or_imp, forall_and]
  exact ModExpr.subst_congr _ hm.2

theorem TypeExpr.mem_typeVars_subst (a : Ty) (σ : TypeVar → Ty) (μ : ModVar → ModExpr)
    (v : TypeVar) : v ∈ (a.subst σ μ).typeVars ↔ ∃ w ∈ a.typeVars, v ∈ (σ w).typeVars := by
  induction a <;> simp_all [TypeExpr.subst, TypeExpr.typeVars, or_and_right, exists_or]

theorem Substitution.type_fresh (σ : Substitution) {n}
    (hn : n ∉ σ.types.map Prod.fst) : σ.type (.flex n) = .var (.flex n) := by
  have he : σ.types.lookup n = none := List.lookup_eq_none_iff.mpr fun p hp =>
    bne_iff_ne.mpr (fun h => hn (List.mem_map.mpr ⟨p, hp, h.symm⟩))
  simp [Substitution.type, he]

theorem Substitution.ty_fixed (σ : Substitution) (a : Ty) (hm : σ.modes = [])
    (ht : ∀ n ∈ σ.types.map Prod.fst, TypeVar.flex n ∉ a.typeVars) : σ.ty a = a := by
  suffices h : a.subst σ.type σ.mode = a.subst TypeExpr.var ModExpr.var by simpa using h
  apply a.subst_congr
  · intro v hv
    cases v with
    | rigid _ => rfl
    | flex n => exact σ.type_fresh (fun hn => ht n hn hv)
  · intro v _
    cases v <;> simp [Substitution.mode, hm]

theorem TypeExpr.singleType_avoids (a t : Ty) (n k : Nat)
    (ht : TypeVar.flex k ∉ t.typeVars)
    (ha : k = n ∨ TypeVar.flex k ∉ a.typeVars) :
    TypeVar.flex k ∉ (({types := [(n,t)]} : Substitution).ty a).typeVars := by
  simp only [Substitution.ty, TypeExpr.mem_typeVars_subst, not_exists, not_and]
  intro v hv
  cases v with
  | rigid j => simp [Substitution.type, TypeExpr.typeVars]
  | flex j =>
    by_cases hj : j = n
    · subst j; simpa [Substitution.type] using ht
    · rw [Substitution.type_fresh _ (by simpa using hj)]
      rcases ha with rfl | ha <;> simp_all [TypeExpr.typeVars, ne_comm]
      exact fun h => ha (h ▸ hv)

theorem Substitution.extendType_keys (σ : Substitution) {n t}
    (hn : n ∉ σ.types.map Prod.fst) :
    ((σ.extendType n t).types.map Prod.fst) = n :: σ.types.map Prod.fst := by
  have hf : σ.types.filter (fun p => p.1 != n) = σ.types :=
    List.filter_eq_self.mpr fun p hp =>
      bne_iff_ne.mpr (fun h => hn (List.mem_map.mpr ⟨p, hp, h⟩))
  simp [Substitution.extendType, hf, List.map_map, Function.comp_def]

theorem Substitution.extendType_acyclic {σ : Substitution} {n t} (hσ : σ.Acyclic)
    (hn : n ∉ σ.types.map Prod.fst)
    (ht : ∀ k ∈ n :: σ.types.map Prod.fst, TypeVar.flex k ∉ t.typeVars) :
    (σ.extendType n t).Acyclic := by
  refine ⟨?_, hσ.2.1, ?_, hσ.2.2.2⟩
  · simpa only [σ.extendType_keys hn, List.nodup_cons] using And.intro hn hσ.1
  · intro j u hu k hk
    rw [σ.extendType_keys hn] at hk
    simp only [Substitution.extendType, List.mem_cons, List.mem_map, List.mem_filter,
      Prod.exists, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl⟩ | ⟨j, b, ⟨hb, _⟩, rfl, rfl⟩
    · exact ht k hk
    · exact b.singleType_avoids t n k (ht k hk)
        ((List.mem_cons.mp hk).imp id (fun hk => hσ.2.2.1 j b hb k hk))

theorem Substitution.type_avoids {σ : Substitution} (hσ : σ.Acyclic) {k}
    (hk : k ∈ σ.types.map Prod.fst) (v : TypeVar) :
    TypeVar.flex k ∉ (σ.type v).typeVars := by
  cases v with
  | rigid j => simp [Substitution.type, TypeExpr.typeVars]
  | flex j =>
    cases he : σ.types.lookup j with
    | some a =>
      obtain ⟨before, after, hs, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [Substitution.type, he, Option.getD_some] using
        (hσ.2.2.1 j a (by simp [hs]) k hk)
    | none =>
      simp only [Substitution.type, he, Option.getD_none, TypeExpr.typeVars,
        Finset.mem_singleton, TypeVar.flex.injEq]
      rintro rfl
      obtain ⟨⟨j, a⟩, ha, rfl⟩ := List.mem_map.mp hk
      simpa using (List.lookup_eq_none_iff.mp he) (j, a) ha

theorem Substitution.ty_avoids {σ : Substitution} (hσ : σ.Acyclic) {k}
    (hk : k ∈ σ.types.map Prod.fst) (a : Ty) : TypeVar.flex k ∉ (σ.ty a).typeVars := by
  simp only [Substitution.ty, TypeExpr.mem_typeVars_subst, not_exists, not_and]
  exact fun v _ => σ.type_avoids hσ hk v

@[simp] theorem Substitution.empty_constraint (c : Constraint) :
    ({} : Substitution).constraint c = c := by
  have ht : ({} : Substitution).type = TypeExpr.var := by funext v; cases v <;> rfl
  have hm : ({} : Substitution).mode = ModExpr.var := by funext v; cases v <;> rfl
  cases c <;> simp [Substitution.constraint, Constraint.subst, Substitution.ty, ht, hm]
  rename_i v a
  cases v <;> simp

@[simp] theorem Substitution.empty_bounds (cs : Bounds) :
    ({} : Substitution).bounds cs = cs := by
  induction cs <;> simp_all [Substitution.bounds]

end ModalityInference
