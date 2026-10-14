import ModalityInference.Proofs.SolverImages

/-! Later solver substitutions preserve the equations already eliminated. -/
namespace ModalityInference

def Substitution.ExtendsTypes (τ σ : Substitution) : Prop :=
  ∀ v, τ.ty (σ.type v) = τ.type v

theorem Substitution.extendsTypes_self {σ : Substitution} (hm : σ.modes = [])
    (hσ : σ.Acyclic) : σ.ExtendsTypes σ :=
  fun v => σ.ty_fixed (σ.type v) hm (fun _ hk => σ.type_avoids hσ hk v)

theorem Substitution.ExtendsTypes.ty {τ σ : Substitution} (h : τ.ExtendsTypes σ)
    (hm : σ.modes = []) (a : Ty) : τ.ty (σ.ty a) = τ.ty a := by
  induction a <;> simp_all [Substitution.ty, TypeExpr.subst, σ.mode_eq_var hm, ExtendsTypes]

theorem Substitution.extendsTypes_singleType {τ : Substitution} {n a}
    (h : τ.ty a = τ.type (.flex n)) : τ.ExtendsTypes {types := [(n, a)]} := by
  intro v
  cases v with
  | rigid k => rfl
  | flex k =>
    by_cases hk : k = n
    · subst k; simpa [Substitution.type] using h
    · have hkn : (k == n) = false := by simpa using hk
      simp [Substitution.type, List.lookup_cons, hkn, Substitution.ty, TypeExpr.subst]

theorem Substitution.ExtendsTypes.extendType_single {τ σ : Substitution} {n a}
    (h : τ.ExtendsTypes (σ.extendType n a)) : τ.ExtendsTypes {types := [(n, a)]} := by
  apply Substitution.extendsTypes_singleType
  simpa only [Substitution.extendType, Substitution.type, List.lookup_cons,
    beq_self_eq_true, Option.getD_some] using h (.flex n)

theorem Substitution.ExtendsTypes.extendType_previous {τ σ : Substitution} {n a}
    (h : τ.ExtendsTypes (σ.extendType n a)) (hn : n ∉ σ.types.map Prod.fst) :
    τ.ExtendsTypes σ := by
  intro v
  have hv := h v
  rw [Substitution.extendType_type hn, h.extendType_single.ty rfl] at hv
  exact hv

theorem solverStep_modes {s t : SolverState} (h : solverStep s = .success t) :
    t.substitution.modes = s.substitution.modes := by
  rcases solverStep_substitution_cases h with heq | ⟨c, rest, n, a, hp, he, hn, hsub, ht, hb⟩
  · rw [heq]
  · rw [hsub]; rfl

theorem solverStep_extendsTypes_previous {s t : SolverState} {τ : Substitution}
    (hσ : s.substitution.Acyclic) (h : solverStep s = .success t)
    (he : τ.ExtendsTypes t.substitution) : τ.ExtendsTypes s.substitution := by
  rcases solverStep_substitution_cases h with heq | ⟨c, rest, n, a, hp, hec, hn, hsub, ht, hb⟩
  · exact heq ▸ he
  · rw [hsub] at he
    exact he.extendType_previous (s.substitution.normalized_equal_fresh hσ hec).1

theorem runWorklist_extendsTypes {fuel s t} (hm : s.substitution.modes = [])
    (hσ : s.substitution.Acyclic) (h : runWorklist fuel s = .success t) :
    t.substitution.ExtendsTypes s.substitution := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h
      exact Substitution.extendsTypes_self hm hσ
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact solverStep_extendsTypes_previous hσ ht
        (ih (by rw [solverStep_modes ht]; exact hm) (solverStep_acyclic hσ ht) h)

theorem runSolver_extendsTypes {fuel s t} (hm : s.substitution.modes = [])
    (h : runSolver fuel s = .success t) : t.substitution.ExtendsTypes s.substitution :=
  runWorklist_extendsTypes hm (runSolver_input_acyclic h) (runSolver_worklist h)

theorem Substitution.constraint_entails_congr {σ τ : Substitution}
    (ht : σ.type = τ.type) (hm : σ.mode = τ.mode) (c : Constraint) (Δ : Bounds) :
    Entails Δ (σ.constraint c) ↔ Entails Δ (τ.constraint c) := by
  have hty : σ.ty = τ.ty := by funext a; simp only [Substitution.ty, ht, hm]
  cases c
  case equal v a =>
    rw [σ.equal_entails Δ v a, τ.equal_entails Δ v a, ht, hty]
  all_goals simp only [Substitution.constraint, Constraint.subst, ht, hm]

theorem Substitution.ExtendsTypes.constraint_entails {τ σ : Substitution}
    (h : τ.ExtendsTypes σ) (hm : σ.modes = []) (c : Constraint) (Δ : Bounds) :
    Entails Δ (τ.constraint (σ.constraint c)) ↔ Entails Δ (τ.constraint c) := by
  rw [Substitution.constraint_compose]
  apply Substitution.constraint_entails_congr
  · exact funext fun v => (Substitution.type_compose v σ τ).trans (h v)
  · funext v
    simp only [Substitution.mode_compose, σ.mode_eq_var hm, ModExpr.subst]

theorem Substitution.ExtendsTypes.bounds_entails {τ σ : Substitution}
    (h : τ.ExtendsTypes σ) (hm : σ.modes = []) (cs : Bounds) (Δ : Bounds) :
    EntailsAll Δ (τ.bounds (σ.bounds cs)) ↔ EntailsAll Δ (τ.bounds cs) := by
  simp only [EntailsAll, Substitution.bounds, List.forall_mem_map, h.constraint_entails hm]

theorem Substitution.ExtendsTypes.singleType_equation {τ : Substitution} {n a}
    (h : τ.ExtendsTypes {types := [(n, a)]}) : τ.ty a = τ.type (.flex n) := by
  simpa only [Substitution.type, List.lookup_cons, beq_self_eq_true, Option.getD_some] using h (.flex n)

theorem Substitution.ExtendsTypes.singleType_entails {τ : Substitution} {n a Δ}
    (h : τ.ExtendsTypes {types := [(n, a)]}) (ha : (τ.type (.flex n)).DefinedUnder Δ) :
    Entails Δ (τ.constraint (.equal (.flex n) a)) := by
  rw [τ.equal_entails, h.singleType_equation]
  exact ⟨⟨.refl, ha, ha⟩, ⟨.refl, ha, ha⟩⟩

theorem runWorklist_extendsTypes_previous {fuel s t} {τ : Substitution}
    (hσ : s.substitution.Acyclic) (h : runWorklist fuel s = .success t)
    (he : τ.ExtendsTypes t.substitution) : τ.ExtendsTypes s.substitution := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · exact RunResult.success.inj h ▸ he
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact solverStep_extendsTypes_previous hσ ht (ih (solverStep_acyclic hσ ht) h)

end ModalityInference
