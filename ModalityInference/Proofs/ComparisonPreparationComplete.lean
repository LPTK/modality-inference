import ModalityInference.Proofs.ComparisonPropagationComposition

/-! Every original algebraic witness has a scoped prepared witness. Freshening
changes binder names only; partial images and guarded bounds are preserved. -/
namespace ModalityInference.ComparisonPreparation

def liftWitness (p : Prepared) (source : Scheme) (σ : CompareSubstitution) :
    CompareSubstitution :=
  { types := (List.range' p.firstType source.typeParams.length).map fun k =>
      (k, σ.type (.flex ((source.typeParams[k - p.firstType]?).getD 0)))
    modes := (List.range' p.firstMode source.modParams.length).map fun k =>
      (k, σ.mode (.flex ((source.modParams[k - p.firstMode]?).getD 0))) }

theorem liftWitness_domainsAbove (p : Prepared) (source : Scheme) (σ : CompareSubstitution) :
    (liftWitness p source σ).DomainsAbove p.firstType p.firstMode := by
  constructor <;> rintro entry he
  all_goals obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
  all_goals obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hk
  all_goals simp

theorem liftWitness_type_at (p : Prepared) (source : Scheme) (σ : CompareSubstitution)
    {i n : Nat} (hi : source.typeParams[i]? = some n) :
    (liftWitness p source σ).type (.flex (p.firstType + i)) = σ.type (.flex n) := by
  have hk : p.firstType + i ∈ List.range' p.firstType source.typeParams.length := by
    exact List.mem_range'.mpr ⟨i, (List.getElem?_eq_some_iff.mp hi).1, by simp⟩
  simp only [liftWitness, CompareSubstitution.type, List.lookup_graph _ hk,
    Option.getD_some, Nat.add_sub_cancel_left, hi]

theorem liftWitness_mode_at (p : Prepared) (source : Scheme) (σ : CompareSubstitution)
    {i n : Nat} (hi : source.modParams[i]? = some n) :
    (liftWitness p source σ).mode (.flex (p.firstMode + i)) = σ.mode (.flex n) := by
  have hk : p.firstMode + i ∈ List.range' p.firstMode source.modParams.length := by
    exact List.mem_range'.mpr ⟨i, (List.getElem?_eq_some_iff.mp hi).1, by simp⟩
  simp only [liftWitness, CompareSubstitution.mode, List.lookup_graph _ hk,
    Option.getD_some, Nat.add_sub_cancel_left, hi]

theorem liftWitness_wellShaped {p : Prepared} {source : Scheme} {σ : CompareSubstitution}
    {Δ : Bounds} (h : σ.WellShaped Δ) : (liftWitness p source σ).WellShaped Δ := by
  rintro entry he
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp he
  exact h.type (.flex ((source.typeParams[k - p.firstType]?).getD 0))

private theorem lookup_none_of_not_key {α : Type} {xs : List (Nat × α)} {n : Nat}
    (h : n ∉ xs.map Prod.fst) : xs.lookup n = none := by
  exact List.lookup_eq_none_iff.mpr fun p hp => by
    simpa only [bne_iff_ne] using
      (fun he : n = p.1 => h (List.mem_map.mpr ⟨p, hp, he.symm⟩))

theorem liftWitness_type {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hσ : CompareInstantiates source σ) {v : TypeVar}
    (hv : v.index < (prepare ambient source target).firstType) :
    (liftWitness (prepare ambient source target) source σ).ty
      ((prepare ambient source target).sourceRenaming.type v) = σ.type v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    let p := prepare ambient source target
    change (liftWitness p source σ).ty (p.sourceRenaming.type (.flex n)) = σ.type (.flex n)
    cases he : p.sourceRenaming.types.lookup n with
    | none =>
      have hn : n ∉ source.typeParams := lookup_fresh_none
        (xs := source.typeParams)
        (f := fun i => (TypeExpr.var (.flex (p.firstType + i)))) he
      have hnone : σ.types.lookup n = none :=
        lookup_none_of_not_key fun hk => hn (hσ.1.mem_iff.mp hk)
      have hfixed := (liftWitness_domainsAbove p source σ).type_fixed (.flex n) hv
      simpa only [Substitution.type, he, Option.getD_none, CompareSubstitution.ty,
        CompareTy.ofTy, CompareTy.subst, CompareSubstitution.type, hnone] using hfixed
    | some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := source.typeParams)
        (f := fun i => (TypeExpr.var (.flex (p.firstType + i)))) he
      simpa only [Substitution.type, he, Option.getD_some, CompareSubstitution.ty,
        CompareTy.ofTy, CompareTy.subst] using liftWitness_type_at p source σ hi

theorem liftWitness_mode {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hσ : CompareInstantiates source σ) {v : ModVar}
    (hv : v.index < (prepare ambient source target).firstMode) :
    ((prepare ambient source target).sourceRenaming.mode v).subst
      (liftWitness (prepare ambient source target) source σ).mode = σ.mode v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    let p := prepare ambient source target
    change (p.sourceRenaming.mode (.flex n)).subst (liftWitness p source σ).mode = σ.mode (.flex n)
    cases he : p.sourceRenaming.modes.lookup n with
    | none =>
      have hn : n ∉ source.modParams := lookup_fresh_none
        (xs := source.modParams)
        (f := fun i => (ModExpr.var (.flex (p.firstMode + i)))) he
      have hnone : σ.modes.lookup n = none :=
        lookup_none_of_not_key fun hk => hn (hσ.2.mem_iff.mp hk)
      have hfixed := (liftWitness_domainsAbove p source σ).mode_fixed (.flex n) hv
      simpa only [Substitution.mode, he, Option.getD_none, ModExpr.subst,
        CompareSubstitution.mode, hnone] using hfixed
    | some a =>
      obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := source.modParams)
        (f := fun i => (ModExpr.var (.flex (p.firstMode + i)))) he
      simpa only [Substitution.mode, he, Option.getD_some, ModExpr.subst] using
        liftWitness_mode_at p source σ hi

theorem liftWitness_reconstruct_type {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution} (hσ : CompareInstantiates source σ) {v : TypeVar}
    (hv : v.index < (prepare ambient source target).firstType) :
    (reconstruct (prepare ambient source target)
      (liftWitness (prepare ambient source target) source σ)).type v = σ.type v :=
  (reconstruct_type _ _ v ((liftWitness_domainsAbove _ _ _).type_fixed v hv)).trans
    (liftWitness_type hσ hv)

theorem liftWitness_reconstruct_mode {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution} (hσ : CompareInstantiates source σ) {v : ModVar}
    (hv : v.index < (prepare ambient source target).firstMode) :
    (reconstruct (prepare ambient source target)
      (liftWitness (prepare ambient source target) source σ)).mode v = σ.mode v :=
  (reconstruct_mode _ _ v ((liftWitness_domainsAbove _ _ _).mode_fixed v hv)).trans
    (liftWitness_mode hσ hv)

theorem liftWitness_ty {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hσ : CompareInstantiates source σ) (t : Ty)
    (ht : ∀ v ∈ t.typeVars, v.index < (prepare ambient source target).firstType)
    (hm : ∀ v ∈ t.modVars, v.index < (prepare ambient source target).firstMode) :
    (liftWitness (prepare ambient source target) source σ).ty
      ((prepare ambient source target).sourceRenaming.ty t) = σ.ty t := by
  rw [← reconstruct_ty _ _ t
    (fun v hv => (liftWitness_domainsAbove _ _ _).type_fixed v (ht v hv))
    (fun v hv => (liftWitness_domainsAbove _ _ _).mode_fixed v (hm v hv))]
  exact CompareSubstitution.ty_congr_on _ _ t
    (fun _ hv => liftWitness_reconstruct_type hσ (ht _ hv))
    (fun _ hv => liftWitness_reconstruct_mode hσ (hm _ hv))

theorem liftWitness_bounds {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hσ : CompareInstantiates source σ) (cs Δ : Bounds)
    (ht : ∀ v ∈ cs.typeVars, v.index < (prepare ambient source target).firstType)
    (hm : ∀ v ∈ cs.modVars, v.index < (prepare ambient source target).firstMode) :
    AlgebraEntailsAll Δ ((liftWitness (prepare ambient source target) source σ).bounds
      ((prepare ambient source target).sourceRenaming.bounds cs)) ↔
      AlgebraEntailsAll Δ (σ.bounds cs) := by
  rw [← reconstruct_algebra_bounds _ _ cs Δ
    (fun v hv => (liftWitness_domainsAbove _ _ _).type_fixed v (ht v hv))
    (fun v hv => (liftWitness_domainsAbove _ _ _).mode_fixed v (hm v hv))]
  exact CompareSubstitution.algebra_bounds_congr _ _ cs
    (fun c hc v hv => liftWitness_reconstruct_type hσ
      (ht v ((cs.mem_typeVars_iff v).mpr ⟨c, hc, hv⟩)))
    (fun c hc v hv => liftWitness_reconstruct_mode hσ
      (hm v ((cs.mem_modVars_iff v).mpr ⟨c, hc, hv⟩)))

/-- The prepared witness keeps the free namespace fixed and retains the
separate guarded-bound and bare-body judgments. -/
def PreparedWitness (p : Prepared) (action : CompareSubstitution) : Prop :=
  action.DomainsAbove p.firstType p.firstMode ∧ action.WellShaped p.assumptions ∧
    AlgebraEntailsAll p.assumptions (action.bounds p.sourceBounds) ∧
    AlgebraSubtype p.assumptions (action.ty p.sourceType) (CompareTy.ofTy p.targetType)

private theorem source_type_lt {ambient : Bounds} {source target : Scheme} {v : TypeVar}
    (hv : v ∈ source.body.typeVars ∪ source.bounds.typeVars) :
    v.index < (prepare ambient source target).firstType := by
  apply SchemePreparation.original_type_lt_first
  simp only [SchemePreparation.originalTypeIds, List.mem_append,
    TypeExpr.mem_typeVariables, Bounds.mem_typeVariables]
  rcases Finset.mem_union.mp hv with hv | hv <;> tauto

private theorem source_mode_lt {ambient : Bounds} {source target : Scheme} {v : ModVar}
    (hv : v ∈ source.body.modVars ∪ source.bounds.modVars) :
    v.index < (prepare ambient source target).firstMode := by
  apply SchemePreparation.original_mode_lt_first
  simp only [SchemePreparation.originalModeIds, List.mem_append,
    TypeExpr.mem_modeVariables, Bounds.mem_modeVariables]
  rcases Finset.mem_union.mp hv with hv | hv <;> tauto

/-- Preparation preserves every algebraic witness, with no totality or
satisfiability premise on the body or the declared assumptions. -/
theorem prepare_algebra_complete {ambient : Bounds} {source target : Scheme}
    (h : AlgebraSubsumes ambient source target) :
    ∃ action, PreparedWitness (prepare ambient source target) action := by
  obtain ⟨σ, hi, hs, hb, ht⟩ := h
  let p := prepare ambient source target
  refine ⟨liftWitness p source σ, liftWitness_domainsAbove _ _ _,
    liftWitness_wellShaped hs, ?_, ?_⟩
  · exact (liftWitness_bounds hi source.bounds p.assumptions
      (fun _ hv => source_type_lt (Finset.mem_union_right _ hv))
      (fun _ hv => source_mode_lt (Finset.mem_union_right _ hv))).mpr hb
  · have he := liftWitness_ty (ambient := ambient) (target := target) hi source.body
      (fun _ hv => source_type_lt (Finset.mem_union_left _ hv))
      (fun _ hv => source_mode_lt (Finset.mem_union_left _ hv))
    exact he.symm ▸ ht

theorem PreparedWitness.subsumes {ambient : Bounds} {source target : Scheme}
    {action : CompareSubstitution} (h : PreparedWitness (prepare ambient source target) action) :
    AlgebraSubsumes ambient source target :=
  reconstruct_algebra_sound ambient source target action
    (fun v hv => h.1.type_fixed v (source_type_lt hv))
    (fun v hv => h.1.mode_fixed v (source_mode_lt hv)) h.2.1 h.2.2.1 h.2.2.2

theorem prepare_algebra_iff (ambient : Bounds) (source target : Scheme) :
    AlgebraSubsumes ambient source target ↔
      ∃ action, PreparedWitness (prepare ambient source target) action :=
  ⟨prepare_algebra_complete, fun ⟨_, h⟩ => h.subsumes⟩

end ModalityInference.ComparisonPreparation
