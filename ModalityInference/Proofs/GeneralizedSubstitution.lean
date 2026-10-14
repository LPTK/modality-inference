import ModalityInference.Proofs.FreshenedContexts
import ModalityInference.Proofs.GeneralizationTransport

/-! Substitution only renames the binders of a fully generalized scheme. -/
namespace ModalityInference

theorem Scheme.substitutionAction_typeParam (s : Scheme) (σ : Substitution)
    {n : Nat} (hn : n ∈ s.typeParams) :
    (s.substitutionAction σ).type (.flex n) = (s.binderRenaming σ).type (.flex n) := by
  rw [Scheme.substitutionAction, Substitution.type_compose]
  cases he : (s.binderRenaming σ).types.lookup n with
  | none =>
    have hf := lookup_fresh_none (by simpa [binderRenaming, freshSubstitution] using he)
    exact False.elim (hf hn)
  | some a =>
    obtain ⟨i, _, rfl⟩ := lookup_fresh_some (xs := s.typeParams)
      (f := fun i => TypeExpr.var (.flex ((s.fresheningIndices σ).1 + i)))
      (by simpa [binderRenaming, freshSubstitution] using he)
    simpa only [Substitution.type, he, Option.getD_some, Substitution.ty, TypeExpr.subst] using
      (s.freshening_bounded σ).2.type_ge
        (n := (s.fresheningIndices σ).1 + i) (Nat.le_add_right _ _)

theorem Scheme.substitutionAction_modParam (s : Scheme) (σ : Substitution)
    {n : Nat} (hn : n ∈ s.modParams) :
    (s.substitutionAction σ).mode (.flex n) = (s.binderRenaming σ).mode (.flex n) := by
  rw [Scheme.substitutionAction, Substitution.mode_compose]
  cases he : (s.binderRenaming σ).modes.lookup n with
  | none =>
    exact False.elim ((lookup_fresh_none
      (by simpa [binderRenaming, freshSubstitution] using he)) hn)
  | some a =>
    obtain ⟨i, _, rfl⟩ := lookup_fresh_some (xs := s.modParams)
      (f := fun i => ModExpr.var (.flex ((s.fresheningIndices σ).2 + i)))
      (by simpa [binderRenaming, freshSubstitution] using he)
    simpa only [Substitution.mode, he, Option.getD_some, ModExpr.subst] using
      (s.freshening_bounded σ).2.mode_ge
        (n := (s.fresheningIndices σ).2 + i) (Nat.le_add_right _ _)

theorem Instantiates.unsubstitute_of_renaming {s : Scheme} {σ θ : Substitution}
    (h : Instantiates (s.subst σ) θ)
    (ht : ∀ v ∈ s.body.typeVars ∪ s.bounds.typeVars,
      (s.substitutionAction σ).type v = (s.binderRenaming σ).type v)
    (hm : ∀ v ∈ s.body.modVars ∪ s.bounds.modVars,
      (s.substitutionAction σ).mode v = (s.binderRenaming σ).mode v) :
    ∃ θ', Instantiates s θ' ∧ θ'.ty s.body = θ.ty (s.subst σ).body ∧
      ∀ Δ, EntailsAll Δ (θ'.bounds s.bounds) ↔ EntailsAll Δ (θ.bounds (s.subst σ).bounds) := by
  have htype (v : TypeVar) (hv : v ∈ s.body.typeVars ∪ s.bounds.typeVars)
      (hlt : v.index < (s.fresheningIndices σ).1) :
      (θ.mapImages (s.binderRenaming σ)).type v = (θ.compose (s.substitutionAction σ)).type v := by
    simpa only [Substitution.type_compose, ht v hv] using
      θ.mapImages_type (s.binderRenaming σ) v (h.subst_type_lt hlt)
  have hmode (v : ModVar) (hv : v ∈ s.body.modVars ∪ s.bounds.modVars)
      (hlt : v.index < (s.fresheningIndices σ).2) :
      (θ.mapImages (s.binderRenaming σ)).mode v = (θ.compose (s.substitutionAction σ)).mode v := by
    simpa only [Substitution.mode_compose, hm v hv] using
      θ.mapImages_mode (s.binderRenaming σ) v (h.subst_mode_lt hlt)
  refine ⟨θ.mapImages (s.binderRenaming σ),
    (s.freshSubstitution_instantiates _ _ _).mapImages θ, ?_, ?_⟩
  · rw [Scheme.subst_body_action, Substitution.ty_compose]
    exact s.body.subst_congr
      (fun v hv => htype v (Finset.mem_union_left _ hv)
        (((s.body.bounded_iff _ _).mp (s.freshening_bounded σ).1.1).1 v hv))
      (fun v hv => hmode v (Finset.mem_union_left _ hv)
        (((s.body.bounded_iff _ _).mp (s.freshening_bounded σ).1.1).2 v hv))
  · simp only [Scheme.subst_bounds_action, EntailsAll, Substitution.bounds,
      List.forall_mem_map, Substitution.constraint_compose]
    exact fun Δ => forall_congr' fun c => forall_congr' fun hc =>
      Substitution.constraint_entails_congr_on c Δ
        (fun v hv => htype v (Finset.mem_union_right _ ((s.bounds.mem_typeVars_iff _).mpr ⟨c, hc, hv⟩))
          (((c.bounded_iff _ _).mp ((s.freshening_bounded σ).1.2 c hc)).1 v hv))
        (fun v hv => hmode v (Finset.mem_union_right _ ((s.bounds.mem_modVars_iff _).mpr ⟨c, hc, hv⟩))
          (((c.bounded_iff _ _).mp ((s.freshening_bounded σ).1.2 c hc)).2 v hv))

theorem Instantiates.unsubstitute_generalize {cs : Bounds} {a : Ty} {σ θ : Substitution}
    (h : Instantiates ((Scheme.generalize cs a).subst σ) θ) :
    ∃ θ', Instantiates (Scheme.generalize cs a) θ' ∧
      θ'.ty a = θ.ty ((Scheme.generalize cs a).subst σ).body ∧
      ∀ Δ, EntailsAll Δ (θ'.bounds cs) ↔
        EntailsAll Δ (θ.bounds ((Scheme.generalize cs a).subst σ).bounds) := by
  apply h.unsubstitute_of_renaming
  · intro v hv
    cases v with
    | rigid n => rfl
    | flex n =>
      exact (Scheme.generalize cs a).substitutionAction_typeParam σ
        (Scheme.generalize_typeParams.mpr hv)
  · intro v hv
    cases v with
    | rigid n => rfl
    | flex n =>
      exact (Scheme.generalize cs a).substitutionAction_modParam σ
        (Scheme.generalize_modParams.mpr hv)

theorem Instantiates.unsubstAvoid_generalize {cs : Bounds} {a : Ty}
    {σ θ : Substitution} {avoid : Bounds}
    (h : Instantiates ((Scheme.generalize cs a).substAvoid σ avoid) θ) :
    ∃ θ', Instantiates (Scheme.generalize cs a) θ' ∧
      θ'.ty a = θ.ty ((Scheme.generalize cs a).substAvoid σ avoid).body ∧
      ∀ Δ, EntailsAll Δ (θ'.bounds cs) ↔
        EntailsAll Δ (θ.bounds ((Scheme.generalize cs a).substAvoid σ avoid).bounds) := by
  obtain ⟨θ₁, hi₁, ha₁, hb₁⟩ := h.unsubstitute_identity
    (Substitution.identityAt_type _ _) (Substitution.identityAt_mode _ _)
  exact let ⟨θ₂, hi₂, ha₂, hb₂⟩ := hi₁.unsubstitute_generalize
    ⟨θ₂, hi₂, ha₂.trans ha₁, fun Δ => (hb₂ Δ).trans (hb₁ Δ)⟩

theorem Scheme.subsumes_refined_of_instances {source base : Scheme} {p : Nat}
    (hp : base.freshModeIndex ≤ p) (Δ : Bounds)
    (hinst : ∀ θ, Instantiates base θ → ∃ τ, Instantiates source τ ∧
      τ.ty source.body = θ.ty base.body ∧
      ∀ Ξ, EntailsAll Ξ (τ.bounds source.bounds) ↔ EntailsAll Ξ (θ.bounds base.bounds)) :
    Subsumes Δ source (base.refineMode p).withAssumptions := by
  let target := (base.refineMode p).withAssumptions
  let θ := base.freshSubstitution (source.subsumptionIndices Δ target).1
    (source.subsumptionIndices Δ target).2 true
  let m := ModExpr.var (.rigid ((source.subsumptionIndices Δ target).2 + base.modParams.length))
  have hi : Instantiates base θ := base.freshSubstitution_instantiates _ _ _
  have hb := (hi.refineMode_bounds hp m
    (Δ ++ ((θ.extendMode p m).bounds target.bounds).assumptions)).mp
      (EntailsAll.of_subst_assumptions (Bounds.assumptions_entails_append _ _))
  obtain ⟨τ, hi', ha', hb'⟩ := hinst θ hi
  have he (nt nm : Nat) (rigid : Bool) : target.freshSubstitution nt nm rigid =
      (base.refineMode p).freshSubstitution nt nm rigid := rfl
  change Subsumes Δ source target
  simp only [Subsumes, Scheme.instantiate, he, Scheme.refineMode_freshSubstitution]
  exact ⟨τ, hi', (hb' _).mpr hb.1,
    ha'.symm ▸ (hi.refineMode_body hp m).symm ▸ hb.2.1⟩

theorem Scheme.generalize_subsumes_substAvoid_refined (cs : Bounds) (a : Ty)
    (σ : Substitution) (avoid Δ : Bounds) {p : Nat}
    (hp : ((generalize cs a).substAvoid σ avoid).freshModeIndex ≤ p) :
    Subsumes Δ (generalize cs a)
      (((generalize cs a).substAvoid σ avoid).refineMode p).withAssumptions :=
  subsumes_refined_of_instances hp Δ (fun _ hi => hi.unsubstAvoid_generalize)

theorem Scheme.subsumes_substAvoid_refined (s : Scheme) (σ : Substitution)
    (avoid Δ : Bounds) {p : Nat} (hp : (s.substAvoid σ avoid).freshModeIndex ≤ p) :
    Subsumes Δ (s.subst σ) ((s.substAvoid σ avoid).refineMode p).withAssumptions :=
  subsumes_refined_of_instances hp Δ (fun _ hi => hi.unsubstitute_identity
    (Substitution.identityAt_type _ _) (Substitution.identityAt_mode _ _))

theorem Context.substAvoid_refined_le (Γ : Context) (σ : Substitution)
    (avoid Δ : Bounds) {p : Nat}
    (hp : ∀ s, some s ∈ Γ → (s.substAvoid σ avoid).freshModeIndex ≤ p) :
    ContextLe Δ (Γ.subst σ)
      ((AlgorithmicContext.substAvoid (Γ.map ContextEntry.binding) σ avoid).refinedContext p) := by
  induction Γ with
  | nil => exact .nil
  | cons entry Γ ih =>
    cases entry with
    | none => exact .drop (ih (fun s hs => hp s (List.mem_cons_of_mem _ hs)))
    | some s =>
      exact .keep (ih (fun s hs => hp s (List.mem_cons_of_mem _ hs)))
        (s.subsumes_substAvoid_refined σ avoid Δ (hp s List.mem_cons_self))

@[simp] theorem Substitution.empty_ty (a : Ty) : ({} : Substitution).ty a = a := by
  exact (a.subst_congr (fun v _ => by cases v <;> rfl)
    (fun v _ => by cases v <;> rfl)).trans a.subst_id

@[simp] theorem Scheme.mono_subst (a : Ty) (σ : Substitution) :
    (mono a).subst σ = mono (σ.ty a) := by
  simp [mono, subst, instantiate, freshSubstitution, Substitution.bounds,
    Substitution.empty_ty]

@[simp] theorem Scheme.mono_substAvoid (a : Ty) (σ : Substitution) (avoid : Bounds) :
    (mono a).substAvoid σ avoid = mono (σ.ty a) := by
  simp only [substAvoid, mono_subst, Substitution.ty, Substitution.identityAt_type,
    Substitution.identityAt_mode, TypeExpr.subst_id]

end ModalityInference
