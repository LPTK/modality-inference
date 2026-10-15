import ModalityInference.Proofs.ComparisonBareShapes
import ModalityInference.Proofs.ComparisonCheckerSolution
import ModalityInference.Proofs.ComparisonEliminationSoundness
import ModalityInference.Proofs.ComparisonSkeletonNames

namespace ModalityInference

namespace CompareSubstitution

theorem ty_congr_on (σ τ : CompareSubstitution) (t : Ty)
    (ht : ∀ v ∈ t.typeVars, σ.type v = τ.type v)
    (hm : ∀ v ∈ t.modVars, σ.mode v = τ.mode v) : σ.ty t = τ.ty t := by
  exact ComparisonAbsorption.instantiate_congr t ht hm

theorem algebra_equal_iff (σ : CompareSubstitution) (Δ : Bounds) (v : TypeVar) (a : Ty) :
    AlgebraEntails Δ (σ.constraint (.equal v a)) ↔
      AlgebraEntails Δ (.sub (σ.type v) (σ.ty a)) ∧
      AlgebraEntails Δ (.sub (σ.ty a) (σ.type v)) := by
  cases v
  case rigid =>
    simp [CompareSubstitution.constraint, CompareSubstitution.type, AlgebraEntails,
      CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels, and_left_comm, and_comm]
  case flex n =>
    cases he : σ.types.lookup n <;>
      simp [CompareSubstitution.constraint, CompareSubstitution.type, he, AlgebraEntails,
        CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels, and_left_comm, and_comm]

theorem algebra_constraint_congr {Δ : Bounds} (σ τ : CompareSubstitution) (c : Constraint)
    (ht : ∀ v ∈ c.typeVars, σ.type v = τ.type v)
    (hm : ∀ v ∈ c.modVars, σ.mode v = τ.mode v) :
    AlgebraEntails Δ (σ.constraint c) ↔ AlgebraEntails Δ (τ.constraint c) := by
  cases c with
  | sub a b | equiv a b =>
    have ha := ty_congr_on σ τ a
      (fun v hv => ht v (Finset.mem_union_left _ hv))
      (fun v hv => hm v (Finset.mem_union_left _ hv))
    have hb := ty_congr_on σ τ b
      (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))
    simp only [CompareSubstitution.constraint, ha, hb]
  | mode m n =>
    have hm' := m.subst_congr (fun v hv => hm v (Finset.mem_union_left _ hv))
    have hn' := n.subst_congr (fun v hv => hm v (Finset.mem_union_right _ hv))
    simp only [CompareSubstitution.constraint, hm', hn']
  | defined m =>
    simp only [CompareSubstitution.constraint, m.subst_congr hm]
  | equal v a =>
    have hv := ht v (Finset.mem_insert_self _ _)
    have ha := ty_congr_on σ τ a (fun w hw => ht w (Finset.mem_insert_of_mem hw)) hm
    rw [algebra_equal_iff, algebra_equal_iff, hv, ha]

theorem algebra_bounds_congr {Δ : Bounds} (σ τ : CompareSubstitution) (bounds : Bounds)
    (ht : ∀ c ∈ bounds, ∀ v ∈ c.typeVars, σ.type v = τ.type v)
    (hm : ∀ c ∈ bounds, ∀ v ∈ c.modVars, σ.mode v = τ.mode v) :
    AlgebraEntailsAll Δ (σ.bounds bounds) ↔ AlgebraEntailsAll Δ (τ.bounds bounds) := by
  simp only [AlgebraEntailsAll, CompareSubstitution.bounds, List.forall_mem_map]
  exact forall_congr' fun c => forall_congr' fun hc => algebra_constraint_congr σ τ c (ht c hc) (hm c hc)

end CompareSubstitution

namespace ComparisonExactContext

theorem finish_wellShaped {Δ : Bounds} (before : Substitution) {after : CompareSubstitution}
    (h : after.WellShaped Δ) : (finish before after).WellShaped Δ := by
  intro entry he
  simp only [finish, List.mem_append, List.mem_map, List.mem_filter] at he
  rcases he with ⟨pair, hp, rfl⟩ | ⟨he, _⟩
  · exact h.ty pair.2
  · exact h entry he

theorem finish_type_of_identity {before : Substitution} (after : CompareSubstitution)
    (h : ∀ v, before.type v = .var v) (v : TypeVar) :
    (finish before after).type v = after.type v := by
  rw [finish_type, h]
  rfl

end ComparisonExactContext

namespace ComparisonAbsorption

theorem finish_mode (r : Result) (after : CompareSubstitution) (v : ModVar) :
    (ComparisonExactContext.finish r.action after).mode v = neutral r.owners after.mode v := by
  rw [ComparisonExactContext.finish_mode, action_mode]
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [neutral]
    split <;> rfl

theorem finish_reconstruct {Δ : Bounds} (p : SchemePreparation.Prepared)
    (total : ModExpr → Bool) (after : CompareSubstitution)
    (hshape : after.WellShaped Δ)
    (htotal : ∀ m, transparent p total m = true →
      Submode Δ (m.subst (ComparisonExactContext.finish (plan p total).action after).mode)
        (m.subst (ComparisonExactContext.finish (plan p total).action after).mode)) :
    AlgebraSubtype Δ ((ComparisonExactContext.finish (plan p total).action after).ty p.sourceType)
      (after.ty (plan p total).body) := by
  have hm : (ComparisonExactContext.finish (plan p total).action after).mode =
      neutral (plan p total).owners after.mode := funext (finish_mode _ _)
  have ht : (ComparisonExactContext.finish (plan p total).action after).type = after.type :=
    funext (ComparisonExactContext.finish_type_of_identity after (action_type _))
  have ha := (plan_reconstruct p total after.type after.mode hshape.type
    (by simpa only [hm] using htotal)).1
  exact AlgebraSubtype.shaped (by simpa only [CompareSubstitution.ty, instantiate, ht, hm] using ha)

end ComparisonAbsorption

end ModalityInference

namespace ModalityInference

theorem ModExpr.support_subst {Q : ModVar → Prop} (m : ModExpr) (σ : ModVar → ModExpr)
    (h : ∀ v ∈ m.vars, ∀ w ∈ (σ v).vars, Q w) : ∀ w ∈ (m.subst σ).vars, Q w := by
  induction m with
  | «const» => simp [ModExpr.subst, ModExpr.vars]
  | var v => exact h v (Finset.mem_singleton_self _)
  | compose a b iha ihb | meet a b iha ihb | join a b iha ihb
  | leftResidual a b iha ihb | rightResidual a b iha ihb =>
    simp only [ModExpr.vars, Finset.mem_union, or_imp, forall_and] at h
    simpa only [ModExpr.subst, ModExpr.vars, Finset.mem_union, or_imp, forall_and] using
      And.intro (iha h.1) (ihb h.2)
  | close a ih | closeInv a ih | future a ih | capture a ih => exact ih h

theorem TypeExpr.mode_support_subst {Q : ModVar → Prop} (t : Ty) (σ : Substitution)
    (ht : ∀ v ∈ t.typeVars, ∀ w ∈ (σ.type v).modVars, Q w)
    (hm : ∀ v ∈ t.modVars, ∀ w ∈ (σ.mode v).vars, Q w) :
    ∀ w ∈ (σ.ty t).modVars, Q w := by
  induction t with
  | var v => exact ht v (Finset.mem_singleton_self _)
  | unit | credit => simp [Substitution.ty, TypeExpr.subst, TypeExpr.modVars]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [TypeExpr.typeVars, TypeExpr.modVars, Finset.mem_union, or_imp, forall_and] at ht hm
    simpa only [Substitution.ty, TypeExpr.subst, TypeExpr.modVars,
      Finset.mem_union, or_imp, forall_and] using And.intro (iha ht.1 hm.1) (ihb ht.2 hm.2)
  | modal a m ih =>
    simp only [TypeExpr.modVars, Finset.mem_union, or_imp, forall_and] at hm
    simpa only [Substitution.ty, TypeExpr.subst, TypeExpr.modVars,
      Finset.mem_union, or_imp, forall_and] using And.intro (ih ht hm.1) (ModExpr.support_subst m σ.mode hm.2)

theorem Substitution.mode_support {σ : Substitution} {Q : ModVar → Prop}
    (hi : ∀ entry ∈ σ.modes, ∀ v ∈ entry.2.vars, Q v)
    (v : ModVar) (hv : Q v) : ∀ w ∈ (σ.mode v).vars, Q w := by
  cases v with
  | rigid n => simpa only [Substitution.mode, ModExpr.vars, Finset.mem_singleton, forall_eq] using hv
  | flex n =>
    cases he : σ.modes.lookup n with
    | none => simpa only [Substitution.mode, he, Option.getD_none, ModExpr.vars,
        Finset.mem_singleton, forall_eq] using hv
    | some m =>
      obtain ⟨before, after, heq, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [Substitution.mode, he, Option.getD_some] using hi (n, m) (by simp [heq])

theorem ComparisonExactContext.Scoped.mode_avoids_domain {p : SchemePreparation.Prepared}
    {σ : Substitution} (h : Scoped p σ) (v : ModVar) :
    ∀ w ∈ (σ.mode v).vars, ∀ n ∈ σ.modes.map Prod.fst, w ≠ .flex n := by
  cases v with
  | rigid n => simp [Substitution.mode, ModExpr.vars]
  | flex n =>
    cases he : σ.modes.lookup n with
    | none =>
      simp only [Substitution.mode, he, Option.getD_none, ModExpr.vars,
        Finset.mem_singleton, forall_eq]
      intro k hk heq
      have heq := ModVar.flex.inj heq
      subst k
      have hn := List.lookup_eq_none_iff.mp he
      obtain ⟨entry, hentry, hkey⟩ := List.mem_map.mp hk
      have hneq := bne_iff_ne.mp (hn entry hentry)
      exact hneq hkey.symm
    | some m =>
      obtain ⟨before, after, heq, _⟩ := List.lookup_eq_some_iff.mp he
      intro w hw k hk hew
      have hw' : w ∈ m.vars := by simpa only [Substitution.mode, he, Option.getD_some] using hw
      have hf := (h.2 n m (by simp [heq])).2 w hw'
      have ha := h.mode_keys hk
      exact Bool.noConfusion (ha.symm.trans (hew ▸ hf))

namespace ComparisonAbsorption

theorem rewrite_modes_free {total : ModExpr → Bool} {owners : Owners} {t u : Ty}
    (h : rewrite total owners t = some u) : ∀ v ∈ u.modVars, modeFree owners v = true := by
  induction t generalizing u with
  | var | unit | credit =>
    rw [rewrite.eq_def] at h
    split at h
    · cases Option.some.inj h; simp [TypeExpr.modVars]
    · contradiction
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    rw [rewrite.eq_def] at h
    split at h
    · next hd => cases Option.some.inj h; exact ((disjoint_correct _ _).mp hd).2
    · cases ha : rewrite total owners a <;> simp only [ha, Option.bind_eq_bind, Option.bind] at h
      · contradiction
      · cases hb : rewrite total owners b <;> simp only [hb] at h
        · contradiction
        · cases Option.some.inj h
          simpa only [TypeExpr.modVars, Finset.mem_union, or_imp, forall_and] using ⟨iha ha, ihb hb⟩
  | modal a m ih =>
    rw [rewrite.eq_def] at h
    split at h
    · next hd => cases Option.some.inj h; exact ((disjoint_correct _ _).mp hd).2
    · split at h
      · next x n he =>
        cases he
        split at h
        · cases Option.some.inj h; simp [TypeExpr.modVars]
        · contradiction
      · next _ _ he => cases he
      · next _ _ he => cases he
      · next _ _ he => cases he
      · next a' m' _ he =>
        cases he
        split at h
        · next hm =>
          cases ha : rewrite total owners a <;> simp only [ha, Option.map] at h
          · contradiction
          · cases Option.some.inj h
            simp only [Bool.and_eq_true] at hm
            simpa only [TypeExpr.modVars, Finset.mem_union, or_imp, forall_and] using
              ⟨ih ha, (modeDisjoint_correct _ _).mp hm.1⟩
        · contradiction
      · contradiction

theorem plan_modes_free (p : SchemePreparation.Prepared) (total : ModExpr → Bool) :
    ∀ v ∈ (plan p total).body.modVars, modeFree (plan p total).owners v = true :=
  rewrite_modes_free (plan_spec p total).2

end ComparisonAbsorption

end ModalityInference

namespace ModalityInference.ComparisonChecker

/-- Semantic composition of structural templates and the three context
adaptations. The core obligations retain their original partial guards. -/
theorem compose_prepasses {Δ : Bounds} (p : SchemePreparation.Prepared)
    (before : Substitution) (known : List ModExpr) (templates : Substitution)
    (core : CompareSubstitution)
    (hcore : core.WellShaped Δ) :
    let input := ComparisonExactContext.rewrite p before
    let total := ComparisonBody.isTotal known
    let absorption := ComparisonAbsorption.plan input total
    let absorbed := { input with sourceType := absorption.body }
    let annotations := ComparisonAnnotations.prepare absorbed total
    let work := { absorbed with sourceType := annotations.substitution.ty absorbed.sourceType }
    let templated := ComparisonExactContext.finish templates core
    let annotated := ComparisonExactContext.finish annotations.substitution templated
    let restored := ComparisonExactContext.finish absorption.action annotated
    let action := ComparisonExactContext.finish before restored
    (∀ m, ComparisonAbsorption.transparent input total m = true →
      Submode Δ (m.subst restored.mode) (m.subst restored.mode)) →
    AlgebraEntailsAll Δ (core.bounds (templates.bounds work.sourceBounds)) →
    AlgebraSubtype Δ (core.ty (templates.ty work.sourceType)) (CompareTy.ofTy p.targetType) →
    action.WellShaped Δ ∧ AlgebraEntailsAll Δ (action.bounds p.sourceBounds) ∧
      AlgebraSubtype Δ (action.ty p.sourceType) (CompareTy.ofTy p.targetType) := by
  dsimp only
  intro htotal hbounds hbody
  let input := ComparisonExactContext.rewrite p before
  let absorption := ComparisonAbsorption.plan input (ComparisonBody.isTotal known)
  let annotations := ComparisonAnnotations.prepare { input with sourceType := absorption.body }
    (ComparisonBody.isTotal known)
  have ht := ComparisonExactContext.finish_wellShaped templates hcore
  have ha := ComparisonExactContext.finish_wellShaped annotations.substitution ht
  have hr := ComparisonExactContext.finish_wellShaped absorption.action ha
  refine ⟨ComparisonExactContext.finish_wellShaped before hr, ?_, ?_⟩
  · rw [ComparisonExactContext.finish_bounds]
    change AlgebraEntailsAll Δ
      ((ComparisonExactContext.finish absorption.action
        (ComparisonExactContext.finish annotations.substitution
          (ComparisonExactContext.finish templates core))).bounds input.sourceBounds)
    rw [ComparisonExactContext.finish_bounds,
      ComparisonAbsorption.plan_bounds_fixed input (ComparisonBody.isTotal known)]
    rw [ComparisonExactContext.finish_bounds]
    have hann := ComparisonAnnotations.prepare_bounds_fixed
      { input with sourceType := absorption.body } (ComparisonBody.isTotal known)
    change annotations.substitution.bounds input.sourceBounds = input.sourceBounds at hann
    rw [hann, ComparisonExactContext.finish_bounds]
    exact hbounds
  · rw [ComparisonExactContext.finish_ty]
    apply (ComparisonAbsorption.finish_reconstruct _ _ _ ha htotal).trans
    simpa only [ComparisonExactContext.finish_ty] using hbody

end ModalityInference.ComparisonChecker
