import ModalityInference.Proofs.GroundSchemes

/-! Ground interpretation commutes with substitution whenever its images agree
on the identifiers occurring in the type or constraint. -/
namespace ModalityInference

theorem TypeExpr.realize_subst_congr (a : Ty) {σ : Substitution} {ρ η : GroundAssignment}
    (ht : ∀ v ∈ a.typeVars, (σ.type v).realize ρ = some (η.types v))
    (hm : ∀ v ∈ a.modVars, (σ.mode v).eval (some ∘ ρ.modes) = some (η.modes v)) :
    (σ.ty a).realize ρ = a.realize η := by
  induction a <;> simp_all [Substitution.ty, TypeExpr.subst, TypeExpr.realize,
    TypeExpr.typeVars, TypeExpr.modVars, Finset.mem_union, or_imp, forall_and]
  rw [ModExpr.eval_subst, ModExpr.eval_congr _ (τ := some ∘ η.modes) hm.2]

theorem GroundSatisfies.subst_congr (c : Constraint) {σ : Substitution} {ρ η : GroundAssignment}
    (ht : ∀ v ∈ c.typeVars, (σ.type v).realize ρ = some (η.types v))
    (hm : ∀ v ∈ c.modVars, (σ.mode v).eval (some ∘ ρ.modes) = some (η.modes v)) :
    GroundSatisfies ρ (σ.constraint c) ↔ GroundSatisfies η c := by
  cases c <;> simp only [Constraint.typeVars, Constraint.modVars, Finset.mem_union,
    Finset.mem_insert, or_imp, forall_and, forall_eq] at ht hm
  case equal v a =>
    cases v <;> simp only [Substitution.constraint, GroundSatisfies,
      a.realize_subst_congr ht.2 hm]
    case rigid n => simp [show ρ.types (.rigid n) = η.types (.rigid n) from Option.some.inj ht.1]
    case flex n =>
      cases he : σ.types.lookup n
      all_goals have hv := ht.1
      all_goals simp only [Substitution.type, he, Option.getD_some, Option.getD_none,
        TypeExpr.realize, Option.some.injEq] at hv
      all_goals simp [hv, a.realize_subst_congr ht.2 hm]
  case sub a b | equiv a b =>
    simp only [Substitution.constraint, Constraint.subst, GroundSatisfies,
      show (a.subst σ.type σ.mode).realize ρ = a.realize η from a.realize_subst_congr ht.1 hm.1,
      show (b.subst σ.type σ.mode).realize ρ = b.realize η from b.realize_subst_congr ht.2 hm.2]
  case mode a b =>
    simp only [Substitution.constraint, Constraint.subst, GroundSatisfies, ModExpr.Below,
      ModExpr.eval_subst, a.eval_congr (τ := some ∘ η.modes) hm.1,
      b.eval_congr (τ := some ∘ η.modes) hm.2]
  case defined a =>
    simp only [Substitution.constraint, Constraint.subst, GroundSatisfies, ModExpr.WellFormed,
      ModExpr.eval_subst, a.eval_congr (τ := some ∘ η.modes) hm]

theorem GroundModels.subst_congr (cs : Bounds) {σ : Substitution} {ρ η : GroundAssignment}
    (ht : ∀ v ∈ cs.typeVars, (σ.type v).realize ρ = some (η.types v))
    (hm : ∀ v ∈ cs.modVars, (σ.mode v).eval (some ∘ ρ.modes) = some (η.modes v)) :
    GroundModels ρ (σ.bounds cs) ↔ GroundModels η cs := by
  induction cs <;> simp_all [Bounds.typeVars_cons, Bounds.modVars_cons,
    Finset.mem_union, or_imp, forall_and, GroundModels, Substitution.bounds]
  exact fun _ => GroundSatisfies.subst_congr _ ht.1 hm.1

end ModalityInference
