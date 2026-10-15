import ModalityInference.Declarative
import ModalityInference.Proofs.SubstitutionSupport

/-! Constraint substitution respects finite syntactic support. The optimized
substitution of equality constraints has the same guarded entailment as uniform
substitution by type and modality functions. -/
namespace ModalityInference

theorem Constraint.subst_congr (c : Constraint) {ts us : TypeVar → Ty} {ms ns : ModVar → ModExpr}
    (ht : ∀ v ∈ c.typeVars, ts v = us v) (hm : ∀ v ∈ c.modVars, ms v = ns v) :
    c.subst ts ms = c.subst us ns := by
  cases c <;> simp_all [Constraint.subst, Constraint.typeVars, Constraint.modVars,
    or_imp, forall_and]
  all_goals first
    | exact ⟨TypeExpr.subst_congr _ ht.1 hm.1, TypeExpr.subst_congr _ ht.2 hm.2⟩
    | exact ⟨ModExpr.subst_congr _ hm.1, ModExpr.subst_congr _ hm.2⟩
    | exact ModExpr.subst_congr _ hm
    | exact TypeExpr.subst_congr _ ht.2 hm

theorem Substitution.constraint_subst_entails (σ : Substitution) (c : Constraint) (Δ : Bounds) :
    Entails Δ (σ.constraint c) ↔ Entails Δ (c.subst σ.type σ.mode) := by
  cases c <;> try rfl
  case equal v a =>
    cases v
    case rigid n =>
      simp [Substitution.constraint, Constraint.subst, Substitution.type, Entails,
        TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels, Substitution.ty]
    case flex n =>
      cases he : σ.types.lookup n <;>
        simp [Substitution.constraint, Constraint.subst, Substitution.type, he, Entails,
          TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels, Substitution.ty]

end ModalityInference
