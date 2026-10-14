import ModalityInference.Proofs.TypingDefinedness

/-! Well-formed substitution images replace reflexive constraints on fresh
inference variables. Written partial modalities still require their own guards. -/
namespace ModalityInference

theorem Substitution.wellFormedUnder_empty (Δ : Bounds) :
    ({} : Substitution).WellFormedUnder Δ := by
  constructor <;> intro v <;> cases v <;>
    simp [Substitution.type, Substitution.mode, TypeExpr.DefinedUnder,
      TypeExpr.wellFormedBounds, ModeModels, Entails, ModExpr.WellFormed, ModExpr.eval]

@[simp] theorem TypeExpr.definedUnder_fn {Δ} {a b : Ty} :
    (TypeExpr.fn a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [DefinedUnder, wellFormedBounds, ModeModels, or_imp, forall_and]

@[simp] theorem TypeExpr.definedUnder_prod {Δ} {a b : Ty} :
    (TypeExpr.prod a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [DefinedUnder, wellFormedBounds, ModeModels, or_imp, forall_and]

@[simp] theorem TypeExpr.definedUnder_sum {Δ} {a b : Ty} :
    (TypeExpr.sum a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [DefinedUnder, wellFormedBounds, ModeModels, or_imp, forall_and]

@[simp] theorem TypeExpr.definedUnder_modal {Δ} {a : Ty} {m : ModExpr} :
    (TypeExpr.modal a m).DefinedUnder Δ ↔
      a.DefinedUnder Δ ∧ ∀ η, ModeModels Δ η → m.WellFormed η := by
  simp [DefinedUnder, wellFormedBounds, ModeModels, or_imp, forall_and, ModeSatisfies]

theorem Substitution.WellFormedUnder.type_of_guards {σ : Substitution} {Δ}
    (hσ : σ.WellFormedUnder Δ) (a : Ty)
    (h : EntailsAll Δ (σ.bounds a.wellFormedBounds)) : (σ.ty a).DefinedUnder Δ := by
  induction a
  case var v => exact hσ.types v
  all_goals simp_all [Substitution.ty, TypeExpr.subst, Substitution.bounds,
    TypeExpr.wellFormedBounds, EntailsAll, Entails, Substitution.constraint,
    Constraint.subst, or_imp, forall_and]
  all_goals simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

end ModalityInference
