import ModalityInference.Proofs.GenerationDefinedness
import ModalityInference.Proofs.EntailmentTransport
import ModalityInference.GenerationHygiene

/-! Generalization must retain definedness of the selected instance, including
type images containing partial internal modalities. -/
namespace ModalityInference.GeneralizationDefinedness
open GenerationDefinedness

theorem generated_hygienic : corrected_generated.Hygienic := by
  exact .lam (by simp [AlgorithmicContext.FreshForMode]) .unit

theorem identity_solves : Solves correctedGuards [] {} := by
  constructor
  · simp [correctedGuards, EntailsAll, Substitution.bounds, Substitution.constraint,
      Constraint.subst, Substitution.type, TypeExpr.subst, ModExpr.subst, Entails, TypeExpr.DefinedUnder,
      TypeExpr.wellFormedBounds, ModExpr.WellFormed, ModExpr.eval, ModExpr.epsilon]
    exact .refl
  · exact ⟨{}, rfl, rfl, by simp [EntailsAll, Substitution.bounds]⟩

theorem partial_instance : Instantiates (Scheme.generalize [] function) partialImage := by
  simp [Instantiates, Scheme.generalize, function, partialImage, TypeExpr.typeVariables,
    TypeExpr.modeVariables, Bounds.typeVariables, Bounds.modeVariables, ModExpr.freeVariables,
    ModExpr.epsilon, ModExpr.bottom]

theorem instance_bounds : EntailsAll [] (partialImage.bounds ([] : Bounds)) := by
  simp [EntailsAll, Substitution.bounds]

theorem partial_instance_undefined : ¬(partialImage.ty function).DefinedUnder [] := by
  intro h
  exact Bool.noConfusion (h.realize_defined
    (ρ := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩) (by simp [GroundModels]))

theorem defined_instance_typable (θ : Substitution) (hd : (θ.ty function).DefinedUnder []) :
    RawTyping [] [] (.lam () .unit) (θ.ty function) := by
  refine ⟨.lam [] .unit, rfl, ?_⟩
  change Typing [] [] (.lam [] .unit)
    (.modal (.fn (θ.type (.flex 0)) (.modal .unit .bottom)) .epsilon)
  have ha : (θ.type (.flex 0)).DefinedUnder [] :=
    (TypeExpr.definedUnder_fn.mp (TypeExpr.definedUnder_modal.mp hd).1).1
  apply Typing.lam (captured := [])
  · exact ((θ.type (.flex 0)).definedUnder_iff_entails_wellFormed []).mp ha
  · simp [Entails, ModExpr.WellFormed, ModExpr.eval, ModExpr.epsilon]
  · exact .nil
  · exact .unit (by simp [Entails, ModExpr.WellFormed, ModExpr.eval, ModExpr.bottom])

def UnguardedGeneralization : Prop := ∀ {rhs a cs residual σ},
  (hg : Generates [] rhs a cs) → hg.Hygienic → rhs.freeVars = ∅ →
  Solves cs residual σ → ∀ θ, Instantiates (Scheme.generalize residual (σ.ty a)) θ →
    EntailsAll [] (θ.bounds residual) → RawTyping [] [] rhs (θ.ty (σ.ty a))

theorem no_unguarded_generalization : ¬UnguardedGeneralization := by
  intro h
  have hi : Instantiates (Scheme.generalize [] (({} : Substitution).ty function)) partialImage := by
    simpa [Substitution.ty, TypeExpr.subst, Substitution.type, Substitution.mode, ModExpr.subst]
      using partial_instance
  have ht := h corrected_generated generated_hygienic (by simp [Term.freeVars])
    identity_solves partialImage hi instance_bounds
  apply no_substituted_typing (.lam () .unit)
  simpa [function, Substitution.ty, TypeExpr.subst, Substitution.type, Substitution.mode,
    ModExpr.subst] using ht

end ModalityInference.GeneralizationDefinedness
