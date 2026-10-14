import ModalityInference.Proofs.GenerationDefinedness
import ModalityInference.Proofs.EntailmentTransport
import ModalityInference.GenerationHygiene

/-! Generalization quantifies over well-formed instance substitutions. An
undefined internal image is outside that domain, even when residual bounds are empty. -/
namespace ModalityInference.GeneralizationDefinedness
open GenerationDefinedness

theorem generated_hygienic : corrected_generated.Hygienic := by
  exact .lam (by simp [AlgorithmicContext.FreshForMode]) .unit

theorem identity_solves : Solves generatedConstraints [] {} :=
  ⟨(fun _ h => nomatch h), ⟨{}, rfl, rfl, fun _ h => nomatch h⟩,
    Substitution.wellFormedUnder_empty []⟩

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

theorem defined_instance_typable (θ : Substitution) (hθ : θ.WellFormedUnder []) :
    RawTyping [] [] (.lam () .unit) (θ.ty function) := by
  refine ⟨.lam [] .unit, rfl, ?_⟩
  change Typing [] [] (.lam [] .unit)
    (.modal (.fn (θ.type (.flex 0)) (.modal .unit .bottom)) (θ.mode (.flex 0)))
  apply Typing.lam (captured := [])
  · exact ((θ.type (.flex 0)).definedUnder_iff_entails_wellFormed []).mp (hθ.types (.flex 0))
  · exact hθ.modes (.flex 0)
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
