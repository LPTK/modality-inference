import ModalityInference.Proofs.UndefinedDomain
import ModalityInference.Proofs.ResourceContexts

/-! A reflexive constraint is not satisfied when its type has no ground
realization. The archived entailment and typing fragment reproduce the former
vacuity bug even with the guards on introduced typing results. -/
namespace ModalityInference.UndefinedBounds

def broken : Ty := UndefinedDomain.domain
def scheme : Scheme :=
  {bounds := [.sub broken broken], body := .fn (.modal .unit .epsilon) .unit}
def term : AnnotatedTerm := .app (.var 0) .unit

def FormerEntails (Δ : Bounds) : Constraint → Prop
  | .sub a b => Subtype Δ a b
  | .mode a b => Submode Δ a b
  | .defined a => ∀ σ, ModeModels Δ σ → a.WellFormed σ
  | .equal v t => Subtype Δ (.var v) t ∧ Subtype Δ t (.var v)
  | .equiv a b => Subtype Δ a b ∧ Subtype Δ b a

def FormerEntailsAll (Δ cs : Bounds) : Prop := ∀ c ∈ cs, FormerEntails Δ c

inductive FormerTyping : Bounds → Context → AnnotatedTerm → Ty → Prop where
  | var {Δ Γ i s σ} : Γ[i]? = some (some s) → Instantiates s σ →
      FormerEntailsAll Δ (σ.bounds s.bounds) →
      EntailsAll Δ (σ.ty s.body).wellFormedBounds →
      FormerTyping Δ Γ (.var i) (σ.ty s.body)
  | unit {Δ Γ m} : Entails Δ (.defined m) →
      FormerTyping Δ Γ .unit (.modal .unit m)
  | app {Δ Γ Γ₁ Γ₂ f x a b} : ContextJoin Δ Γ₁ Γ₂ Γ →
      FormerTyping Δ Γ₁ f (.fn a b) → FormerTyping Δ Γ₂ x a →
      FormerTyping Δ Γ (.app f x) b

theorem former_typed : FormerTyping [] [some scheme] term .unit := by
  refine .app (a := .modal .unit .epsilon) (.left .nil)
    (.var (s := scheme) (σ := {}) rfl ?_ ?_ ?_) (.unit ?_)
  all_goals simp [Instantiates, scheme, FormerEntailsAll, FormerEntails, EntailsAll,
    Entails, Substitution.bounds, Substitution.constraint, Constraint.subst,
    Substitution.ty, TypeExpr.subst, ModExpr.subst, TypeExpr.wellFormedBounds,
    ModExpr.WellFormed, ModExpr.eval, ModExpr.epsilon]
  exact .refl

theorem no_ground_instance (ρ η : GroundAssignment) : ¬ GroundInstantiates ρ scheme η := by
  intro h
  have hb := h.2.2 (.sub broken broken) (by simp [scheme])
  simp [GroundSatisfies, broken, UndefinedDomain.domain, UndefinedDomain.badMode,
    TypeExpr.realize, ModExpr.eval, Mode.leftResidual, Mode.top, Mode.bottom] at hb

theorem interpreted (ρ : GroundAssignment) (w : World) :
    ResourceEnvironmentInterpretation ρ w [some scheme] [.unit] (fun _ => ∅) :=
  .singleton ⟨fun _ h => h.elim,
    fun η _ hη _ => (no_ground_instance ρ η hη).elim⟩

theorem rejected : evalFuel 2 {} [.unit] term =
    .rejected "application of a non-function" := rfl

theorem not_semantic : ¬ ResourceSemanticEvaluation UndefinedDomain.world [.unit]
    term (.unit Mode.identity) ∅ :=
  fun h => let ⟨_, _, he, _⟩ := h {} UndefinedDomain.compatible
    he.no_rejection 2 "application of a non-function" rejected

theorem corrected_bound_rejected : ¬ Entails [] (.sub broken broken) :=
  fun h => Bool.noConfusion ((broken.wellFormedBounds_spec
    ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩).mp
      (h.2.1 _ (by simp [ModeModels])))

theorem corrected_instantiation_rejected (σ : Substitution) :
    ¬ EntailsAll [] (σ.bounds scheme.bounds) := by
  intro h
  exact corrected_bound_rejected (h _ (by simp [Substitution.bounds, scheme,
    Substitution.constraint, Constraint.subst, TypeExpr.subst,
    broken, UndefinedDomain.domain, UndefinedDomain.badMode, ModExpr.subst]))

theorem corrected_consistency_rejected : ¬ BoundsSatisfiable scheme.bounds :=
  fun ⟨σ, _, _, h⟩ => corrected_instantiation_rejected σ h

end ModalityInference.UndefinedBounds
