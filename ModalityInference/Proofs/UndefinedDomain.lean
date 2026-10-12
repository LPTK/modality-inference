import ModalityInference.Proofs.Grounding
import ModalityInference.Proofs.Evaluation
import ModalityInference.Proofs.TypingDefinedness

/-! A partial modality hidden in a function domain defeated the former typing
rules. The three archived rules below are exactly the fragment used by the
counterexample; the corrected `Typing` guards introduced types and modes.
-/
namespace ModalityInference.UndefinedDomain

def badMode : ModExpr := .leftResidual (.const Mode.top) (.const Mode.bottom)
def domain : Ty := .modal .unit badMode
def scheme : Scheme := .mono (.fn domain .unit)
def term : AnnotatedTerm := .app (.var 0) .unit

inductive FormerTyping : Bounds → Context → AnnotatedTerm → Ty → Prop where
  | var {Δ Γ i s σ} : Γ[i]? = some (some s) → Instantiates s σ →
      EntailsAll Δ (σ.bounds s.bounds) → FormerTyping Δ Γ (.var i) (σ.ty s.body)
  | unit {Δ Γ m} : FormerTyping Δ Γ .unit (.modal .unit m)
  | app {Δ Γ Γ₁ Γ₂ f x a b} : ContextJoin Δ Γ₁ Γ₂ Γ →
      FormerTyping Δ Γ₁ f (.fn a b) → FormerTyping Δ Γ₂ x a →
      FormerTyping Δ Γ (.app f x) b

theorem former_typed : FormerTyping [] [some scheme] term .unit := by
  refine .app (a := domain) (.left .nil) (.var (s := scheme) (σ := {}) rfl ?_ ?_) .unit
  all_goals simp [Instantiates, scheme, Scheme.mono, EntailsAll, Substitution.bounds]

theorem interpreted (ρ : GroundAssignment) (w : World) :
    EnvironmentInterpretation ρ w [some scheme] [.unit] :=
  .singleton (fun _ _ _ h => nomatch h)

theorem rejected : evalFuel 2 {} [.unit] term =
    .rejected "application of a non-function" := rfl

def world : World := ⟨{0}⟩

theorem compatible : world.Compatible {} [.unit] := by
  simp [World.Compatible, world, Supplies.Valid, Supply.at, EnvironmentReferences]
  exact fun _ h => nomatch h

theorem not_semantic (ρ : GroundAssignment) :
    ¬ SemanticEvaluation ρ world [some scheme] [.unit] term (.unit Mode.identity) := by
  intro h
  obtain ⟨v, hv, _⟩ := h {} compatible
  exact hv.no_rejection 2 "application of a non-function" rejected

/-- The entire type, not only its outermost mode, must realize successfully. -/
theorem corrected_function_rejected (Γ : Context) (t : AnnotatedTerm) :
    ¬ Typing [] Γ t scheme.body := by
  intro h
  exact Bool.noConfusion (h.realize_defined
    (ρ := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩) (by simp [GroundModels]))

end ModalityInference.UndefinedDomain
