import ModalityInference.Core.Scoping
import ModalityInference.Proofs.UndefinedDomain
import ModalityInference.Proofs.GenerationTypes
import ModalityInference.Inference

/-! Unrestricted raw substitutions can insert undefined internal types into an
unused lambda domain. The inference theorem excludes them with well-formed-image
evidence, without emitting reflexive constraints for fresh variables. A separate
lookup check rejects partial modalities already written in an input scheme. -/
namespace ModalityInference.GenerationDefinedness
open UndefinedDomain

inductive FormerGenerates : AlgorithmicContext → RawTerm → Ty → Bounds → Prop where
  | var {Γ i s σ} : Lookup Γ i s → Instantiates s σ →
      FormerGenerates Γ (.var i) (σ.ty s.body) (σ.bounds s.bounds)
  | unit {Γ} : FormerGenerates Γ .unit (.modal .unit .bottom) []
  | lam {Γ t a b m cs} :
      FormerGenerates (.binding (some (.mono a)) :: .lock m :: Γ) t b cs →
      FormerGenerates Γ (.lam () t) (.modal (.fn a b) m) cs

def function : Ty := .modal (.fn (.var (.flex 0)) (.modal .unit .bottom)) (.var (.flex 0))

def partialImage : Substitution := {types := [(0, domain)], modes := [(0, .epsilon)]}

theorem former_generated : FormerGenerates [] (.lam () .unit) function [] := .lam .unit

theorem former_solution : Solution [] [] partialImage := by
  simp [Solution, EntailsAll, Substitution.bounds]

theorem no_substituted_typing (term : RawTerm) :
    ¬RawTyping [] [] term (partialImage.ty function) := by
  rintro ⟨t, _, ht⟩
  exact Bool.noConfusion (ht.realize_defined
    (ρ := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩) (by simp [GroundModels]))

theorem no_former_generation_sound :
    ¬(∀ {Γ : Context} {t a cs Δ σ},
      FormerGenerates (Γ.map ContextEntry.binding) t a cs → Solution cs Δ σ →
      RawTyping Δ (Context.subst Γ σ) t (σ.ty a)) := by
  intro h
  exact no_substituted_typing _ (h (Γ := []) former_generated former_solution)

/-- A fresh variable has no written partial modalities to check. Its later image
is covered by the well-formed-substitution hypothesis. -/
theorem variable_written_guards_empty :
    (TypeExpr.var (.flex 0) : Ty).wellFormedBounds = [] := rfl

/-- Archived pre-correction instantiation; only declared bounds were emitted. -/
def formerInstantiate (s : InferenceState) (scheme : Scheme) : Ty × InferenceState :=
  let (cs, t) := scheme.instantiate s.nextType s.nextMode
  (t, {nextType := s.nextType + scheme.typeParams.length
       nextMode := s.nextMode + scheme.modParams.length
       constraints := s.constraints ++ cs})

/-- The former variable branch followed by the unchanged top-level solve/generalize. -/
def formerVariableInference (fuel : Nat) (Γ : Context) (i : Nat) : RunResult Inferred := do
  let scheme ← lookupScheme (Γ.map ContextEntry.binding) i
  let (t, r) := formerInstantiate (initialInferenceState Γ) scheme
  let s ← solveFrom fuel r.nextType r.nextMode r.constraints
  let context := Γ.map (Option.map (fun t => t.subst s.substitution))
  let scheme := generalizeOver context s.bounds (s.substitution.ty t)
  return ⟨scheme, AnnotatedTerm.substTypes (.var i) s.substitution,
    s.substitution, s.bounds, s.trace⟩

theorem former_inference_success :
    formerVariableInference 40 [some scheme] 0 = .success ⟨scheme, .var 0, {}, [], []⟩ := rfl

theorem no_inference_derivation (Γ : Context) (t : AnnotatedTerm) :
    ¬Typing [] Γ t scheme.body := corrected_function_rejected Γ t

def generatedConstraints : Bounds := []

theorem corrected_generated : Generates [] (.lam () .unit) function generatedConstraints := .lam .unit

theorem corrected_solution_rejected :
    ¬(Solution generatedConstraints [] partialImage ∧ partialImage.WellFormedUnder []) := by
  intro hs
  exact Bool.noConfusion ((corrected_generated.definedUnder hs.1 hs.2).realize_defined
    (ρ := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩) (by simp [GroundModels]))

theorem corrected_inference_rejected :
    ∃ diagnostic, infer 40 [some scheme] (.var 0) = .rejected diagnostic := ⟨_, rfl⟩

end ModalityInference.GenerationDefinedness
