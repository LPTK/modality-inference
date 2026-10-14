import ModalityInference.Proofs.GenerationDefinedness
import ModalityInference.Proofs.SchemeBounds
import ModalityInference.GenerationHygiene

/-! Ambient subtype assumptions must expose written definedness for generation
completeness. A raw subtype assumption alone can make an undefined binding usable
through context subsumption, whereas generation checks its written modalities. -/
namespace ModalityInference.GenerationCompletenessDomain

def partialType : Ty := UndefinedDomain.domain
def ambient : Bounds := [.sub partialType .unit]
def source : Scheme := .mono partialType
def target : Scheme := .mono .unit

theorem source_subsumes : Subsumes ambient source target := by
  refine ⟨{}, ?_, ?_, ?_⟩
  · simp [Instantiates, source, Scheme.mono]
  · simp [EntailsAll, source, Scheme.mono, Substitution.bounds]
  · change Subtype ambient partialType .unit
    exact .bound (by simp [ambient])

theorem typed : RawTyping ambient [some source] (.var 0) .unit := by
  refine ⟨.var 0, rfl, ?_⟩
  apply Typing.subs (Γ := [some target]) (a := .unit)
  · apply Typing.var (s := target) (σ := {}) rfl
    · simp [Instantiates, target, Scheme.mono]
    · simp [EntailsAll, target, Scheme.mono, Substitution.bounds]
    · simp [EntailsAll, target, Scheme.mono, Substitution.ty, TypeExpr.subst,
        TypeExpr.wellFormedBounds]
  · exact .keep .nil source_subsumes
  · exact .refl

theorem no_generated_solution {a cs}
    (h : Generates [.binding (some source)] (.var 0) a cs) (σ : Substitution) :
    ¬ Solution cs ambient σ := by
  cases h
  rename_i s θ hi hl
  cases hl
  intro hs
  have hg := hs (.defined UndefinedDomain.badMode) (by
    simp [source, Scheme.mono, partialType, UndefinedDomain.domain, UndefinedDomain.badMode,
      Substitution.bounds, Substitution.ty, TypeExpr.subst, ModExpr.subst,
      TypeExpr.wellFormedBounds, Substitution.constraint, Constraint.subst])
  have hm : ModeModels ambient (fun _ => Mode.identity) := by
    simp [ModeModels, ambient, ModeSatisfies]
  exact Bool.noConfusion (hg (fun _ => Mode.identity) hm)

/-- The unrestricted completeness contract admits ambient bounds that omit
the definedness obligations needed by a generated variable use. -/
theorem no_unrestricted_generation_completeness :
    ¬ (∀ {Δ Γ t a}, RawTyping Δ Γ t a →
      ∃ b cs σ, ∃ hg : Generates (Γ.map ContextEntry.binding) t b cs,
        hg.Hygienic ∧ Solution cs Δ σ ∧ σ.WellFormedUnder Δ ∧
          Subtype Δ (σ.ty b) a) := by
  intro h
  obtain ⟨b, cs, σ, hg, _, hs, _, _⟩ := h typed
  exact no_generated_solution hg σ hs

end ModalityInference.GenerationCompletenessDomain
