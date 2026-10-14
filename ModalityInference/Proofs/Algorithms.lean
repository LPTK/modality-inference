import ModalityInference.Proofs.Structural
import ModalityInference.Rewriting
import ModalityInference.SchemeSubsumption
import ModalityInference.Proofs.Backend
import ModalityInference.Proofs.Reduction
import ModalityInference.Proofs.RewriteSoundness
import ModalityInference.Proofs.SolverResidual
import ModalityInference.Proofs.SolverFlexible
import ModalityInference.Proofs.GenerationExecution
import ModalityInference.Proofs.SolverSoundness
import ModalityInference.Proofs.GenerationCorrespondence
import ModalityInference.Proofs.GeneralizationTransport
import ModalityInference.Proofs.InferenceDerivation
import ModalityInference.Proofs.GenerationSoundness
import ModalityInference.Proofs.SolverCompleteness
import ModalityInference.Proofs.InferenceCompleteness

namespace ModalityInference.Deferred

def FlexibleBounds (cs : Bounds) : Prop :=
  (∀ v ∈ cs.typeVars, ∃ n, v = .flex n) ∧ (∀ v ∈ cs.modVars, ∃ n, v = .flex n)

/-- Proved local equivalence, including structural ground subtyping decomposition,
both partial residual adjunctions, definedness guards, and closure orientation. -/
theorem rewrite_sound {cs ds ρ} (h : ConstraintReduction cs ds) :
    GroundModels ρ cs ↔ GroundModels ρ ds := h.groundModels

/-- Proved for every abstract rewrite constructor, including substitution, fresh
shape expansion, and local equivalence. Every solution is preserved on the
original observed domain, modulo mutual ground subtyping. -/
theorem rewrite_solution_preservation {s t scope} (h : Rewrites s t)
    (ht : scope.types ⊆ s.typeVars) (hm : scope.modes ⊆ s.modVars) :
    ∀ ρ, ConfigModels scope s ρ ↔ ConfigModels scope t ρ := Rewrites.configModels h ht hm

/-- Proved full input solution entailment, residual grammar and acyclicity.
`SolverExtension` preserves earlier eliminated equations through later substitutions;
`SolverSoundness` reconstructs the complete input using the cache, support, freshness
and image-definedness invariants. -/
theorem solve_sound {fuel cs result} (h : solve fuel cs = .success result) :
    Solution cs result.bounds result.substitution ∧ Residual result.bounds ∧
      result.substitution.Acyclic :=
  ⟨solve_solution h, solve_residual h, solve_acyclic h⟩

/-- Proved syntactic consistency witness. Flexible support is preserved by all
worklist steps. The returned modality witness extends to a residual ground model,
then finite reification supplies the original `BoundsSatisfiable` contract. -/
theorem solve_consistency {fuel cs result} (hf : FlexibleBounds cs)
    (h : solve fuel cs = .success result) : BoundsSatisfiable result.bounds :=
  solveFrom_consistency (cs.flexible_iff.mpr hf) h

/-- Every satisfiable flexible input is accepted with sufficiently large fuel.
Ground solutions survive fresh expansion, equality elimination and all ordinary
worklist steps; initialized termination and modality-search completeness finish
the executable proof. `solve_ground_principal` additionally establishes the
paper's ground factorization property for every successful result. -/
theorem solve_complete {cs} (hf : FlexibleBounds cs) (hs : BoundsSatisfiable cs) :
    ∃ n, ∀ fuel ≥ n, ∃ result, solve fuel cs = .success result :=
  ModalityInference.solve_complete (cs.flexible_iff.mpr hf) hs

/-- Proved for every constructor, including fresh instantiation, lazy locks,
context usage routing and closed-definition solves. Bounded and flexible support
invariants establish the solver premises for closed right-hand sides.
Constraint order is immaterial. -/
theorem generator_correspondence {fuel Γ t s r}
    (h : generate fuel Γ t s = .success r) :
    ∃ cs, Generates Γ t r.type cs ∧ r.state.constraints.Perm (s.constraints ++ cs) :=
  generate_correspondence h

/-- Proved for every generation constructor by freshening and refining substituted
contexts, compatible binary and ternary sharing, hygienic locking, and generalized
scheme transport for closed definitions. Hygiene and well-formed substitution
images are essential; `GenerationScope` and `GenerationDefinedness` retain the
counterexamples to the former unrestricted statements. -/
theorem generation_sound {Γ : Context} {t a cs Δ σ}
    (h : Generates (Γ.map ContextEntry.binding) t a cs) (hh : h.Hygienic)
    (hs : Solution cs Δ σ) (hσ : σ.WellFormedUnder Δ) :
    RawTyping Δ (Γ.subst σ) t (σ.ty a) := h.sound hh hs hσ

/-- Generalization follows from generation soundness and transport of solved
constraints through every well-formed generalized instance, without admissions.
`GeneralizationDefinedness` refutes the former unguarded contract. -/
theorem closed_definition_generalization {rhs a cs residual σ}
    (hg : Generates [] rhs a cs) (hh : hg.Hygienic) (_hc : rhs.freeVars = ∅)
    (hs : Solves cs residual σ) :
    ∀ θ, Instantiates (Scheme.generalize residual (σ.ty a)) θ →
      EntailsAll [] (θ.bounds residual) → θ.WellFormedUnder [] →
      RawTyping [] [] rhs (θ.ty (σ.ty a)) := by
  intro θ _hi hb hθ
  simpa only [Context.subst, List.map_nil, Substitution.ty_compose] using
    generation_sound (Γ := []) hg hh
      (by simpa only [Solution, Substitution.bounds_compose] using
        (hθ.judgmentMap hb).entails_substituted_bounds hs.1)
      (hs.2.2.compose_of_entails hθ hb)

/-- Soundness for the paper's unannotated terms, derived without admissions from
generation soundness and the executable inference derivation.
`SharingLockCapture` retains the refutation
of the former, stronger claim about the executable's specific capture metadata. -/
theorem inference_sound {fuel Γ t result scope}
    (_hΓ : Context.Scoped scope Γ) (h : infer fuel Γ t = .success result) :
    result.elaborated.erase = t ∧
      RawTyping result.residual (Γ.subst result.substitution) t result.scheme.body := by
  obtain ⟨a, cs, hg, hh, hs, hw, he⟩ := infer_derivation h
  exact ⟨infer_erases h, he.symm ▸ generation_sound hg hh hs hw⟩

/-- Every declaratively typable closed source term is accepted with sufficiently
large fuel. The ground generation induction covers every constructor, including
lazy locks, shared contexts, and generalized closed definitions. -/
theorem inference_complete {t a} (h : RawTyping [] [] t a) :
    ∃ n, ∀ fuel ≥ n, ∃ result, infer fuel [] t = .success result :=
  ModalityInference.inference_complete h

/-- Every ground instance of a declaratively valid closed result type is
represented, up to subtyping, by every successfully inferred scheme. -/
theorem inference_ground_principal {t a fuel result} (ht : RawTyping [] [] t a)
    (hi : infer fuel [] t = .success result) (ρ τ : GroundAssignment) :
    SchemeCovers ρ τ result.scheme (Scheme.generalize [] a) :=
  ModalityInference.inference_ground_principal ht hi ρ τ

/-- Proved by polarity-aware CNF normalization, clause translation with an explicit
identifier-to-Fin lookup, and the existing `Equation.decide_correct` theorem.
This theorem concerns Boolean formulas; modality projection correctness is proved
separately in `Proofs/Projection`. Full scheme subsumption remains deferred. -/
theorem backend_reduction {fuel e report}
    (h : ConcreteBackend.decideFormula fuel e = .success report) :
    report.valid = true ↔ ∀ valuation, e.eval valuation = true :=
  ConcreteBackend.decideFormula_correct h

end ModalityInference.Deferred
