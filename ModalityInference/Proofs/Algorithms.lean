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

/-- DEFERRED. Prerequisites: fixed identifier orientation, duplicate suppression,
and finite shape expansion. `ModePropagation` refutes the former unbounded
transitive work: mode bounds are now retained directly for finite checking.
No polynomial complexity claim is made. -/
theorem rewrite_termination (s : SolverState) :
    ∃ n, ∀ fuel ≥ n, runSolver fuel s ≠ .exhausted := by sorry

/-- DEFERRED. Prerequisites: each worklist transition is simulated by abstract
rewriting. `ModeSeen` and `TypeSeen` justify duplicate discharge for every constraint
kind throughout the complete worklist. `SolverTransport` transports these
consequences through later type substitutions, and `SolverImages` proves definedness
of returned type images; complete substitution simulation remains. -/
theorem runSolver_correspondence {fuel s t}
    (hft : ∀ v ∈ (s.pending ++ s.bounds).typeVariables, v.index < s.nextType)
    (hfm : ∀ v ∈ (s.pending ++ s.bounds).modeVariables, v.index < s.nextMode)
    (hσ : s.substitution = {}) (hΔ : s.bounds = []) (hseen : s.seen = [])
    (h : runSolver fuel s = .success t) :
    RewriteStar ⟨s.pending, s.bounds, s.substitution⟩
      ⟨t.pending, t.bounds, t.substitution⟩ := by sorry

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

/-- DEFERRED. Prerequisites: rewrite completeness and termination. Mode search
completeness is proved independently. `ModalEquality` records the former modal
self-equality counterexample and the corrected reduction. `ModePropagation`
records a satisfiable input on which former transitive work exhausted every budget.
A sufficiently large budget is essential for the corrected solver. -/
theorem solve_complete {cs} (hf : FlexibleBounds cs) (hs : BoundsSatisfiable cs) :
    ∃ n, ∀ fuel ≥ n, ∃ result, solve fuel cs = .success result := by sorry

/-- DEFERRED. Prerequisites: principal shape expansion and modal-bound preservation.
Ambient assumptions obey the paper's variable-bound grammar; `PrincipalAmbient`
refutes the former unrestricted whole-type assumptions, even when satisfiable.
Factorization is modulo declarative type/modal equivalence on the original domain. -/
theorem principal_factorization {fuel cs result Δ θ}
    (hΔ : Residual Δ) (h : solve fuel cs = .success result) (hθ : Solution cs Δ θ) :
    ∃ τ : Substitution, EntailsAll Δ (τ.bounds result.bounds) ∧
      (∀ v ∈ cs.typeVars,
        Subtype Δ (θ.type v) (τ.ty (result.substitution.type v)) ∧
        Subtype Δ (τ.ty (result.substitution.type v)) (θ.type v)) ∧
      (∀ v ∈ cs.modVars,
        Submode Δ (θ.mode v) ((result.substitution.mode v).subst τ.mode) ∧
        Submode Δ ((result.substitution.mode v).subst τ.mode) (θ.mode v)) := by sorry

/-- Proved for every constructor, including fresh instantiation, lazy locks,
context usage routing and closed-definition solves. Bounded and flexible support
invariants establish the solver premises for closed right-hand sides.
Constraint order is immaterial. -/
theorem generator_correspondence {fuel Γ t s r}
    (h : generate fuel Γ t s = .success r) :
    ∃ cs, Generates Γ t r.type cs ∧ r.state.constraints.Perm (s.constraints ++ cs) :=
  generate_correspondence h

/-- DEFERRED. Prerequisites: generation rule induction, context splitting/locking,
substitution, and generalization under the empty term context. `GenerationScope`
refutes the unrestricted statement: a lock can be captured by a scheme quantifier.
Hygiene keeps locks outside those quantifiers; `generate_initial_hygienic` proves
it for actual generation from every initialized context. Definedness guards and
`Generates.definedUnder` remain necessary under partial substitutions. -/
theorem generation_sound {Γ : Context} {t a cs Δ σ}
    (h : Generates (Γ.map ContextEntry.binding) t a cs) (hh : h.Hygienic)
    (hs : Solution cs Δ σ) :
    RawTyping Δ (Γ.subst σ) t (σ.ty a) := by sorry

/-- DEFERRED. Prerequisites: declarative inversion, fresh instantiation and
constraint principality. Completeness must produce a hygienic derivation;
both generation judgments are independent of the executable functions. -/
theorem generation_complete {Δ Γ t a} (h : RawTyping Δ Γ t a) :
    ∃ b cs σ, ∃ hg : Generates (Γ.map ContextEntry.binding) t b cs,
      hg.Hygienic ∧ Solution cs Δ σ ∧ Subtype Δ (σ.ty b) a := by sorry

/-- DEFERRED. Prerequisites: closed term environment, solve consistency and
substitution, universal introduction over *all* remaining free variables.
The RHS derivation obeys the same lock-scope condition as generation soundness.
The selected instance must be defined, as in variable typing;
`GeneralizationDefinedness` refutes the former unguarded contract. -/
theorem closed_definition_generalization {rhs a cs residual σ}
    (hg : Generates [] rhs a cs) (hh : hg.Hygienic) (hc : rhs.freeVars = ∅)
    (hs : Solves cs residual σ) :
    ∀ θ, Instantiates (Scheme.generalize residual (σ.ty a)) θ →
      EntailsAll [] (θ.bounds residual) → (θ.ty (σ.ty a)).DefinedUnder [] →
      RawTyping [] [] rhs (θ.ty (σ.ty a)) := by sorry

/-- DEFERRED typing conjunct; erasure of the actual inferred term is proved.
The current capture construction is refuted by `SharingLockCapture`; repairing
the emitted annotations is necessary before this intended contract can hold.
`CaptureRefinement` proves a replacement annotation for that exact witness,
under the same residual bounds and inferred type; the general repair remains.
Typing still needs generation soundness, solver soundness, fresh scheme
instantiation and substitution of typed capture annotations. This checks the actual
elaborated term, not just the existence of some typing annotation. -/
theorem inference_sound {fuel Γ t result scope}
    (hΓ : Context.Scoped scope Γ) (h : infer fuel Γ t = .success result) :
    result.elaborated.erase = t ∧
      Typing result.residual (Γ.subst result.substitution) result.elaborated result.scheme.body :=
  ⟨infer_erases h, by sorry⟩

/-- DEFERRED. Prerequisites: freshness invariants, solver completeness and generator
correspondence. Fuel is not part of the declarative typing relation. -/
theorem inference_complete {t a} (h : RawTyping [] [] t a) :
    ∃ n, ∀ fuel ≥ n, ∃ result, infer fuel [] t = .success result := by sorry

/-- Proved by polarity-aware CNF normalization, clause translation with an explicit
identifier-to-Fin lookup, and the existing `Equation.decide_correct` theorem.
This theorem concerns Boolean formulas; modality projection correctness is proved
separately in `Proofs/Projection`. Full scheme subsumption remains deferred. -/
theorem backend_reduction {fuel e report}
    (h : ConcreteBackend.decideFormula fuel e = .success report) :
    report.valid = true ↔ ∀ valuation, e.eval valuation = true :=
  ConcreteBackend.decideFormula_correct h

/-- DEFERRED. Prerequisites: rigid bound entailment, finite representative theorem,
modal witness reconstruction after Boolean existential elimination, backend reduction.
The returned evidence is data until this theorem is proved. -/
theorem scheme_subsumption_sound {fuel source target evidence}
    (hs : source.typeParams.Nodup ∧ source.modParams.Nodup)
    (ht : target.typeParams.Nodup ∧ target.modParams.Nodup)
    (hb : Residual target.bounds)
    (h : checkSubsumption fuel source target = .success evidence) :
    Subsumes [] source target := by sorry

/-- DEFERRED. Prerequisites: complete rigid closure, completeness of type
representatives and projections, freshening/skolemization of body-only variables,
normalization/search termination. -/
theorem scheme_subsumption_complete {source target}
    (hs : source.typeParams.Nodup ∧ source.modParams.Nodup)
    (ht : target.typeParams.Nodup ∧ target.modParams.Nodup)
    (hb : Residual target.bounds)
    (h : Subsumes [] source target) :
    ∃ n, ∀ fuel ≥ n, ∃ evidence,
      checkSubsumption fuel source target = .success evidence := by sorry
end ModalityInference.Deferred
