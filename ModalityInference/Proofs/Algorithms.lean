import ModalityInference.Proofs.Structural
import ModalityInference.Rewriting
import ModalityInference.SchemeSubsumption
import ModalityInference.Proofs.Backend
import ModalityInference.Proofs.Reduction
import ModalityInference.Proofs.RewriteSoundness
import ModalityInference.Proofs.SolverResidual
import ModalityInference.Proofs.SolverFlexible
import ModalityInference.Proofs.GenerationExecution

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
occurs checks, finite propagation. No polynomial complexity claim is made. -/
theorem rewrite_termination (s : SolverState) :
    ∃ n, ∀ fuel ≥ n, runSolver fuel s ≠ .exhausted := by sorry

/-- DEFERRED. Prerequisites: each worklist transition is simulated by abstract
rewriting (including normalization and justified duplicate discharge). -/
theorem runSolver_correspondence {fuel s t}
    (hft : ∀ v ∈ (s.pending ++ s.bounds).typeVariables, v.index < s.nextType)
    (hfm : ∀ v ∈ (s.pending ++ s.bounds).modeVariables, v.index < s.nextMode)
    (hσ : s.substitution = {}) (hΔ : s.bounds = []) (hseen : s.seen = [])
    (h : runSolver fuel s = .success t) :
    RewriteStar ⟨s.pending, s.bounds, s.substitution⟩
      ⟨t.pending, t.bounds, t.substitution⟩ := by sorry

/-- DEFERRED solution entailment. Local type and modality steps reconstruct input
entailment; normalization, residual output form and acyclic substitution preservation
are proved independently. The remaining component needs worklist simulation,
substitution transport and its duplicate invariant. -/
theorem solve_sound {fuel cs result} (h : solve fuel cs = .success result) :
    Solution cs result.bounds result.substitution ∧ Residual result.bounds ∧
      result.substitution.Acyclic :=
  ⟨by sorry, solve_residual h, solve_acyclic h⟩

/-- Proved syntactic consistency witness. Flexible support is preserved by all
worklist steps. The returned modality witness extends to a residual ground model,
then finite reification supplies the original `BoundsSatisfiable` contract. -/
theorem solve_consistency {fuel cs result} (hf : FlexibleBounds cs)
    (h : solve fuel cs = .success result) : BoundsSatisfiable result.bounds :=
  solveFrom_consistency (cs.flexible_iff.mpr hf) h

/-- DEFERRED. Prerequisites: rewrite completeness and termination. Mode search
completeness is proved independently. `ModalEquality` records the former modal
self-equality counterexample and the corrected reduction. A sufficiently large
budget is essential. -/
theorem solve_complete {cs} (hf : FlexibleBounds cs) (hs : BoundsSatisfiable cs) :
    ∃ n, ∀ fuel ≥ n, ∃ result, solve fuel cs = .success result := by sorry

/-- DEFERRED. Prerequisites: principal shape expansion and modal-bound preservation.
Factorization is modulo declarative type/modal equivalence on the original domain. -/
theorem principal_factorization {fuel cs result Δ θ}
    (h : solve fuel cs = .success result) (hθ : Solution cs Δ θ) :
    ∃ τ : Substitution, EntailsAll Δ (τ.bounds result.bounds) ∧
      (∀ v ∈ cs.typeVars,
        Subtype Δ (θ.type v) (τ.ty (result.substitution.type v)) ∧
        Subtype Δ (τ.ty (result.substitution.type v)) (θ.type v)) ∧
      (∀ v ∈ cs.modVars,
        Submode Δ (θ.mode v) ((result.substitution.mode v).subst τ.mode) ∧
        Submode Δ ((result.substitution.mode v).subst τ.mode) (θ.mode v)) := by sorry

/-- DEFERRED. Executable generation preserves source erasure and accumulated
constraints. Relational correspondence still needs fresh instantiation, lazy locks,
all syntax-directed rules, context usage routing and closed-definition solves.
Constraint order is immaterial. -/
theorem generator_correspondence {fuel Γ t s r}
    (h : generate fuel Γ t s = .success r) :
    ∃ cs, Generates Γ t r.type cs ∧ r.state.constraints.Perm (s.constraints ++ cs) := by sorry

/-- DEFERRED. Prerequisites: generation rule induction, context splitting/locking,
substitution, and generalization under the empty term context. Generation now
emits guards for lookup, lambda domains/modes and unused sum branches;
`Generates.definedUnder` proves result definedness under every solution. -/
theorem generation_sound {Γ : Context} {t a cs Δ σ}
    (h : Generates (Γ.map ContextEntry.binding) t a cs) (hs : Solution cs Δ σ) :
    RawTyping Δ (Γ.subst σ) t (σ.ty a) := by sorry

/-- DEFERRED. Prerequisites: declarative inversion, fresh instantiation and
constraint principality. Generates is independent of the executable functions. -/
theorem generation_complete {Δ Γ t a} (h : RawTyping Δ Γ t a) :
    ∃ b cs σ, Generates (Γ.map ContextEntry.binding) t b cs ∧
      Solution cs Δ σ ∧ Subtype Δ (σ.ty b) a := by sorry

/-- DEFERRED. Prerequisites: closed term environment, solve consistency and
substitution, universal introduction over *all* remaining free variables. -/
theorem closed_definition_generalization {rhs a cs residual σ}
    (hg : Generates [] rhs a cs) (hc : rhs.freeVars = ∅)
    (hs : Solves cs residual σ) :
    ∀ θ, Instantiates (Scheme.generalize residual (σ.ty a)) θ →
      EntailsAll [] (θ.bounds residual) → RawTyping [] [] rhs (θ.ty (σ.ty a)) := by sorry

/-- DEFERRED typing conjunct; erasure of the actual inferred term is proved.
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
