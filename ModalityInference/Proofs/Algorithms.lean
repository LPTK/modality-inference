import ModalityInference.Proofs.Structural
import ModalityInference.Rewriting
import ModalityInference.SchemeSubsumption

namespace ModalityInference.Deferred

def FlexibleBounds (cs : Bounds) : Prop :=
  (∀ v ∈ cs.typeVars, ∃ n, v = .flex n) ∧ (∀ v ∈ cs.modVars, ∃ n, v = .flex n)

/-- DEFERRED. Prerequisites: every guarded residual adjunction, structural
subtyping decomposition and closure orientation. This is a local equivalence. -/
theorem rewrite_sound {cs ds ρ} (h : ConstraintReduction cs ds) :
    GroundModels ρ cs ↔ GroundModels ρ ds := by sorry

/-- DEFERRED. Prerequisites: substitution bookkeeping, fresh shape expansion,
local rewrite equivalence. Fresh variables are existentially extended. -/
theorem rewrite_solution_preservation {s t} (h : Rewrites s t) :
    (∃ Δ σ, BoundsSatisfiable Δ ∧ Solution s.constraints Δ σ) ↔
      (∃ Δ σ, BoundsSatisfiable Δ ∧ Solution t.constraints Δ σ) := by sorry

/-- DEFERRED. Prerequisites: fixed identifier orientation, duplicate suppression,
occurs checks, finite propagation. No polynomial complexity claim is made. -/
theorem rewrite_termination (s : SolverState) :
    ∃ n, ∀ fuel ≥ n, runSolver fuel s ≠ .exhausted := by sorry

/-- DEFERRED. Prerequisites: executable normalization simulates relational rewrites,
finite mode consistency checking, acyclic substitution composition. -/
theorem solve_sound {fuel cs result} (h : solve fuel cs = .success result) :
    Solution cs result.bounds result.substitution ∧ Residual result.bounds ∧
      result.substitution.Acyclic := by sorry

/-- DEFERRED. Prerequisites: finite DPLL completeness and ground instantiation of
remaining flexible type variables. This rules out inconsistent unused `def`s. -/
theorem solve_consistency {fuel cs result} (hf : FlexibleBounds cs)
    (h : solve fuel cs = .success result) : BoundsSatisfiable result.bounds := by sorry

/-- DEFERRED. Prerequisites: rewrite completeness and termination, mode search
completeness. A sufficiently large budget is essential. -/
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

/-- DEFERRED. Prerequisites: fresh instantiation, lazy locks, all syntax-directed
rules, context usage routing and closed-definition solves. Constraint order is immaterial. -/
theorem generator_correspondence {fuel Γ t s r}
    (h : generate fuel Γ t s = .success r) :
    ∃ cs, Generates Γ t r.type cs ∧ r.state.constraints.Perm (s.constraints ++ cs) := by sorry

/-- DEFERRED. Prerequisites: generation rule induction, context splitting/locking,
substitution, and generalization under the empty term context. -/
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

/-- DEFERRED. Prerequisites: freshness invariants, solver completeness and generator
correspondence. Fuel is not part of the declarative typing relation. -/
theorem inference_complete {t a} (h : RawTyping [] [] t a) :
    ∃ n, ∀ fuel ≥ n, ∃ result, infer fuel [] t = .success result := by sorry

/-- DEFERRED. Prerequisites: Boolean projections (including reversed past), residual
well-formedness, CNF equivalence, identifier-to-Fin bijection. The final solver
`Equation.decide_correct` is already proved and is not admitted here. -/
theorem backend_reduction {fuel e report}
    (h : ConcreteBackend.decideFormula fuel e = .success report) :
    report.valid = true ↔ ∀ valuation, e.eval valuation = true := by sorry

/-- DEFERRED. Prerequisites: rigid bound entailment, finite representative theorem,
modal witness reconstruction after Boolean existential elimination, backend reduction.
The returned evidence is data until this theorem is proved. -/
theorem scheme_subsumption_sound {fuel source target evidence}
    (h : checkSubsumption fuel source target = .success evidence) :
    Subsumes [] source target := by sorry

/-- DEFERRED. Prerequisites: complete rigid closure, completeness of type
representatives and projections, freshening/skolemization of body-only variables,
normalization/search termination. -/
theorem scheme_subsumption_complete {source target}
    (h : Subsumes [] source target) :
    ∃ n, ∀ fuel ≥ n, ∃ evidence,
      checkSubsumption fuel source target = .success evidence := by sorry
end ModalityInference.Deferred
