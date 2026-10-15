import ModalityInference.Rewriting
import ModalityInference.SchemeSubsumption
import ModalityInference.ComparisonAlgebra

/-! Unproved specifications retained without admissions.

These definitions name propositions; they do not supply proofs of those propositions.
They preserve the contracts of the removed admitted declarations, including their
side conditions. A future proof must establish the named proposition itself.

Principality remains required for the paper's completeness-and-principality claim;
successful inference on every typable term alone does not establish it. The symbolic
factorization statement below is one proposed route to that claim. Solver
correspondence is a possible supporting lemma. Scheme-checker correctness is a
separate verification task, and closed-term substitution is optional metatheory.
-/
namespace ModalityInference.Obligations

/-- Optional syntactic metatheorem, formerly `Deferred.closed_term_substitution`.
Closed replacements avoid duplicating resources from a shared ambient context.
The established environment-based semantic proof does not need this statement. -/
def ClosedTermSubstitution : Prop :=
  ∀ {Δ : Bounds} {Γ : Context} {t : RawTerm} {a : Ty}, RawTyping Δ Γ t a →
    ∀ σ : Nat → RawTerm,
      (∀ (i : Nat) s θ, Γ[i]? = some (some s) → Instantiates s θ →
        EntailsAll Δ (θ.bounds s.bounds) → RawTyping Δ [] (σ i) (θ.ty s.body)) →
      RawTyping Δ [] (t.subst σ) a

/-- Possible bridge to abstract solution preservation, formerly
`Deferred.runSolver_correspondence`. Complete substitution simulation remains
unproved; cache and transport prerequisites are established separately. -/
def RunSolverCorrespondence : Prop :=
  ∀ {fuel : Nat} {s t : SolverState},
    (∀ v ∈ (s.pending ++ s.bounds).typeVariables, v.index < s.nextType) →
    (∀ v ∈ (s.pending ++ s.bounds).modeVariables, v.index < s.nextMode) →
    s.substitution = {} → s.bounds = [] → s.seen = [] →
    runSolver fuel s = .success t →
    RewriteStar ⟨s.pending, s.bounds, s.substitution⟩
      ⟨t.pending, t.bounds, t.substitution⟩

/-- Unproved symbolic principality contract, formerly
`Deferred.principal_factorization`. Every original solution must factor through
the returned substitution and residual bounds, modulo mutual subtyping/submoding.
The residual ambient grammar is essential: `PrincipalAmbient` refutes the former
unrestricted statement. Proving this contract, or a suitable ground replacement,
remains part of establishing the paper's principality claim. -/
def PrincipalFactorization : Prop :=
  ∀ {fuel : Nat} {cs : Bounds} {result : Solved} {Δ : Bounds} {θ : Substitution},
    Residual Δ → solve fuel cs = .success result → Solution cs Δ θ → θ.WellFormedUnder Δ →
    ∃ τ : Substitution, τ.WellFormedUnder Δ ∧ EntailsAll Δ (τ.bounds result.bounds) ∧
      (∀ v ∈ cs.typeVars,
        Subtype Δ (θ.type v) (τ.ty (result.substitution.type v)) ∧
        Subtype Δ (τ.ty (result.substitution.type v)) (θ.type v)) ∧
      (∀ v ∈ cs.modVars,
        Submode Δ (θ.mode v) ((result.substitution.mode v).subst τ.mode) ∧
        Submode Δ ((result.substitution.mode v).subst τ.mode) (θ.mode v))

/-- Signature-checker soundness requires structural reconstruction and rigid
entailment in the compatible-shape comparison algebra. The verified finite-basis
and modality kernels do not by themselves verify the assembled checker. -/
def SchemeSubsumptionSound : Prop :=
  ∀ {fuel : Nat} {source target : Scheme} {evidence : SubsumptionEvidence},
    (source.typeParams.Nodup ∧ source.modParams.Nodup) →
    (target.typeParams.Nodup ∧ target.modParams.Nodup) →
    Residual target.bounds → checkSubsumption fuel source target = .success evidence →
    AlgebraSubsumes [] source target

/-- Completeness covers compatible internal witnesses, including ordinary
instantiations. Partial body images remain in scope; no body-definedness or
satisfiable-target premise is imposed. -/
def SchemeSubsumptionComplete : Prop :=
  ∀ {source target : Scheme},
    (source.typeParams.Nodup ∧ source.modParams.Nodup) →
    (target.typeParams.Nodup ∧ target.modParams.Nodup) →
    Residual target.bounds → AlgebraSubsumes [] source target →
    ∃ n, ∀ fuel ≥ n, ∃ evidence,
      checkSubsumption fuel source target = .success evidence

end ModalityInference.Obligations
