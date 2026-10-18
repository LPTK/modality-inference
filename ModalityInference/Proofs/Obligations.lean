import ModalityInference.Rewriting
import ModalityInference.SchemeSubsumption
import ModalityInference.ComparisonAlgebra

/-! Proof contracts retained as named propositions.

These definitions preserve the stated contracts and their side conditions.
A theorem proving a contract establishes the named proposition itself.

Ground principality and completeness are proved for solving and closed inference.
The symbolic factorization statement below expresses the corresponding stronger
property under residual ambient bounds. `WorklistCorrespondence` proves the exact
solver correspondence contract. `ComparisonSoundness` and
`ComparisonSubsumptionCompleteness` prove the scheme-checker contracts;
closed-term substitution is optional syntactic metatheory.
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

/-- Every successful initialized worklist run is an abstract rewriting
derivation, including substitution, cached obligations, and definedness guards. -/
def RunSolverCorrespondence : Prop :=
  ∀ {fuel : Nat} {s t : SolverState},
    (∀ v ∈ (s.pending ++ s.bounds).typeVariables, v.index < s.nextType) →
    (∀ v ∈ (s.pending ++ s.bounds).modeVariables, v.index < s.nextMode) →
    s.substitution = {} → s.bounds = [] → s.seen = [] →
    runSolver fuel s = .success t →
    RewriteStar ⟨s.pending, s.bounds, s.substitution⟩
      ⟨t.pending, t.bounds, t.substitution⟩

/-- Symbolic principality: every original solution factors through
the returned substitution and residual bounds, modulo mutual subtyping/submoding.
The residual ambient grammar supplies structural inversion; images remain
symbolic and are defined under those same ambient bounds. -/
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

/-- Successful signature checking supplies a compatible-shape comparison
witness whose quantified images and instantiated body are defined under the
ambient and target bounds. -/
def SchemeSubsumptionSound : Prop :=
  ∀ {fuel : Nat} {source target : Scheme} {evidence : SubsumptionEvidence},
    (source.typeParams.Nodup ∧ source.modParams.Nodup) →
    (target.typeParams.Nodup ∧ target.modParams.Nodup) →
    Residual target.bounds → checkSubsumption fuel source target = .success evidence →
    AlgebraSubsumesUnder [] source target

/-- Completeness covers every compatible internal witness with defined images
and instantiated body. Residual expressions remain symbolic and are admitted
when the relevant bounds establish their definedness guards. -/
def SchemeSubsumptionComplete : Prop :=
  ∀ {source target : Scheme},
    (source.typeParams.Nodup ∧ source.modParams.Nodup) →
    (target.typeParams.Nodup ∧ target.modParams.Nodup) →
    Residual target.bounds → AlgebraSubsumesUnder [] source target →
    ∃ n, ∀ fuel ≥ n, ∃ evidence,
      checkSubsumption fuel source target = .success evidence

end ModalityInference.Obligations
