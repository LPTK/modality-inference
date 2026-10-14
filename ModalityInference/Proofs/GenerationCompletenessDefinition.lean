import ModalityInference.Proofs.GenerationCompletenessBase
import ModalityInference.Proofs.GeneralizedCoverage

/-! Completeness of closed definitions uses every ground instance of the
right-hand side and the principal residual returned by its solver call. -/
namespace ModalityInference

theorem GroundTypingComplete.defn {Δ Γ rhs body a b rhsBounds}
    (hrhs : Typing rhsBounds [] rhs a) (hsat : BoundsSatisfiable rhsBounds)
    (ihr : GroundTypingComplete rhsBounds [] rhs a)
    (ihb : GroundTypingComplete Δ (some (Scheme.generalize rhsBounds a) :: Γ) body b) :
    GroundTypingComplete Δ Γ (.defn rhs body) b := by
  intro A s ρ τ target hs hΔ hΓ hmodel htarget
  let initial : InferenceState := {nextType := s.nextType, nextMode := s.nextMode}
  have hready : GenerationReady [] initial :=
    ⟨AlgorithmicContext.bounded_nil _ _, AlgorithmicContext.flexible_nil,
      AlgorithmicContext.modParamsBounded_nil _, Bounds.bounded_nil _ _, Bounds.flexible_nil⟩
  obtain ⟨η, hη⟩ := hsat.ground
  obtain ⟨ground, hground⟩ := Option.isSome_iff_exists.mp (hrhs.realize_defined hη)
  obtain ⟨n, r, ξ, lower, hg, hξ, _, _, _⟩ := ihr [] initial ρ η ground hready hη
    (AlgorithmicContextCovers.nil _ _ _) (by simp [initial, GroundModels]) hground
  have hb := generate_bounded hg hready.contextBounded hready.constraintsBounded
  have hf := generate_flexible hg hready.contextFlexible hready.constraintsFlexible
  obtain ⟨k, hk⟩ := solveFrom_complete hb.2 hf.2 ⟨ξ, hξ⟩
  obtain ⟨solved, hsolved⟩ := hk k le_rfl
  let scheme := Scheme.generalize solved.bounds (solved.substitution.ty r.type)
  have hscheme : SchemeCovers ρ τ scheme (Scheme.generalize rhsBounds a) := by
    apply generate_generalize_covers hg hsolved
    intro ψ u hψ hu
    obtain ⟨fuel, q, ζ, v, hq, hz, _, hv, hvu⟩ := ihr [] initial ρ ψ u hready hψ
      (AlgorithmicContextCovers.nil _ _ _) (by simp [initial, GroundModels]) hu
    exact ⟨fuel, q, ζ, v, hq, hz, hv, hvu⟩
  have hstart := generate_counters hg
  have hcount := solveFrom_counters hsolved
  have htypes : s.nextType ≤ solved.nextType := hstart.1.trans hcount.1
  have hmodes : s.nextMode ≤ solved.nextMode := hstart.2.trans hcount.2
  let next : InferenceState := {s with nextType := solved.nextType, nextMode := solved.nextMode}
  have hsolvedBounded := solveFrom_fresh hb.2 hsolved
  have hsolvedFlexible := solveFrom_flexible hf.2 hsolved
  have hnext : GenerationReady (.binding (some scheme) :: A) next := by
    refine ⟨?_, ?_, ?_, hs.constraintsBounded.mono htypes hmodes, hs.constraintsFlexible⟩
    · simpa [next, ContextEntry.Bounded, Scheme.Bounded, scheme, Scheme.generalize] using
        And.intro (And.intro (hsolvedBounded.2.ty (hb.1.mono hcount.1 hcount.2)) hsolvedBounded.1)
          (hs.contextBounded.mono htypes hmodes)
    · simpa [ContextEntry.Flexible, Scheme.Flexible, scheme, Scheme.generalize] using
        And.intro (And.intro (hsolvedFlexible.2.ty hf.1) hsolvedFlexible.1) hs.contextFlexible
    · exact AlgorithmicContext.modParamsBounded_binding.mpr
        ⟨by simpa [scheme] using generate_closed_modParamsBounded hg hsolved,
          hs.parametersBounded.mono hmodes⟩
  have hbodyContext : AlgorithmicContextCovers ρ τ (.binding (some scheme) :: A)
      (some (Scheme.generalize rhsBounds a) :: Γ) body.freeVars := by
    intro i hi t ht
    cases i
    case zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht
      cases ht
      exact ⟨scheme, .here, hscheme⟩
    case succ i =>
      have hi' : i ∈ (Term.defn rhs body).freeVars :=
        Finset.mem_union_right _ ((body.mem_freeVars_add 0 1 i).mpr hi)
      obtain ⟨source, hsource, hcovers⟩ := hΓ i hi' t (by simpa using ht)
      exact ⟨source, .there hsource, hcovers⟩
  obtain ⟨l, bodyResult, ζ, bodyGround, hbody, hz, hagree, hreal, hsub⟩ :=
    ihb _ next ρ τ target hnext hΔ hbodyContext hmodel htarget
  let fuel := max n (max k l)
  have hr' := generate_monotone hg fuel (by simp [fuel])
  have hs' := solveFrom_monotone hsolved fuel (by simp [fuel])
  have hb' := generate_monotone hbody fuel (by simp [fuel])
  have hclosed : rhs.erase.freeVars = ∅ := by simpa [Term.erase] using hrhs.closed
  refine ⟨fuel + 1, ⟨bodyResult.type,
    .defn r.term bodyResult.term, bodyResult.state⟩,
    ζ, bodyGround, ?_, hz, hagree.mono htypes hmodes, hreal, hsub⟩
  change generate (fuel + 1) A (.defn rhs.erase body.erase) s = _
  simp only [initial] at hr'
  simp only [scheme, next] at hb'
  simp [generate, hclosed, hr', hs', hb', bind, pure, RunResult.bind]

end ModalityInference
