import ModalityInference.Proofs.GenerationCompletenessAlloc
import ModalityInference.Proofs.GenerationCompletenessBinders
import ModalityInference.Proofs.GenerationEventualRouting

/-! Ground completeness for elimination forms with fresh component types. -/
namespace ModalityInference

theorem InferenceState.freshTypes3_mode_model (s : InferenceState) (ρ : GroundAssignment)
    (a b c : GroundTy) (m : Mode) : ∃ η : GroundAssignment,
    η.types (.flex s.nextType) = a ∧ η.types (.flex (s.nextType + 1)) = b ∧
    η.types (.flex (s.nextType + 2)) = c ∧ η.modes (.flex s.nextMode) = m ∧
    SolverGround.AgreesBelow η ρ s.nextType s.nextMode := by
  refine ⟨(((ρ.setType (.flex s.nextType) a).setType (.flex (s.nextType + 1)) b).setType
    (.flex (s.nextType + 2)) c).setMode (.flex s.nextMode) m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [GroundAssignment.setType, GroundAssignment.setMode]
  · simp [GroundAssignment.setType, GroundAssignment.setMode]
  · simp [GroundAssignment.setType, GroundAssignment.setMode]
  · simp [GroundAssignment.setMode]
  · intro v hv
    have h0 : v ≠ .flex s.nextType := by intro he; subst v; exact Nat.lt_irrefl _ hv
    have h1 : v ≠ .flex (s.nextType + 1) := by
      intro he; subst v; simp [TypeVar.index] at hv; omega
    have h2 : v ≠ .flex (s.nextType + 2) := by
      intro he; subst v; simp [TypeVar.index] at hv; omega
    simp [GroundAssignment.setType, GroundAssignment.setMode, h0, h1, h2]
  · intro v hv
    have h0 : v ≠ .flex s.nextMode := by intro he; subst v; exact Nat.lt_irrefl _ hv
    simp [GroundAssignment.setMode, GroundAssignment.setType, h0]

theorem GroundTypingComplete.case {Δ Γ Γ₁ Γ₂ a b c t u v m}
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ)
    (ht : Typing Δ Γ₁ t (.modal (.sum a b) m))
    (hu : Typing Δ (some (Scheme.mono (.modal a m)) :: Γ₂) u c)
    (hv : Typing Δ (some (Scheme.mono (.modal b m)) :: Γ₂) v c)
    (iht : GroundTypingComplete Δ Γ₁ t (.modal (.sum a b) m))
    (ihu : GroundTypingComplete Δ (some (Scheme.mono (.modal a m)) :: Γ₂) u c)
    (ihv : GroundTypingComplete Δ (some (Scheme.mono (.modal b m)) :: Γ₂) v c) :
    GroundTypingComplete Δ Γ (.case t u v) c := by
  intro A s ρ τ target hs hΔ hΓ hmodel htarget
  obtain ⟨sumType, hsum⟩ := Option.isSome_iff_exists.mp (ht.realize_defined hΔ)
  have hsum' := hsum
  simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hsum'
  obtain ⟨sum, ⟨leftType, hleft, rightType, hright, rfl⟩, mode, hmode, rfl⟩ := hsum'
  let X := t.freeVars
  let Y := u.freeVars 1 ∪ v.freeVars 1
  let A₁ := (splitContext X Y A).1
  let A₂ := (splitContext X Y A).2
  have hcontexts : AlgorithmicContextCovers ρ τ A₁ Γ₁ X ∧
      AlgorithmicContextCovers ρ τ A₂ Γ₂ Y := by
    apply AlgorithmicContextCovers.split (by simpa [X, Y, Term.freeVars,
      Finset.union_assoc] using hΓ) hj hΔ (fun i hi => ht.freeVars_present hi)
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · simpa using hu.freeVars_present ((u.mem_freeVars_add 0 1 i).mp hi)
    · simpa using hv.freeVars_present ((v.mem_freeVars_add 0 1 i).mp hi)
  have hready := hs.split X Y
  obtain ⟨nt, rt, η, ground, hrt, hη, hat, hreal, hsub⟩ :=
    iht A₁ s ρ τ _ hready.1 hΔ hcontexts.1 hmodel hsum
  have hrtBounded := generate_bounded hrt hready.1.contextBounded hready.1.constraintsBounded
  have hrtFlexible := generate_flexible hrt hready.1.contextFlexible hready.1.constraintsFlexible
  have hcount := generate_counters hrt
  obtain ⟨ζ, hza, hzb, hzc, hzm, haz⟩ :=
    rt.state.freshTypes3_mode_model η leftType rightType target mode
  let ta : Ty := .var (.flex rt.state.nextType)
  let tb : Ty := .var (.flex (rt.state.nextType + 1))
  let tc : Ty := .var (.flex (rt.state.nextType + 2))
  let mm : ModExpr := .var (.flex rt.state.nextMode)
  let next : InferenceState :=
    {nextType := rt.state.nextType + 3, nextMode := rt.state.nextMode + 1,
      constraints := rt.state.constraints ++ [.sub rt.type (.modal (.sum ta tb) mm)]}
  have hnextModel : GroundModels ζ next.constraints := by
    have hhead : GroundSatisfies ζ (.sub rt.type (.modal (.sum ta tb) mm)) :=
      ⟨ground, _, (haz.realize hrtBounded.1).trans hreal,
        by simp [ta, tb, mm, TypeExpr.realize, ModExpr.eval, hza, hzb, hzm], hsub⟩
    simpa [next, GroundModels, or_imp, forall_and] using
      And.intro (haz.models hrtBounded.2 hη) hhead
  have hnext : GenerationReady A₂ next := by
    refine (hready.2.advance hrt hready.1.contextBounded hready.1.contextFlexible).restate
      (by simp [next]) (by simp [next]) ?_ ?_
    · simp only [next, Bounds.bounded_append, Bounds.bounded_cons, Bounds.bounded_nil, and_true]
      refine ⟨hrtBounded.2.mono (by omega) (by omega), ?_⟩
      refine ⟨hrtBounded.1.mono (by omega) (by omega), ?_⟩
      simp [ta, tb, mm, TypeExpr.Bounded, ModExpr.Bounded, TypeVar.index, ModVar.index]
    · simpa [next, ta, tb, mm, Constraint.Flexible, TypeExpr.Flexible, ModExpr.Flexible] using
        hrtFlexible.symm
  have hstartAgree := (haz.mono hcount.1 hcount.2).trans hat
  have hcontextζ := hcontexts.2.source_agreesBelow hready.2.contextBounded hstartAgree
  have hleftBounded : (TypeExpr.modal ta mm).Bounded next.nextType next.nextMode := by
    simp [next, ta, mm, TypeExpr.Bounded, ModExpr.Bounded, TypeVar.index, ModVar.index]
  have hrightBounded : (TypeExpr.modal tb mm).Bounded next.nextType next.nextMode := by
    simp [next, tb, mm, TypeExpr.Bounded, ModExpr.Bounded, TypeVar.index, ModVar.index]
  have hleftFlexible : (TypeExpr.modal ta mm).Flexible := by
    simp [ta, mm, TypeExpr.Flexible, ModExpr.Flexible]
  have hrightFlexible : (TypeExpr.modal tb mm).Flexible := by
    simp [tb, mm, TypeExpr.Flexible, ModExpr.Flexible]
  have hleftReady := hnext.mono hleftBounded hleftFlexible
  have hrightReady := hnext.mono hrightBounded hrightFlexible
  have hleftCovers : AlgorithmicContextCovers ζ τ
      (.binding (some (.mono (.modal ta mm))) :: A₂)
      (some (.mono (.modal a m)) :: Γ₂) u.freeVars := by
    apply (hcontextζ.restrict (Finset.subset_union_left)).binding
      (SchemeCovers.mono (x := leftType.modal mode) (y := leftType.modal mode)
        (by simp [ta, mm, TypeExpr.realize, ModExpr.eval, hza, hzm])
        (by simp [TypeExpr.realize, hleft, hmode]) (.refl))
    exact fun i hi => (u.mem_freeVars_add 0 1 i).mpr hi
  have hrightCovers : AlgorithmicContextCovers ζ τ
      (.binding (some (.mono (.modal tb mm))) :: A₂)
      (some (.mono (.modal b m)) :: Γ₂) v.freeVars := by
    apply (hcontextζ.restrict (Finset.subset_union_right)).binding
      (SchemeCovers.mono (x := rightType.modal mode) (y := rightType.modal mode)
        (by simp [tb, mm, TypeExpr.realize, ModExpr.eval, hzb, hzm])
        (by simp [TypeExpr.realize, hright, hmode]) (.refl))
    exact fun i hi => (v.mem_freeVars_add 0 1 i).mpr hi
  obtain ⟨nu, ru, ψ, leftGround, hru, hψ, hau, hruReal, hruSub⟩ :=
    ihu _ next ζ τ target hleftReady hΔ hleftCovers hnextModel htarget
  have hrightReady' := hrightReady.advance hru hleftReady.contextBounded hleftReady.contextFlexible
  have hrightCovers' := hrightCovers.source_agreesBelow hrightReady.contextBounded hau
  obtain ⟨nv, rv, χ, rightGround, hrv, hχ, hav, hrvReal, hrvSub⟩ :=
    ihv _ ru.state ψ τ target hrightReady' hΔ hrightCovers' hψ htarget
  have hucount := generate_counters hru
  have huBounded := generate_bounded hru hleftReady.contextBounded hleftReady.constraintsBounded
  have hfinalAgree := (hav.mono hucount.1 hucount.2).trans hau
  have htc : tc.Bounded next.nextType next.nextMode := by
    simp [next, tc, TypeExpr.Bounded, TypeVar.index]
  have htcReal : tc.realize χ = some target :=
    (hfinalAgree.realize htc).trans (by simp [tc, TypeExpr.realize, hzc])
  have hfinalModel : GroundModels χ
      (rv.state.constraints ++ [.sub ru.type tc, .sub rv.type tc]) := by
    have hlu : GroundSatisfies χ (.sub ru.type tc) :=
      ⟨leftGround, target, (hav.realize huBounded.1).trans hruReal, htcReal, hruSub⟩
    have hlv : GroundSatisfies χ (.sub rv.type tc) :=
      ⟨rightGround, target, hrvReal, htcReal, hrvSub⟩
    simpa [GroundModels, or_imp, forall_and] using And.intro hχ (And.intro hlu hlv)
  let fuel := max nt (max nu nv)
  have hrt' := generate_monotone hrt fuel (by simp [fuel])
  have hru' := generate_monotone hru fuel (by simp [fuel])
  have hrv' := generate_monotone hrv fuel (by simp [fuel])
  refine ⟨fuel + 1, ⟨tc, .case rt.term ru.term rv.term,
      rv.state.emit [.sub ru.type tc, .sub rv.type tc]⟩, χ, target, ?_, hfinalModel,
      (hfinalAgree.mono (hcount.1.trans (by simp [next]))
        (hcount.2.trans (by simp [next]))).trans hstartAgree, htcReal, .refl⟩
  change generate (fuel + 1) A (.case t.erase u.erase v.erase) s = _
  have hft : t.erase.freeVars = X := by simp [Term.erase, X]
  have hfu : u.erase.freeVars 1 = u.freeVars 1 := by simp [Term.erase]
  have hfv : v.erase.freeVars 1 = v.freeVars 1 := by simp [Term.erase]
  simp only [A₁, Y] at hrt'
  simp only [A₂, Y, next, ta, tb, mm] at hru' hrv'
  simp [generate, hft, hfu, hfv, hrt', hru', hrv', tc,
    InferenceState.freshType, InferenceState.freshMode, InferenceState.emit,
    bind, pure, RunResult.bind]

end ModalityInference
