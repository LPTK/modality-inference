import ModalityInference.Proofs.GenerationCompletenessAlloc
import ModalityInference.Proofs.GenerationCompletenessBinders
import ModalityInference.Proofs.GenerationEventualRouting

/-! Product elimination preserves all three fresh monomorphic bindings. -/
namespace ModalityInference

theorem GroundTypingComplete.split {Δ Γ Γ₁ Γ₂ a b c t u m}
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ)
    (ht : Typing Δ Γ₁ t (.modal (.prod a b) m))
    (hu : Typing Δ (some (Scheme.mono (.modal .credit m)) ::
      some (Scheme.mono (.modal a m)) :: some (Scheme.mono (.modal b m)) :: Γ₂) u c)
    (iht : GroundTypingComplete Δ Γ₁ t (.modal (.prod a b) m))
    (ihu : GroundTypingComplete Δ (some (Scheme.mono (.modal .credit m)) ::
      some (Scheme.mono (.modal a m)) :: some (Scheme.mono (.modal b m)) :: Γ₂) u c) :
    GroundTypingComplete Δ Γ (.split t u) c := by
  intro A s ρ τ target hs hΔ hΓ hmodel htarget
  obtain ⟨prodType, hprod⟩ := Option.isSome_iff_exists.mp (ht.realize_defined hΔ)
  have hprod' := hprod
  simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hprod'
  obtain ⟨prod, ⟨leftType, hleft, rightType, hright, rfl⟩, mode, hmode, rfl⟩ := hprod'
  let X := t.freeVars
  let Y := u.freeVars 3
  let A₁ := (splitContext X Y A).1
  let A₂ := (splitContext X Y A).2
  have hcontexts : AlgorithmicContextCovers ρ τ A₁ Γ₁ X ∧
      AlgorithmicContextCovers ρ τ A₂ Γ₂ Y := by
    apply AlgorithmicContextCovers.split hΓ hj hΔ (fun i hi => ht.freeVars_present hi)
    intro i hi
    simpa using hu.freeVars_present ((u.mem_freeVars_add 0 3 i).mp hi)
  have hready := hs.split X Y
  obtain ⟨nt, rt, η, ground, hrt, hη, hat, hreal, hsub⟩ :=
    iht A₁ s ρ τ _ hready.1 hΔ hcontexts.1 hmodel hprod
  have hrtBounded := generate_bounded hrt hready.1.contextBounded hready.1.constraintsBounded
  have hrtFlexible := generate_flexible hrt hready.1.contextFlexible hready.1.constraintsFlexible
  have hcount := generate_counters hrt
  obtain ⟨ζ, hza, hzb, hzm, haz⟩ :=
    rt.state.freshTypes2_mode_model η leftType rightType mode
  let ta : Ty := .var (.flex rt.state.nextType)
  let tb : Ty := .var (.flex (rt.state.nextType + 1))
  let mm : ModExpr := .var (.flex rt.state.nextMode)
  let next : InferenceState :=
    {nextType := rt.state.nextType + 2, nextMode := rt.state.nextMode + 1,
      constraints := rt.state.constraints ++ [.sub rt.type (.modal (.prod ta tb) mm)]}
  have hnextModel : GroundModels ζ next.constraints := by
    have hhead : GroundSatisfies ζ (.sub rt.type (.modal (.prod ta tb) mm)) :=
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
  have hcreditBounded : (TypeExpr.modal .credit mm).Bounded next.nextType next.nextMode := by
    simp [next, mm, TypeExpr.Bounded, ModExpr.Bounded, ModVar.index]
  have hleftBounded : (TypeExpr.modal ta mm).Bounded next.nextType next.nextMode := by
    simp [next, ta, mm, TypeExpr.Bounded, ModExpr.Bounded, TypeVar.index, ModVar.index]
  have hrightBounded : (TypeExpr.modal tb mm).Bounded next.nextType next.nextMode := by
    simp [next, tb, mm, TypeExpr.Bounded, ModExpr.Bounded, TypeVar.index, ModVar.index]
  have hcreditFlexible : (TypeExpr.modal .credit mm).Flexible := by
    simp [mm, TypeExpr.Flexible, ModExpr.Flexible]
  have hleftFlexible : (TypeExpr.modal ta mm).Flexible := by
    simp [ta, mm, TypeExpr.Flexible, ModExpr.Flexible]
  have hrightFlexible : (TypeExpr.modal tb mm).Flexible := by
    simp [tb, mm, TypeExpr.Flexible, ModExpr.Flexible]
  have hbodyReady := ((hnext.mono hrightBounded hrightFlexible).mono hleftBounded hleftFlexible).mono
    hcreditBounded hcreditFlexible
  have hbodyCovers : AlgorithmicContextCovers ζ τ
      (.binding (some (.mono (.modal .credit mm))) ::
        .binding (some (.mono (.modal ta mm))) :: .binding (some (.mono (.modal tb mm))) :: A₂)
      (some (.mono (.modal .credit m)) :: some (.mono (.modal a m)) ::
        some (.mono (.modal b m)) :: Γ₂) u.freeVars := by
    have hrightCovers := hcontextζ.binding
      (SchemeCovers.mono (a := .modal tb mm) (b := .modal b m)
        (x := rightType.modal mode) (y := rightType.modal mode)
        (by simp [tb, mm, TypeExpr.realize, ModExpr.eval, hzb, hzm])
        (by simp [TypeExpr.realize, hright, hmode]) (.refl))
      (used := u.freeVars 2) (fun i hi => (u.mem_freeVars_add 2 1 i).mpr hi)
    have hleftCovers := hrightCovers.binding
      (SchemeCovers.mono (a := .modal ta mm) (b := .modal a m)
        (x := leftType.modal mode) (y := leftType.modal mode)
        (by simp [ta, mm, TypeExpr.realize, ModExpr.eval, hza, hzm])
        (by simp [TypeExpr.realize, hleft, hmode]) (.refl))
      (used := u.freeVars 1) (fun i hi => (u.mem_freeVars_add 1 1 i).mpr hi)
    exact hleftCovers.binding
      (SchemeCovers.mono (x := .credit mode) (y := .credit mode)
        (by simp [mm, TypeExpr.realize, ModExpr.eval, hzm, GroundTy.modal])
        (by simp [TypeExpr.realize, hmode, GroundTy.modal]) (.refl))
      (fun i hi => (u.mem_freeVars_add 0 1 i).mpr hi)
  obtain ⟨nu, ru, ψ, bodyGround, hru, hψ, hau, hruReal, hruSub⟩ :=
    ihu _ next ζ τ target hbodyReady hΔ hbodyCovers hnextModel htarget
  let fuel := max nt nu
  have hrt' := generate_monotone hrt fuel (Nat.le_max_left _ _)
  have hru' := generate_monotone hru fuel (Nat.le_max_right _ _)
  refine ⟨fuel + 1, ⟨ru.type, .split rt.term ru.term, ru.state⟩, ψ, bodyGround,
    ?_, hψ, ?_, hruReal, hruSub⟩
  · change generate (fuel + 1) A (.split t.erase u.erase) s = _
    have hrt'' : generate fuel (splitContext t.freeVars (u.freeVars 3) A).1 t.erase s =
        .success rt := hrt'
    simp only [generate, show t.erase.freeVars = t.freeVars by simp [Term.erase],
      show u.erase.freeVars 3 = u.freeVars 3 by simp [Term.erase],
      hrt'', bind, pure, RunResult.bind]
    have hrFinal := congrArg (fun result : RunResult Generated =>
      result.bind (fun body => .success (Generated.mk body.type (.split rt.term body.term) body.state))) hru'
    simpa only [next, ta, tb, mm, A₂, X, Y, InferenceState.freshType,
      InferenceState.freshMode, InferenceState.emit, RunResult.bind, Nat.add_assoc] using hrFinal
  · apply SolverGround.AgreesBelow.trans (h' := hstartAgree)
    exact hau.mono (hcount.1.trans (by simp [next])) (hcount.2.trans (by simp [next]))

end ModalityInference
