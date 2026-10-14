import ModalityInference.Proofs.GenerationCompletenessAlloc

/-! Ground completeness for sum introduction and region elimination. -/
namespace ModalityInference

theorem GroundGenerates.injection {A t s ρ a b m} (left : Bool)
    (hready : GenerationReady A s)
    (hg : GroundGenerates A t s ρ ((if left then a else b).modal m)) :
    GroundGenerates A (if left then .inl t else .inr t) s ρ (.sum a b m) := by
  obtain ⟨fuel, r, η, ground, hr, hm, ha, ht, hsub⟩ := hg
  have hbound := generate_bounded hr hready.contextBounded hready.constraintsBounded
  have hcount := generate_counters hr
  obtain ⟨ζ, hzero, hone, hmode, hagree⟩ := r.state.freshTypes2_mode_model η a b m
  have ht' := (hagree.realize hbound.1).trans ht
  have hmodels := hagree.models hbound.2 hm
  let x : Ty := .var (.flex r.state.nextType)
  let y : Ty := .var (.flex (r.state.nextType + 1))
  let mode : ModExpr := .var (.flex r.state.nextMode)
  let state := r.state.freshType.2.freshType.2.freshMode.2
  refine ⟨fuel + 1,
    ⟨.modal (.sum x y) mode, if left then .inl r.term else .inr r.term,
      state.emit [.sub r.type (.modal (if left then x else y) mode)]⟩,
    ζ, .sum a b m, ?_, ?_, ?_, ?_, .refl⟩
  · cases left <;> simp [generate, hr, bind, pure, RunResult.bind,
      InferenceState.freshType, InferenceState.freshMode, state, x, y, mode]
  · have hconstraint : GroundSatisfies ζ (.sub r.type (.modal (if left then x else y) mode)) := by
      cases left <;> simpa [GroundSatisfies, TypeExpr.realize, ModExpr.eval, x, y, mode,
        ht', hzero, hone, hmode] using hsub
    simpa [state, InferenceState.freshType, InferenceState.freshMode, InferenceState.emit,
      GroundModels, or_imp, forall_and] using And.intro hmodels hconstraint
  · exact (hagree.mono hcount.1 hcount.2).trans ha
  · simp [TypeExpr.realize, ModExpr.eval, x, y, mode, hzero, hone, hmode, GroundTy.modal]

theorem GroundTypingComplete.inl {Δ Γ t a b m}
    (ih : GroundTypingComplete Δ Γ t (.modal a m)) :
    GroundTypingComplete Δ Γ (.inl t) (.modal (.sum a b) m) := by
  intro A s ρ τ target hs hΔ hc hm ht
  simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
  obtain ⟨sum, ⟨x, hx, y, hy, rfl⟩, n, hn, rfl⟩ := ht
  have hi := ih A s ρ τ (x.modal n) hs hΔ hc hm
    (by simp [TypeExpr.realize, hx, hn])
  simpa [Term.erase, Term.mapAnnotation, GroundTy.modal] using hi.injection (b := y) true hs

theorem GroundTypingComplete.inr {Δ Γ t a b m}
    (ih : GroundTypingComplete Δ Γ t (.modal b m)) :
    GroundTypingComplete Δ Γ (.inr t) (.modal (.sum a b) m) := by
  intro A s ρ τ target hs hΔ hc hm ht
  simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
  obtain ⟨sum, ⟨x, hx, y, hy, rfl⟩, n, hn, rfl⟩ := ht
  have hi := ih A s ρ τ (y.modal n) hs hΔ hc hm
    (by simp [TypeExpr.realize, hy, hn])
  simpa [Term.erase, Term.mapAnnotation, GroundTy.modal] using hi.injection (a := x) false hs

theorem GroundGenerates.region {A t s ρ a}
    (hready : GenerationReady A s)
    (hg : GroundGenerates A t s ρ (a.modal Mode.global)) :
    GroundGenerates A (.region t) s ρ a := by
  obtain ⟨fuel, r, η, ground, hr, hm, ha, ht, hsub⟩ := hg
  have hbound := generate_bounded hr hready.contextBounded hready.constraintsBounded
  have hcount := generate_counters hr
  obtain ⟨ζ, hnew, hagree⟩ := r.state.freshType_model η a
  have ht' := (hagree.realize hbound.1).trans ht
  have hmodels := hagree.models hbound.2 hm
  refine ⟨fuel + 1,
    ⟨r.state.freshType.1, .region r.term,
      r.state.freshType.2.emit [.sub r.type (.modal r.state.freshType.1 (.const Mode.global))]⟩,
    ζ, a, ?_, ?_, (hagree.mono hcount.1 hcount.2).trans ha, hnew, .refl⟩
  · simp [generate, hr, bind, pure, RunResult.bind]
  · have hconstraint : GroundSatisfies ζ
        (.sub r.type (.modal r.state.freshType.1 (.const Mode.global))) := by
      simpa [GroundSatisfies, TypeExpr.realize, ModExpr.eval, ht', hnew] using hsub
    simpa [InferenceState.freshType, InferenceState.emit,
      GroundModels, or_imp, forall_and] using And.intro hmodels hconstraint

theorem GroundTypingComplete.region {Δ Γ t a}
    (ih : GroundTypingComplete Δ Γ t (.modal a (.const Mode.global))) :
    GroundTypingComplete Δ Γ (.region t) a := by
  intro A s ρ τ target hs hΔ hc hm ht
  have hi := ih A s ρ τ (target.modal Mode.global) hs hΔ hc hm
    (by simp [TypeExpr.realize, ht, ModExpr.eval])
  simpa [Term.erase, Term.mapAnnotation] using hi.region hs

end ModalityInference
