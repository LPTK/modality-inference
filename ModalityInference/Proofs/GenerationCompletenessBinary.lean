import ModalityInference.Proofs.GenerationCompletenessAlloc
import ModalityInference.Proofs.GenerationEventualRouting

/-! Ground completeness for applications and both product allocations. -/
namespace ModalityInference

theorem GroundTypingComplete.binary_models {Δ Γ Γ₁ Γ₂ x y a b}
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ) (hx : Typing Δ Γ₁ x a) (hy : Typing Δ Γ₂ y b)
    (ix : GroundTypingComplete Δ Γ₁ x a) (iy : GroundTypingComplete Δ Γ₂ y b)
    {A s ρ τ ga gb} (hs : GenerationReady A s) (hΔ : GroundModels τ Δ)
    (hctx : AlgorithmicContextCovers ρ τ A Γ (x.freeVars ∪ y.freeVars))
    (hm : GroundModels ρ s.constraints) (ha : a.realize τ = some ga) (hb : b.realize τ = some gb) :
    ∃ fuel rx ry η gx gy,
      generate fuel (splitContext x.freeVars y.freeVars A).1 x.erase s = .success rx ∧
      generate fuel (splitContext x.freeVars y.freeVars A).2 y.erase rx.state = .success ry ∧
      GroundModels η ry.state.constraints ∧ SolverGround.AgreesBelow η ρ s.nextType s.nextMode ∧
      rx.type.realize η = some gx ∧ ry.type.realize η = some gy ∧
      Subtype [] gx.reify ga.reify ∧ Subtype [] gy.reify gb.reify ∧
      GenerationReady A ry.state ∧ rx.type.Bounded ry.state.nextType ry.state.nextMode ∧
      ry.type.Bounded ry.state.nextType ry.state.nextMode := by
  obtain ⟨hc₁, hc₂⟩ := hctx.split hj hΔ
    (fun _ hi => hx.freeVars_present hi) (fun _ hi => hy.freeVars_present hi)
  obtain ⟨hs₁, hs₂⟩ := hs.split x.freeVars y.freeVars
  obtain ⟨nx, rx, η, gx, hrx, hmx, hax, htx, hsubx⟩ := ix _ _ _ _ _ hs₁ hΔ hc₁ hm ha
  have hsy := hs₂.advance hrx hs₁.contextBounded hs₁.contextFlexible
  obtain ⟨ny, ry, ζ, gy, hry, hmy, hay, hty, hsuby⟩ := iy _ _ _ _ _ hsy hΔ
    (hc₂.source_agreesBelow hs₂.contextBounded hax) hmx hb
  have hbx := (generate_bounded hrx hs₁.contextBounded hs₁.constraintsBounded).1
  have hcounters := generate_counters hry
  refine ⟨max nx ny, rx, ry, ζ, gx, gy,
    generate_monotone hrx _ (Nat.le_max_left _ _),
    generate_monotone hry _ (Nat.le_max_right _ _), hmy,
    (hay.mono (generate_counters hrx).1 (generate_counters hrx).2).trans hax,
    (hay.realize hbx).trans htx, hty, hsubx, hsuby, ?_,
    hbx.mono hcounters.1 hcounters.2,
    (generate_bounded hry hsy.contextBounded hsy.constraintsBounded).1⟩
  exact (hs.advance hrx hs₁.contextBounded hs₁.contextFlexible).advance hry
    hsy.contextBounded hsy.contextFlexible

theorem GroundTypingComplete.app {Δ Γ Γ₁ Γ₂ f x a b}
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ) (hf : Typing Δ Γ₁ f (.fn a b)) (hx : Typing Δ Γ₂ x a)
    (ihf : GroundTypingComplete Δ Γ₁ f (.fn a b)) (ihx : GroundTypingComplete Δ Γ₂ x a) :
    GroundTypingComplete Δ Γ (.app f x) b := by
  intro A s ρ τ target hs hΔ hc hm ht
  obtain ⟨domain, hdomain⟩ := Option.isSome_iff_exists.mp (hx.realize_defined hΔ)
  have hfn : (TypeExpr.fn a b).realize τ = some (.fn domain target Mode.identity) := by
    simp [TypeExpr.realize, hdomain, ht]
  obtain ⟨fuel, rf, rx, η, gf, gx, hrf, hrx, hmodel, hagree, htf, htx, hsf, hsx,
    hready, hbf, hbx⟩ := binary_models hj hf hx ihf ihx hs hΔ hc hm hfn hdomain
  obtain ⟨ζ, hz, _, hmode, hsame⟩ := rx.state.freshTypes2_mode_model η target target Mode.identity
  have htf' := (hsame.realize hbf).trans htf
  have htx' := (hsame.realize hbx).trans htx
  let output : Generated :=
    ⟨.var (.flex rx.state.nextType), .app rf.term rx.term,
      {nextType := rx.state.nextType + 1, nextMode := rx.state.nextMode + 1,
        constraints := rx.state.constraints ++ [.sub rf.type
          (.modal (.fn rx.type (.var (.flex rx.state.nextType))) (.var (.flex rx.state.nextMode)))]}⟩
  refine ⟨fuel + 1, output, ζ, target, ?_, ?_, ?_, ?_, .refl⟩
  · change generate (fuel + 1) A (.app f.erase x.erase) s = .success output
    simp only [generate, show f.erase.freeVars = f.freeVars by simp [Term.erase],
      show x.erase.freeVars = x.freeVars by simp [Term.erase],
      hrf, hrx, bind, pure, RunResult.bind]
    rfl
  · intro c hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hsame.models hready.constraintsBounded hmodel c hmem
    · obtain rfl := List.mem_singleton.mp hmem
      refine ⟨gf, .fn gx target Mode.identity, htf', ?_, ?_⟩
      · simp [TypeExpr.realize, htx', hz, ModExpr.eval, hmode, GroundTy.modal]
      · exact hsf.trans (GroundOrder.to_subtype (.fn (GroundOrder.of_subtype hsx) (.refl _) id id))
  · exact (hsame.mono ((generate_counters hrf).1.trans (generate_counters hrx).1)
      ((generate_counters hrf).2.trans (generate_counters hrx).2)).trans hagree
  · exact congrArg some hz

theorem GroundTypingComplete.pair_mode {Δ Γ Γ₁ Γ₂ x y a b m n} (stack : Bool)
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hx : Typing Δ Γ₁ x (.modal a m)) (hy : Typing Δ Γ₂ y (.modal b m))
    (ix : GroundTypingComplete Δ Γ₁ x (.modal a m))
    (iy : GroundTypingComplete Δ Γ₂ y (.modal b m))
    (hmn : n = m ∨ Submode Δ m n)
    (hlocal : stack = true → Submode Δ (.const Mode.localLower) n) :
    GroundTypingComplete Δ Γ (if stack then .stackPair x y else .pair x y)
      (.modal (.prod a b) n) := by
  intro A s ρ τ target hs hΔ hc hm ht
  simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
  obtain ⟨prod, ⟨ga, ha, gb, hb, rfl⟩, outputMode, hn, rfl⟩ := ht
  obtain ⟨inputMode, hinput, hle⟩ : ∃ k, m.eval (some ∘ τ.modes) = some k ∧ k.le outputMode = true := by
    rcases hmn with rfl | hmn
    · exact ⟨outputMode, hn, Mode.le_refl _⟩
    · simpa [ModExpr.Below, hn] using hmn.denote hΔ.modeModels
  have hctx : AlgorithmicContextCovers ρ τ A Γ (x.freeVars ∪ y.freeVars) := by
    cases stack <;> simpa [Term.freeVars] using hc
  obtain ⟨fuel, rx, ry, η, gx, gy, hrx, hry, hmodel, hagree, htx, hty, hsx, hsy,
    hready, hbx, hby⟩ := binary_models (ga := ga.modal inputMode) (gb := gb.modal inputMode)
      hj hx hy ix iy hs hΔ hctx hm
      (by simp [TypeExpr.realize, ha, hinput]) (by simp [TypeExpr.realize, hb, hinput])
  obtain ⟨ζ, hzero, hone, hmode, hsame⟩ := ry.state.freshTypes2_mode_model η ga gb outputMode
  have htx' := (hsame.realize hbx).trans htx
  have hty' := (hsame.realize hby).trans hty
  have hmodels := hsame.models hready.constraintsBounded hmodel
  let first : Ty := .var (.flex ry.state.nextType)
  let second : Ty := .var (.flex (ry.state.nextType + 1))
  let mode : ModExpr := .var (.flex ry.state.nextMode)
  let state := ry.state.freshType.2.freshType.2.freshMode.2.emit
    [.sub rx.type (.modal first mode), .sub ry.type (.modal second mode)]
  have hfirst : GroundSatisfies ζ (.sub rx.type (.modal first mode)) := by
    simpa [GroundSatisfies, TypeExpr.realize, ModExpr.eval, first, mode, htx', hzero, hmode]
      using hsx.trans ((Subtype.refl (a := ga.reify)).ground_modal hle)
  have hsecond : GroundSatisfies ζ (.sub ry.type (.modal second mode)) := by
    simpa [GroundSatisfies, TypeExpr.realize, ModExpr.eval, second, mode, hty', hone, hmode]
      using hsy.trans ((Subtype.refl (a := gb.reify)).ground_modal hle)
  have hstate : GroundModels ζ state.constraints := by
    simpa [state, InferenceState.freshType, InferenceState.freshMode, InferenceState.emit,
      GroundModels, or_imp, forall_and] using And.intro hmodels (And.intro hfirst hsecond)
  refine ⟨fuel + 1, ⟨.modal (.prod first second) mode,
    if stack then .stackPair rx.term ry.term else .pair rx.term ry.term,
    if stack then state.emit [.mode (.const Mode.localLower) mode] else state⟩,
    ζ, .prod ga gb outputMode, ?_, ?_, ?_, ?_, ?_⟩
  · cases stack
    all_goals simp only [Bool.false_eq_true, ↓reduceIte,
      Term.erase, Term.mapAnnotation, generate, Term.freeVars_mapAnnotation,
      bind, pure, RunResult.bind] at *
    all_goals simp only [hrx, hry]
    all_goals rfl
  · cases stack with
    | false => exact hstate
    | true =>
      have hguard : GroundSatisfies ζ (.mode (.const Mode.localLower) mode) := by
        simpa [GroundSatisfies, ModExpr.Below, ModExpr.eval, mode, hmode, hn]
          using (hlocal rfl).denote hΔ.modeModels
      simpa [InferenceState.emit, GroundModels, or_imp, forall_and] using And.intro hstate hguard
  · exact (hsame.mono ((generate_counters hrx).1.trans (generate_counters hry).1)
      ((generate_counters hrx).2.trans (generate_counters hry).2)).trans hagree
  · simp [TypeExpr.realize, ModExpr.eval, first, second, mode, hzero, hone, hmode, GroundTy.modal]
  · simp only [GroundTy.modal, Mode.identity_compose]
    exact .refl

theorem GroundTypingComplete.pair {Δ Γ Γ₁ Γ₂ x y a b m}
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hx : Typing Δ Γ₁ x (.modal a m)) (hy : Typing Δ Γ₂ y (.modal b m))
    (ix : GroundTypingComplete Δ Γ₁ x (.modal a m))
    (iy : GroundTypingComplete Δ Γ₂ y (.modal b m)) :
    GroundTypingComplete Δ Γ (.pair x y) (.modal (.prod a b) m) :=
  pair_mode false hj hx hy ix iy (Or.inl rfl) (by simp)

theorem GroundTypingComplete.stackPair {Δ Γ Γ₁ Γ₂ x y a b m n}
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hx : Typing Δ Γ₁ x (.modal a m)) (hy : Typing Δ Γ₂ y (.modal b m))
    (ix : GroundTypingComplete Δ Γ₁ x (.modal a m))
    (iy : GroundTypingComplete Δ Γ₂ y (.modal b m))
    (hmn : Submode Δ m n) (hlocal : Submode Δ (.const Mode.localLower) n) :
    GroundTypingComplete Δ Γ (.stackPair x y) (.modal (.prod a b) n) :=
  pair_mode true hj hx hy ix iy (Or.inr hmn) (fun _ => hlocal)

end ModalityInference
