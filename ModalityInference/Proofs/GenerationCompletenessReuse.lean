import ModalityInference.Proofs.GenerationCompletenessAlloc
import ModalityInference.Proofs.GenerationEventualRouting

/-! Ground completeness preserves the separate credit and payload usages in
reuse and supplies both freshly allocated modes from the declarative derivation. -/
namespace ModalityInference

theorem GroundTypingComplete.reuse {Δ Γ Γ₁ Γ₂ Γ₃ Γ₂₃ t u v a b m k}
    (hj : ContextJoin Δ Γ₂ Γ₃ Γ₂₃) (hkctx : ContextJoin Δ Γ₁ Γ₂₃ Γ)
    (ht : Typing Δ Γ₁ t (.modal .credit k))
    (hu : Typing Δ Γ₂ u (.modal a m)) (hv : Typing Δ Γ₃ v (.modal b m))
    (hk : Submode Δ k (.const Mode.uniqueOnly))
    (hkm : Submode Δ (.compose k (.const Mode.many)) m)
    (it : GroundTypingComplete Δ Γ₁ t (.modal .credit k))
    (iu : GroundTypingComplete Δ Γ₂ u (.modal a m))
    (iv : GroundTypingComplete Δ Γ₃ v (.modal b m)) :
    GroundTypingComplete Δ Γ (.reuse t u v) (.modal (.prod a b) m) := by
  intro A s ρ τ target hs hΔ hc hm htarget
  simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at htarget
  obtain ⟨pair, ⟨left, hleft, right, hright, rfl⟩, mode, hmode, rfl⟩ := htarget
  obtain ⟨creditMode, fixed, hcreditMode, hfixed, hkle⟩ := hk.denote hΔ.modeModels
  have hfixed' : fixed = Mode.uniqueOnly := Option.some.inj hfixed |>.symm
  subst fixed
  have htyped : (.modal .credit k : Ty).realize τ = some (.credit creditMode) := by
    simp [TypeExpr.realize, hcreditMode, GroundTy.modal, Mode.identity_compose]
  have huleft : (.modal a m : Ty).realize τ = some (left.modal mode) := by
    simp [TypeExpr.realize, hleft, hmode]
  have hvright : (.modal b m : Ty).realize τ = some (right.modal mode) := by
    simp [TypeExpr.realize, hright, hmode]
  have hc' : AlgorithmicContextCovers ρ τ A Γ (t.freeVars ∪ (u.freeVars ∪ v.freeVars)) := by
    simpa only [Term.freeVars, Finset.union_assoc] using hc
  obtain ⟨hc₁, hc₂₃⟩ := hc'.split hkctx hΔ (fun _ hi => ht.freeVars_present hi) (by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨scheme, hscheme⟩ := hu.freeVars_present hi
      exact hj.left_present hscheme
    · obtain ⟨scheme, hscheme⟩ := hv.freeVars_present hi
      exact hj.right_present hscheme)
  obtain ⟨hc₂, hc₃⟩ := hc₂₃.split hj hΔ (fun _ hi => hu.freeVars_present hi)
    (fun _ hi => hv.freeVars_present hi)
  obtain ⟨hs₁, hs₂₃⟩ := hs.split t.freeVars (u.freeVars ∪ v.freeVars)
  obtain ⟨hs₂, hs₃⟩ := hs₂₃.split u.freeVars v.freeVars
  obtain ⟨nt, rt, η, gt, hrt, hmt, hat, htt, hst⟩ :=
    it _ _ _ _ _ hs₁ hΔ hc₁ hm htyped
  have hsu := hs₂.advance hrt hs₁.contextBounded hs₁.contextFlexible
  obtain ⟨nu, ru, ζ, gu, hru, hmu, hau, htu, hsu'⟩ :=
    iu _ _ _ _ _ hsu hΔ (hc₂.source_agreesBelow hs₂.contextBounded hat) hmt huleft
  have htcount := generate_counters hrt
  have hucount := generate_counters hru
  have hagu : SolverGround.AgreesBelow ζ ρ s.nextType s.nextMode :=
    (hau.mono htcount.1 htcount.2).trans hat
  have hsv := (hs₃.advance hrt hs₁.contextBounded hs₁.contextFlexible).advance hru
    hsu.contextBounded hsu.contextFlexible
  obtain ⟨nv, rv, ξ, gv, hrv, hmv, hav, htv, hsv'⟩ :=
    iv _ _ _ _ _ hsv hΔ (hc₃.source_agreesBelow hs₃.contextBounded hagu) hmu hvright
  have hvcount := generate_counters hrv
  have hagv : SolverGround.AgreesBelow ξ ρ s.nextType s.nextMode :=
    (hav.mono (htcount.1.trans hucount.1) (htcount.2.trans hucount.2)).trans hagu
  have hb₁ := (generate_bounded hrt hs₁.contextBounded hs₁.constraintsBounded).1
  have hb₂ := (generate_bounded hru hsu.contextBounded hsu.constraintsBounded).1
  have hb₃ := (generate_bounded hrv hsv.contextBounded hsv.constraintsBounded).1
  have htt' : rt.type.realize ξ = some gt :=
    (hav.realize (hb₁.mono hucount.1 hucount.2)).trans ((hau.realize hb₁).trans htt)
  have htu' : ru.type.realize ξ = some gu := (hav.realize hb₂).trans htu
  have hready : GenerationReady A rv.state :=
    ((hs.advance hrt hs₁.contextBounded hs₁.contextFlexible).advance hru
      hsu.contextBounded hsu.contextFlexible).advance hrv hsv.contextBounded hsv.contextFlexible
  obtain ⟨χ, hχleft, hχright, hχmode, hχagree⟩ :=
    rv.state.freshTypes2_mode_model ξ left right mode
  let next : InferenceState :=
    {rv.state with nextType := rv.state.nextType + 2, nextMode := rv.state.nextMode + 1}
  obtain ⟨ω, hωcredit, hωagree⟩ := next.freshMode_model χ creditMode
  have hωleft : ω.types (.flex rv.state.nextType) = left :=
    (hωagree.1 _ (by simp [next, TypeVar.index])).trans hχleft
  have hωright : ω.types (.flex (rv.state.nextType + 1)) = right :=
    (hωagree.1 _ (by simp [next, TypeVar.index])).trans hχright
  have hωmode : ω.modes (.flex rv.state.nextMode) = mode :=
    (hωagree.2 _ (by simp [next, ModVar.index])).trans hχmode
  have hωcreditValue : ω.modes (.flex (rv.state.nextMode + 1)) = creditMode :=
    Option.some.inj hωcredit
  have hagree : SolverGround.AgreesBelow ω ξ rv.state.nextType rv.state.nextMode :=
    (hωagree.mono (by simp [next]) (by simp [next])).trans hχagree
  have htt'' := (hagree.realize (hb₁.mono (hucount.1.trans hvcount.1)
    (hucount.2.trans hvcount.2))).trans htt'
  have htu'' := (hagree.realize (hb₂.mono hvcount.1 hvcount.2)).trans htu'
  have htv'' := (hagree.realize hb₃).trans htv
  have hcompose : (creditMode.compose Mode.many).le mode = true := by
    have hh := hkm.denote hΔ.modeModels
    simpa [ModExpr.Below, ModExpr.eval, hcreditMode, hmode] using hh
  let output : Generated :=
    ⟨.modal (.prod (.var (.flex rv.state.nextType)) (.var (.flex (rv.state.nextType + 1))))
      (.var (.flex rv.state.nextMode)), .reuse rt.term ru.term rv.term,
      {nextType := rv.state.nextType + 2, nextMode := rv.state.nextMode + 2,
       constraints := rv.state.constraints ++
         [.sub rt.type (.modal .credit (.var (.flex (rv.state.nextMode + 1)))),
          .mode (.var (.flex (rv.state.nextMode + 1))) (.const Mode.uniqueOnly),
          .sub ru.type (.modal (.var (.flex rv.state.nextType)) (.var (.flex rv.state.nextMode))),
          .sub rv.type (.modal (.var (.flex (rv.state.nextType + 1))) (.var (.flex rv.state.nextMode))),
          .mode (.compose (.var (.flex (rv.state.nextMode + 1))) (.const Mode.many))
            (.var (.flex rv.state.nextMode))]}⟩
  let fuel := max nt (max nu nv)
  have hrt' := generate_monotone hrt fuel (by simp [fuel])
  have hru' := generate_monotone hru fuel (by simp [fuel])
  have hrv' := generate_monotone hrv fuel (by simp [fuel])
  refine ⟨fuel + 1, output, ω, .prod left right mode, ?_, ?_, ?_, ?_, ?_⟩
  · change generate (fuel + 1) A (.reuse t.erase u.erase v.erase) s = .success output
    simp only [generate, show t.erase.freeVars = t.freeVars by simp [Term.erase],
      show u.erase.freeVars = u.freeVars by simp [Term.erase],
      show v.erase.freeVars = v.freeVars by simp [Term.erase],
      hrt', hru', hrv', bind, pure, RunResult.bind]
    rfl
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hagree.models hready.constraintsBounded hmv c hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · refine ⟨gt, .credit creditMode, htt'', ?_, hst⟩
        simp [TypeExpr.realize, ModExpr.eval, hωcreditValue, GroundTy.modal, Mode.identity_compose]
      · exact ⟨creditMode, Mode.uniqueOnly, congrArg some hωcreditValue, rfl, hkle⟩
      · refine ⟨gu, left.modal mode, htu'', ?_, hsu'⟩
        simp [TypeExpr.realize, ModExpr.eval, hωleft, hωmode]
      · refine ⟨gv, right.modal mode, htv'', ?_, hsv'⟩
        simp [TypeExpr.realize, ModExpr.eval, hωright, hωmode]
      · refine ⟨creditMode.compose Mode.many, mode, ?_, congrArg some hωmode, hcompose⟩
        simp [ModExpr.eval, hωcreditValue]
  · exact (hagree.mono ((htcount.1.trans hucount.1).trans hvcount.1)
      ((htcount.2.trans hucount.2).trans hvcount.2)).trans hagv
  · simp [output, TypeExpr.realize, ModExpr.eval, hωleft, hωright, hωmode,
      GroundTy.modal, Mode.identity_compose]
  · simpa only [GroundTy.modal, Mode.identity_compose] using
      (Subtype.refl (a := (.prod left right mode : GroundTy).reify))

end ModalityInference
