import ModalityInference.Proofs.GenerationCompletenessBinders
import ModalityInference.Proofs.GenerationCompletenessContext

/-! A fresh symbolic lock and parameter represent every ground lambda typing. -/
namespace ModalityInference

theorem GroundTypingComplete.lam {Δ Γ captured t a b m}
    (hl : Lock Δ m Γ captured)
    (ih : GroundTypingComplete Δ (some (Scheme.mono a) :: captured) t b) :
    GroundTypingComplete Δ Γ (.lam (captured.restrict (t.freeVars 1)) t)
      (.modal (.fn a b) m) := by
  intro A s ρ τ target hs hΔ hc hm ht
  simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ht
  obtain ⟨function, ⟨domain, hdomain, codomain, hcodomain, rfl⟩, mode, hmode, rfl⟩ := ht
  obtain ⟨η, hd, ha⟩ := s.freshType_model ρ domain
  obtain ⟨ζ, hmode', hb⟩ := s.freshType.2.freshMode_model η mode
  have hdomain' : (TypeExpr.var (.flex s.nextType) : Ty).realize ζ = some domain :=
    (hb.realize (by simp [TypeExpr.Bounded, TypeVar.index, InferenceState.freshType])).trans hd
  have hmodeValue : ζ.modes (.flex s.nextMode) = mode := Option.some.inj hmode'
  have hagree : SolverGround.AgreesBelow ζ ρ s.nextType s.nextMode :=
    (hb.mono (by simp [InferenceState.freshType]) (by simp [InferenceState.freshType])).trans ha
  let next : InferenceState := {s with nextType := s.nextType + 1, nextMode := s.nextMode + 1}
  let bodyContext : AlgorithmicContext :=
    .binding (some (.mono (.var (.flex s.nextType)))) :: .lock (.var (.flex s.nextMode)) :: A
  have hready : GenerationReady bodyContext next := by
    refine ⟨?_, ?_, ?_, hs.constraintsBounded.mono (by simp [next]) (by simp [next]),
      hs.constraintsFlexible⟩
    · have hbound := hs.contextBounded.mono (Nat.le_succ _) (Nat.le_succ _)
      simpa [bodyContext, next, ContextEntry.Bounded, Scheme.Bounded, Scheme.mono,
        TypeExpr.Bounded, ModExpr.Bounded, TypeVar.index, ModVar.index] using hbound
    · simpa [bodyContext, ContextEntry.Flexible, Scheme.Flexible, Scheme.mono,
        TypeExpr.Flexible, ModExpr.Flexible] using hs.contextFlexible
    · simpa [bodyContext, next, Scheme.ModParamsBounded, Scheme.mono] using
        hs.parametersBounded.mono (Nat.le_succ s.nextMode)
  have hcontext : AlgorithmicContextCovers ζ τ bodyContext
      (some (Scheme.mono a) :: captured) t.freeVars := by
    have hc' : AlgorithmicContextCovers ζ τ A Γ (t.freeVars 1) :=
      hc.source_agreesBelow hs.contextBounded hagree
    exact (hc'.lock hs.parametersBounded hΔ hl hmodeValue hmode).binding
      (SchemeCovers.mono hdomain' hdomain .refl)
      (fun i hi => (t.mem_freeVars_add 0 1 i).mpr hi)
  obtain ⟨fuel, r, ξ, ground, hr, hmodel, hξ, hreal, hsub⟩ :=
    ih bodyContext next ζ τ codomain hready hΔ hcontext
      (hagree.models hs.constraintsBounded hm) hcodomain
  have hdomain'' : (TypeExpr.var (.flex s.nextType) : Ty).realize ξ = some domain :=
    (hξ.realize (by simp [next, TypeExpr.Bounded, TypeVar.index])).trans hdomain'
  have hmode'' : (.var (.flex s.nextMode) : ModExpr).eval (some ∘ ξ.modes) = some mode :=
    (hξ.eval (by simp [next, ModExpr.Bounded, ModVar.index])).trans hmode'
  refine ⟨fuel + 1,
    ⟨.modal (.fn (.var (.flex s.nextType)) r.type) (.var (.flex s.nextMode)),
      .lam () r.term,
      r.state⟩, ξ, .fn domain ground mode, ?_, hmodel,
    (hξ.mono (by simp [next]) (by simp [next])).trans hagree, ?_, ?_⟩
  · change generate (fuel + 1) A (.lam () t.erase) s = _
    simp only [bodyContext, next] at hr
    simp [generate, InferenceState.freshType, InferenceState.freshMode, hr,
      bind, pure, RunResult.bind]
  · have hdvalue : ξ.types (.flex s.nextType) = domain := Option.some.inj hdomain''
    simp [TypeExpr.realize, hdvalue, hreal, hmode'', GroundTy.modal,
      Mode.identity_compose]
  · simpa only [GroundTy.modal, Mode.identity_compose] using
      (GroundOrder.fn (GroundOrder.refl domain) (GroundOrder.of_subtype hsub)
        (fun h => h) (fun h => h)).to_subtype

end ModalityInference
