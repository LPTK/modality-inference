import ModalityInference.Proofs.GenerationCompletenessBase

/-! Ground completeness for variables, constants, and declarative subsumption. -/
namespace ModalityInference

theorem GroundTypingComplete.var {Δ Γ i scheme σ}
    (hl : Γ[i]? = some (some scheme)) (hi : Instantiates scheme σ)
    (hb : EntailsAll Δ (σ.bounds scheme.bounds)) :
    GroundTypingComplete Δ Γ (.var i) (σ.ty scheme.body) := by
  intro A s ρ τ b hs hΔ hctx hm ht
  obtain ⟨source, hlookup, hcover⟩ := hctx i (by simp [Term.freeVars]) scheme hl
  obtain ⟨η, a, hη, ha, hab⟩ := hcover (σ.ground τ) b
    (hi.ground (hb.groundModels hΔ)) (scheme.body.realize_ground ht)
  obtain ⟨ζ, hζ, hmodel, hagree⟩ := InferenceState.instantiate_model
    hs.constraintsBounded hm (lookupScheme_bounded hs.contextBounded hlookup.lookupScheme) hη ha
  refine ⟨1, ⟨(s.instantiate source).1, .var i, (s.instantiate source).2⟩,
    ζ, a, ?_, hmodel, hagree, hζ, hab⟩
  simp [generate, Term.erase, Term.mapAnnotation, hlookup.lookupScheme, bind, pure, RunResult.bind]

theorem GroundTypingComplete.unit {Δ Γ m} :
    GroundTypingComplete Δ Γ .unit (.modal .unit m) := by
  intro A s ρ τ b hs hΔ hctx hm ht
  simp only [TypeExpr.realize, bind, pure, Option.bind_some,
    Option.bind_eq_some_iff] at ht
  obtain ⟨n, hn, he⟩ := ht
  cases he
  refine ⟨1, ⟨.modal .unit .bottom, .unit, s⟩, ρ, .unit Mode.bottom,
    rfl, hm, SolverGround.AgreesBelow.refl _ _ _, ?_, ?_⟩
  · simp [TypeExpr.realize, ModExpr.bottom, ModExpr.eval, GroundTy.modal,
      Mode.identity_compose]
  · apply GroundOrder.to_subtype
    simp only [GroundTy.modal, Mode.identity_compose]
    exact .unit (by simp [Mode.le, Mode.bottom])

theorem GroundTypingComplete.subs {Δ Γ Γ' t a b}
    (ih : GroundTypingComplete Δ Γ t a)
    (hctx : ContextLe Δ Γ' Γ) (hab : Subtype Δ a b) :
    GroundTypingComplete Δ Γ' t b := by
  intro A s ρ τ target hs hΔ hc hm hb
  obtain ⟨source, ha⟩ := Option.isSome_iff_exists.mp
    ((hab.realize_defined hΔ).trans (by rw [hb]; rfl))
  exact (ih A s ρ τ source hs hΔ (hc.trans (hctx.ground_covers hΔ)) hm ha).weaken
    (hab.ground hΔ ha hb)

end ModalityInference
