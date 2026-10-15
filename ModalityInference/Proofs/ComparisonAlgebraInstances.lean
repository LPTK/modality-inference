import ModalityInference.Proofs.ComparisonAlgebraSoundness
import ModalityInference.Proofs.SourceInference

/-! Semantic signature comparison for inferred and typed source schemes.
Completed internal witnesses supply ordinary instances of the public scheme;
typing supplies the definedness of its original body. -/
namespace ModalityInference

theorem ModExpr.complete_subst (m : ModExpr) (σ : ModVar → ModExpr)
    (ρ : ModVar → Mode) :
    (m.subst σ).complete ρ = m.complete (fun v => (σ v).complete ρ) := by
  induction m <;> simp_all [ModExpr.subst, ModExpr.complete]

theorem TypeExpr.complete_compareGround (a : Ty) (σ : CompareSubstitution)
    (ρ : GroundAssignment) :
    (σ.ty a).complete ρ = (CompareTy.ofTy a).complete (σ.ground ρ) := by
  induction a <;> simp_all [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
    CompareTy.complete, CompareSubstitution.ground, ModExpr.complete_subst]

/-- Once the original source body realizes at the completed source assignment,
the internal derivation compares that very public ground type with the target. -/
theorem AlgebraSubtype.ground_instance {Δ : Bounds} {ρ : GroundAssignment}
    {σ : CompareSubstitution} {a b : Ty} {x y : GroundTy}
    (h : AlgebraSubtype Δ (σ.ty a) (CompareTy.ofTy b)) (hΔ : GroundModels ρ Δ)
    (ha : a.realize (σ.ground ρ) = some x) (hb : b.realize ρ = some y) :
    GroundOrder x y := by
  have hs := h.complete hΔ
  rw [a.complete_compareGround] at hs
  simpa only [CompareTy.complete_of_realize (by simpa using ha :
    (CompareTy.ofTy a).realize (σ.ground ρ) = some x),
    CompareTy.complete_of_realize (by simpa using hb :
      (CompareTy.ofTy b).realize ρ = some y)] using hs

theorem AlgebraSubsumes.ground_covers_typed {ρ : GroundAssignment} {Δ : Bounds}
    {source target : Scheme} {Γ : Context} {term : RawTerm}
    (h : AlgebraSubsumes Δ source target)
    (ht : SourceTyping source.bounds Γ term source.body)
    (hΔ : GroundModels ρ Δ) : SchemeCovers ρ ρ source target := by
  intro η ground hη htarget
  obtain ⟨θ, hb, he, hft, hfm⟩ := hη.skolemize (s := source) hΔ
  have hb := hb.assumptions_right
  obtain ⟨σ, hσ, _, hcs, hab⟩ := h
  have hi := hσ.ground (hcs.groundModels hb)
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (ht.realize_defined hi.2.2)
  obtain ⟨hreb, hbody⟩ := hi.rebase hft hfm
  exact ⟨source.rebase ρ (σ.ground θ), x, hreb, hbody.trans hx,
    (hab.ground_instance hb hx (he.trans htarget)).to_subtype⟩

theorem GroundOrder.resourceLe {a b : GroundTy} (h : GroundOrder a b) : ResourceLe a b := by
  let ρ : GroundAssignment := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩
  exact h.to_subtype.resourceLe (ρ := ρ) (by simp [GroundModels])
    (GroundTy.realize_reify ρ a) (GroundTy.realize_reify ρ b)

theorem SchemeCovers.resource_semantic {ρ w source target v reserved}
    (h : SchemeCovers ρ ρ source target)
    (hv : ResourceSchemeInterpretation ρ w source v reserved) :
    ResourceSchemeInterpretation ρ w target v reserved := by
  refine ⟨hv.1, ?_⟩
  intro η b hη hb
  obtain ⟨ζ, a, hζ, ha, hab⟩ := h η b hη hb
  obtain ⟨owned, ho, hr⟩ := hv.2 ζ a hζ ha
  obtain ⟨target, htarget, ht⟩ :=
    (GroundOrder.of_subtype hab).resourceLe w Mode.identity v owned hr
  exact ⟨target, htarget.trans ho, ht⟩

/-- Signature comparison preserves each instance's ownership evidence for any
source scheme justified by a source typing derivation. -/
theorem AlgebraSubsumes.resource_semantic_typed
    {ρ w Δ source target v reserved Γ term}
    (h : AlgebraSubsumes Δ source target)
    (ht : SourceTyping source.bounds Γ term source.body)
    (hΔ : GroundModels ρ Δ)
    (hv : ResourceSchemeInterpretation ρ w source v reserved) :
    ResourceSchemeInterpretation ρ w target v reserved :=
  (h.ground_covers_typed ht hΔ).resource_semantic hv

theorem inference_scheme_bounds {fuel Γ t result}
    (h : infer fuel Γ t = .success result) : result.scheme.bounds = result.residual := by
  simp only [infer, bind, pure, RunResult.bind] at h
  repeat' (split at h <;> try contradiction)
  cases h
  rfl

theorem inference_comparison_ground_covers {fuel Γ t result Δ target ρ}
    (hi : infer fuel Γ t = .success result)
    (hc : AlgebraSubsumes Δ result.scheme target) (hΔ : GroundModels ρ Δ) :
    SchemeCovers ρ ρ result.scheme target :=
  hc.ground_covers_typed (by
    simpa only [inference_scheme_bounds hi] using (inference_source_sound hi).2) hΔ

/-- Inference followed by algebraic signature comparison preserves the full
interpretation of the public scheme, including its per-instance resources. -/
theorem inference_comparison_resource_semantic {fuel Γ t result Δ target ρ w v reserved}
    (hi : infer fuel Γ t = .success result)
    (hc : AlgebraSubsumes Δ result.scheme target) (hΔ : GroundModels ρ Δ)
    (hv : Runtime.ResourceSchemeInterpretation ρ w result.scheme v reserved) :
    Runtime.ResourceSchemeInterpretation ρ w target v reserved :=
  (inference_comparison_ground_covers hi hc hΔ).resource_semantic hv

/-- A closed inferred program executes safely at every admissible instance of
its declared signature; selected result ownership comes only from fresh cells. -/
theorem inference_comparison_source_semantic
    {fuel t result Δ target ρ η w ground}
    (hi : infer fuel [] t = .success result)
    (hc : AlgebraSubsumes Δ result.scheme target) (hΔ : GroundModels ρ Δ)
    (hη : GroundInstantiates ρ target η) (ht : target.body.realize η = some ground) :
    Runtime.ResourceSemanticEvaluation w [] result.elaborated ground ∅ := by
  obtain ⟨ζ, a, hζ, ha, hab⟩ := inference_comparison_ground_covers hi hc hΔ η ground hη ht
  have hb : GroundModels ζ result.residual := (inference_scheme_bounds hi) ▸ hζ.2.2
  have he := inference_source_semantic (Γ := []) (γ := []) (w := w)
    (reserved := fun _ => ∅) hi hb
    (ResourceEnvironmentInterpretation.nil (reserved := fun _ => ∅)) ha
  intro supplies hs
  obtain ⟨v, owned, hv, hr, ho⟩ := he supplies hs
  obtain ⟨selected, hselected, htarget⟩ :=
    (GroundOrder.of_subtype hab).resourceLe w Mode.identity v.annotate owned hr
  refine ⟨v, selected, hv, htarget, ?_⟩
  simpa [ContextResources] using hselected.trans ho

end ModalityInference
