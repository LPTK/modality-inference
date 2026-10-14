import ModalityInference.Proofs.GenerationEventualCovers
import ModalityInference.Proofs.GroundOrder
import ModalityInference.Proofs.GenerationContexts

/-! Ground instances survive the guards attached to symbolic sharing and locks. -/
namespace ModalityInference

theorem GroundOrder.modal_guard_downward {a b : GroundTy} {m : Mode}
    (hab : GroundOrder a b) (hbb : GroundOrder b (b.modal m)) (hm : m.unique = true) :
    GroundOrder a (a.modal m) := by
  induction hab generalizing m
  case unit p q hpq =>
    cases hbb with
    | unit hq =>
      apply GroundOrder.unit
      simp only [Mode.le_iff, Mode.compose] at hpq hq ⊢
      grind
  case credit p q hpq =>
    cases hbb with
    | credit hq =>
      apply GroundOrder.credit
      simp only [Mode.le_iff, Mode.compose, Mode.many] at hpq hq ⊢
      grind
  case prod a b c d p q hpq hac hbd iha ihb =>
    cases hbb with
    | prod hq hc hd =>
      refine .prod ?_ ?_ ?_
      · simp only [Mode.le_iff, Mode.compose] at hpq hq ⊢
        grind
      · simpa only [GroundTy.modal_compose] using
          iha (by simpa only [GroundTy.modal_compose] using hc) hm
      · simpa only [GroundTy.modal_compose] using
          ihb (by simpa only [GroundTy.modal_compose] using hd) hm
  case sum a b c d p q hpq hac hbd iha ihb =>
    cases hbb with
    | sum hq hc hd =>
      refine .sum ?_ ?_ ?_
      · simp only [Mode.le_iff, Mode.compose] at hpq hq ⊢
        grind
      · simpa only [GroundTy.modal_compose] using
          iha (by simpa only [GroundTy.modal_compose] using hc) hm
      · simpa only [GroundTy.modal_compose] using
          ihb (by simpa only [GroundTy.modal_compose] using hd) hm
  case fn a b c d p q hca hbd hl ho iha ihb =>
    cases hbb with
    | fn _ _ hl' ho' =>
      refine .fn (.refl _) (.refl _) ?_ ?_
      · simp only [Mode.compose] at hl' ⊢
        grind
      · simp only [Mode.compose] at ho' ⊢
        grind

theorem SchemeCovers.share {ρ τ Δ source target}
    (h : SchemeCovers ρ τ source (target.modal (.const Mode.many)))
    (hΔ : GroundModels τ Δ) (hf : target.FreshForBounds Δ)
    (halias : Subtype (Δ ++ target.bounds)
      (.modal target.body (.const Mode.aliased)) target.body) :
    SchemeCovers ρ τ source.share target := by
  intro η b hη hb
  obtain ⟨ζ, a, hζ, ha, hab⟩ := h η (b.modal Mode.many) hη
    (by simp [Scheme.modal, TypeExpr.realize, hb, ModExpr.eval])
  have hguard : GroundOrder a (a.modal Mode.many) :=
    (GroundOrder.of_subtype hab).modal_guard_downward
      (by simpa only [GroundTy.modal_compose, Mode.compose_self] using
        GroundOrder.refl (b.modal Mode.many)) rfl
  have hbounds : GroundModels η (Δ ++ target.bounds) := fun c hc =>
    (List.mem_append.mp hc).elim (hη.models_fresh hf hΔ c) (hη.2.2 c)
  have htarget : Subtype [] (b.modal Mode.aliased).reify b.reify :=
    halias.ground hbounds (by simp [TypeExpr.realize, hb, ModExpr.eval]) hb
  refine ⟨ζ, a.modal Mode.aliased, ?_, ?_, ?_⟩
  · refine ⟨hζ.1, hζ.2.1, ?_⟩
    simpa [Scheme.share, GroundModels, GroundSatisfies, TypeExpr.realize, ha,
      ModExpr.eval, or_imp, forall_and] using And.intro hζ.2.2 hguard.to_subtype
  · simp [Scheme.share, TypeExpr.realize, ha, ModExpr.eval]
  · apply (hab.ground_modal (Mode.le_refl Mode.aliased)).trans
    apply Subtype.trans ?_ htarget
    simpa only [GroundTy.modal_compose] using
      (Subtype.refl (a := b.reify)).ground_modal
        (m := Mode.many.compose Mode.aliased) (n := Mode.aliased) (by decide)

theorem SchemeCovers.lock {ρ τ Δ source target p m n}
    (h : SchemeCovers ρ τ source target) (hΔ : GroundModels τ Δ)
    (hfb : target.FreshForBounds Δ) (hfm : target.FreshForMode m)
    (hfp : source.FreshForMode p)
    (hp : p.eval (some ∘ ρ.modes) = some n)
    (hm : m.eval (some ∘ τ.modes) = some n)
    (hfuture : Subtype (Δ ++ target.bounds) target.body (.modal target.body (.future m))) :
    SchemeCovers ρ τ (source.lock p) (target.modal (.capture m)) := by
  intro η ground hη ht
  have hmη := (show GroundInstantiates τ target η from hη).eval_fresh hfm |>.trans hm
  cases hb : target.body.realize η <;>
    simp [Scheme.modal, TypeExpr.realize, ModExpr.eval, hb, hmη] at ht
  rename_i b
  subst ground
  obtain ⟨ζ, a, hζ, ha, hab⟩ := h η b hη hb
  have hpζ := hζ.eval_fresh hfp |>.trans hp
  have hbounds : GroundModels η (Δ ++ target.bounds) := fun c hc =>
    (List.mem_append.mp hc).elim
      ((show GroundInstantiates τ target η from hη).models_fresh hfb hΔ c) (hη.2.2 c)
  have hbguard : Subtype [] b.reify (b.modal n.future).reify :=
    hfuture.ground hbounds hb (by simp [TypeExpr.realize, hb, ModExpr.eval, hmη])
  have hguard := (GroundOrder.of_subtype hab).modal_guard_downward
    (GroundOrder.of_subtype hbguard) rfl
  refine ⟨ζ, a.modal n.capture, ?_, ?_, hab.ground_modal (Mode.le_refl _)⟩
  · refine ⟨hζ.1, hζ.2.1, ?_⟩
    simpa [Scheme.lock, GroundModels, GroundSatisfies, TypeExpr.realize, ha,
      ModExpr.eval, hpζ, or_imp, forall_and] using And.intro hζ.2.2 hguard.to_subtype
  · simp [Scheme.lock, TypeExpr.realize, ha, ModExpr.eval, hpζ]

end ModalityInference
