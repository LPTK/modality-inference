import ModalityInference.Proofs.ComparisonPartialRootProjection
import ModalityInference.Proofs.ComparisonPartialPublicContext

namespace ModalityInference.ComparisonPartialStructuredCapsule

open ComparisonStructuralProjection

noncomputable section
attribute [local instance] Classical.propDecidable

 theorem frozen_observe_cancel {Δ : Bounds} {a b : CompareTy} {m : ModExpr}
    (ha : ComparisonPartialCapsule.observe Δ (.modal a m) = {(a, m)})
    (hb : ComparisonPartialCapsule.observe Δ (.modal b m) = {(b, m)})
    (h : ComparisonPartialCapsule.observe Δ (.modal a m) ⊆
      ComparisonPartialCapsule.observe Δ (.modal b m)) : a = b := by
  have he := h (show (a, m) ∈ ComparisonPartialCapsule.observe Δ (.modal a m) by rw [ha]; rfl)
  rw [hb] at he
  exact congrArg Prod.fst he

/-- A genuinely partial common action retains its entire literal operand,
even when that action contains compound syntax and total outer factors. -/
 theorem partial_observe_cancel {Δ : Bounds} {a b : CompareTy} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m))
    (h : ComparisonPartialCapsule.observe Δ (.modal a m) ⊆
      ComparisonPartialCapsule.observe Δ (.modal b m)) : a = b := by
  induction m generalizing a b with
  | compose m n ihm ihn =>
    rw [ComparisonPartialCapsule.observe_compose, ComparisonPartialCapsule.observe_compose] at h
    by_cases hn : Entails Δ (.defined n)
    · rw [ComparisonPartialCapsule.observe_modal_total hn,
        ComparisonPartialCapsule.observe_modal_total hn] at h
      exact ihm (fun h => hm (Entails.defined_compose_iff.mpr ⟨h, hn⟩)) h
    · exact (CompareTy.modal.inj (ihn hn h)).1
  | _ =>
    apply frozen_observe_cancel (h := h)
    all_goals rw [ComparisonPartialCapsule.observe]
    all_goals simp [ComparisonPartialCapsule.not_epsilon_of_partial hm, hm]

 theorem rootType_partial_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : CompareTy} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal a m) (.modal b m))
    {kind : Nat} (hk : kind ≠ 0) (hf : kind ≠ 5) (ha : rootTag a.shape = kind) :
    rootType kind a = rootType kind b := by
  apply partial_observe_cancel hm
  apply ComparisonPartialCapsule.algebra_sound hΔ (residual_unitShapes hR)
    (algebra_rootType hR h hk ha)
  change ComparisonPartialCapsule.Atomic ((rootType kind a).shape.subst unitShapes)
  rw [rootType_shape]
  simp only [rootBase, if_neg hf, CompareTy.shape, ComparisonShape.subst, ComparisonPartialCapsule.Atomic]

 theorem observe_public_nonpair {Δ : Bounds} (a : Ty) (suffix : Suffix)
    (hn : ¬suffix.total Δ) (hp : rootTag (CompareTy.ofTy a).shape ≠ 3)
    (hs : rootTag (CompareTy.ofTy a).shape ≠ 4) :
    observe Δ (.ofTy a) suffix = literal Δ (.ofTy a) suffix := by
  induction a generalizing suffix with
  | var v | unit | credit => rfl
  | prod a b ia ib => exact (hp rfl).elim
  | sum a b ia ib => exact (hs rfl).elim
  | fn a b ia ib => exact if_neg hn
  | modal a m ih =>
    change observe Δ (.ofTy a) (suffix.prepend m) = literal Δ (.modal (.ofTy a) m) suffix
    rw [ih (suffix.prepend m) (fun h => hn ((Suffix.total_prepend Δ suffix m).mp h).2) hp hs]
    unfold literal
    rw [Suffix.observe_prepend]

 theorem nonpair_public_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : Ty} {m : ModExpr}
    (hp : rootTag (CompareTy.ofTy a).shape ≠ 3) (hs : rootTag (CompareTy.ofTy a).shape ≠ 4)
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal (.ofTy a) m) (.modal (.ofTy b) m)) :
    CompareTy.ofTy a = CompareTy.ofTy b := by
  have ht := rootTag_equivalent hR h.shape_equivalent
  apply partial_observe_cancel hm
  intro token he
  have hl : ([], token) ∈ (observe Δ (.modal (.ofTy a) m) none).positive := by
    change ([], token) ∈ (observe Δ (.ofTy a) (some m)).positive
    rw [observe_public_nonpair a (some m) hm hp hs]
    exact ⟨token, he, rfl⟩
  have hr := (algebra_sound hΔ h).1 hl
  change ([], token) ∈ (observe Δ (.ofTy b) (some m)).positive at hr
  rw [observe_public_nonpair b (some m) hm
    (fun hh => hp (ht.trans hh)) (fun hh => hs (ht.trans hh))] at hr
  obtain ⟨other, ho, heq⟩ := hr
  have heq' : other = token := congrArg Prod.snd heq
  exact heq' ▸ ho

private theorem ofTy_eq_iff (a b : Ty) : CompareTy.ofTy a = CompareTy.ofTy b ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp_all [CompareTy.ofTy]

 theorem modal_public_cancel_of_root {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : Ty} {n m : ModExpr}
    (ih : ∀ (b : Ty) (m : ModExpr), ¬Entails Δ (.defined m) →
      AlgebraSubtype Δ (.modal (.ofTy a) m) (.modal (.ofTy b) m) → a = b)
    {kind : Nat} (hk : kind ≠ 0) (hf : kind ≠ 5) (ha : rootTag (CompareTy.ofTy a).shape = kind)
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal (.ofTy (.modal a n)) m) (.modal (.ofTy b) m)) :
    TypeExpr.modal a n = b := by
  have hr := rootType_partial_cancel hΔ hR hm h hk hf ha
  cases b with
  | modal b p =>
    have hn : n = p := (CompareTy.modal.inj hr).2
    subst p
    have hc : AlgebraSubtype Δ (.modal (.ofTy a) (.compose n m))
        (.modal (.ofTy b) (.compose n m)) :=
      (AlgebraSubtype.shaped (.composeRev (CompareTy.wellShaped_ofTy a Δ))).trans
        (h.trans (.shaped (.compose (CompareTy.wellShaped_ofTy b Δ))))
    have he := ih b (.compose n m) (fun hd => hm (Entails.defined_compose_iff.mp hd).2) hc
    exact congrArg (fun t => TypeExpr.modal t n) he
  | _ => simp [CompareTy.ofTy, rootType, rootBase, hf] at hr

/-- A genuinely partial shared action freezes a public context literally.
Structural child and root projections synchronize the complete context. -/
 theorem public_partial_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : Ty} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal (.ofTy a) m) (.modal (.ofTy b) m)) : a = b := by
  induction a generalizing b m with
  | var v | unit | credit | fn a c ia ic =>
    exact (ofTy_eq_iff _ _).mp (nonpair_public_cancel hΔ hR
      (by simp [CompareTy.ofTy, CompareTy.shape, rootTag])
      (by simp [CompareTy.ofTy, CompareTy.shape, rootTag]) hm h)
  | modal a n ih =>
    by_cases hp : rootTag (CompareTy.ofTy a).shape = 3
    · exact modal_public_cancel_of_root hΔ hR (fun b m hm h => ih hm h)
        (by decide : 3 ≠ 0) (by decide : 3 ≠ 5) hp hm h
    · by_cases hs : rootTag (CompareTy.ofTy a).shape = 4
      · exact modal_public_cancel_of_root hΔ hR (fun b m hm h => ih hm h)
          (by decide : 4 ≠ 0) (by decide : 4 ≠ 5) hs hm h
      · exact (ofTy_eq_iff _ _).mp (nonpair_public_cancel hΔ hR hp hs hm h)
  | prod a c ia ic =>
    have hr := rootType_partial_cancel hΔ hR hm h
      (by decide : 3 ≠ 0) (by decide : 3 ≠ 5) rfl
    have ht := rootTag_equivalent hR h.shape_equivalent
    cases b with
    | prod b d =>
      have hl := algebra_pairChild hR h (PairRoot.modal (.prod (.ofTy a) (.ofTy c))) false
      have hh := algebra_pairChild hR h (PairRoot.modal (.prod (.ofTy a) (.ofTy c))) true
      exact congrArg₂ TypeExpr.prod (ia hm hl) (ic hm hh)
    | _ => simp [CompareTy.ofTy, CompareTy.shape, rootTag, rootType, rootBase] at hr ht
  | sum a c ia ic =>
    have hr := rootType_partial_cancel hΔ hR hm h
      (by decide : 4 ≠ 0) (by decide : 4 ≠ 5) rfl
    have ht := rootTag_equivalent hR h.shape_equivalent
    cases b with
    | sum b d =>
      have hl := algebra_pairChild hR h (PairRoot.modal (.sum (.ofTy a) (.ofTy c))) false
      have hh := algebra_pairChild hR h (PairRoot.modal (.sum (.ofTy a) (.ofTy c))) true
      exact congrArg₂ TypeExpr.sum (ia hm hl) (ic hm hh)
    | _ => simp [CompareTy.ofTy, CompareTy.shape, rootTag, rootType, rootBase] at hr ht

/-- A frozen public boundary determines the entire internal context. This is
an exact reconstruction criterion, with no publicness premise on the image. -/
 theorem partial_public_context_iff {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a : CompareTy} {b : Ty} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) :
    AlgebraSubtype Δ (.modal a m) (.modal (.ofTy b) m) ↔ a = .ofTy b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := partial_context_public_below (a := a) (b := .modal b m) hΔ hm h
    have he := public_partial_cancel hΔ hR hm (hc.symm ▸ h)
    exact hc.symm.trans (congrArg CompareTy.ofTy he)
  · intro h
    rw [h]
    exact .refl (CompareTy.wellShaped_ofTy b Δ)

 theorem public_partial_context_iff {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a : Ty} {b : CompareTy} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) :
    AlgebraSubtype Δ (.modal (.ofTy a) m) (.modal b m) ↔ b = .ofTy a := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := partial_context_public_above (a := .modal a m) (b := b) hΔ hm h
    have he := public_partial_cancel hΔ hR hm (hc.symm ▸ h)
    exact hc.symm.trans (congrArg CompareTy.ofTy he.symm)
  · intro h
    rw [h]
    exact .refl (CompareTy.wellShaped_ofTy a Δ)

end
end ModalityInference.ComparisonPartialStructuredCapsule
