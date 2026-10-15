import ModalityInference.Proofs.ComparisonPartialCancellation

namespace ModalityInference.ComparisonPartialStructuredCapsule

open ComparisonStructuralProjection

noncomputable section
attribute [local instance] Classical.propDecidable

theorem suffix_rootType_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : CompareTy} {m q r : ModExpr}
    (hm : ¬Entails Δ (.defined m))
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal a m) q) (.modal (.modal b m) r))
    {kind : Nat} (hk : kind ≠ 0) (hf : kind ≠ 5) (ha : rootTag a.shape = kind) :
    rootType kind a = rootType kind b := by
  apply partial_observe_cancel hm
  have hh := ComparisonPartialCapsule.algebra_sound hΔ (residual_unitShapes hR)
    (algebra_rootType hR h hk ha)
    (show ComparisonPartialCapsule.Atomic
      ((rootType kind (.modal (.modal a m) q)).shape.subst unitShapes) from by
      rw [rootType_shape]
      simp only [rootBase, if_neg hf, CompareTy.shape, ComparisonShape.subst,
        ComparisonPartialCapsule.Atomic])
  simpa only [rootType, ComparisonPartialCapsule.observe_modal_total hq,
    ComparisonPartialCapsule.observe_modal_total hr] using hh

theorem suffix_nonpair_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : Ty} {m q r : ModExpr}
    (hp : rootTag (CompareTy.ofTy a).shape ≠ 3) (hs : rootTag (CompareTy.ofTy a).shape ≠ 4)
    (hm : ¬Entails Δ (.defined m))
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal (.ofTy a) m) q)
      (.modal (.modal (.ofTy b) m) r)) : CompareTy.ofTy a = CompareTy.ofTy b := by
  have ht := rootTag_equivalent hR h.shape_equivalent
  have hh := algebra_sound hΔ h
  rw [observe_modal_total hq, observe_modal_total hr] at hh
  apply partial_observe_cancel hm
  intro token he
  have hl : ([], token) ∈ (observe Δ (.modal (.ofTy a) m) none).positive := by
    change ([], token) ∈ (observe Δ (.ofTy a) (some m)).positive
    rw [observe_public_nonpair a (some m) hm hp hs]
    exact ⟨token, he, rfl⟩
  have hb := hh.1 hl
  change ([], token) ∈ (observe Δ (.ofTy b) (some m)).positive at hb
  rw [observe_public_nonpair b (some m) hm
    (fun hh => hp (ht.trans hh)) (fun hh => hs (ht.trans hh))] at hb
  obtain ⟨other, ho, heq⟩ := hb
  have heq' : other = token := congrArg Prod.snd heq
  exact heq' ▸ ho

private theorem ofTy_eq_iff (a b : Ty) : CompareTy.ofTy a = CompareTy.ofTy b ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp_all [CompareTy.ofTy]

theorem suffix_modal_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) (hR : Residual Δ)
    {a b : Ty} {n m q r : ModExpr}
    (ih : ∀ (b : Ty) (m : ModExpr), ¬Entails Δ (.defined m) →
      AlgebraSubtype Δ (.modal (.modal (.ofTy a) m) q) (.modal (.modal (.ofTy b) m) r) → a = b)
    {kind : Nat} (hk : kind ≠ 0) (hf : kind ≠ 5) (ha : rootTag (CompareTy.ofTy a).shape = kind)
    (hm : ¬Entails Δ (.defined m))
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal (.ofTy (.modal a n)) m) q)
      (.modal (.modal (.ofTy b) m) r)) : TypeExpr.modal a n = b := by
  have hroot := suffix_rootType_cancel hΔ hR hm hq hr h hk hf ha
  cases b with
  | modal b p =>
    have hn : n = p := (CompareTy.modal.inj hroot).2
    subst p
    have hc : AlgebraSubtype Δ (.modal (.modal (.ofTy a) (.compose n m)) q)
        (.modal (.modal (.ofTy b) (.compose n m)) r) :=
      (AlgebraSubtype.congr (.shaped (.composeRev (CompareTy.wellShaped_ofTy a Δ)))
        (.refl hq)).trans
        (h.trans (.congr (.shaped (.compose (CompareTy.wellShaped_ofTy b Δ))) (.refl hr)))
    exact congrArg (fun t => TypeExpr.modal t n)
      (ih b (.compose n m) (fun hd => hm (Entails.defined_compose_iff.mp hd).2) hc)
  | _ => simp [CompareTy.ofTy, rootType, rootBase, hf] at hroot

/-- Different total suffixes may change the scalar comparison, but they do not
change the exact operand retained beneath a common partial action. -/
theorem public_partial_suffix_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : Ty} {m q r : ModExpr}
    (hm : ¬Entails Δ (.defined m))
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal (.ofTy a) m) q)
      (.modal (.modal (.ofTy b) m) r)) : a = b := by
  induction a generalizing b m with
  | var v | unit | credit | fn a c ia ic =>
    exact (ofTy_eq_iff _ _).mp (suffix_nonpair_cancel hΔ hR
      (by simp [CompareTy.ofTy, CompareTy.shape, rootTag])
      (by simp [CompareTy.ofTy, CompareTy.shape, rootTag]) hm hq hr h)
  | modal a n ih =>
    by_cases hp : rootTag (CompareTy.ofTy a).shape = 3
    · exact suffix_modal_cancel hΔ hR (fun b m hm h => ih hm h)
        (by decide : 3 ≠ 0) (by decide : 3 ≠ 5) hp hm hq hr h
    · by_cases hs : rootTag (CompareTy.ofTy a).shape = 4
      · exact suffix_modal_cancel hΔ hR (fun b m hm h => ih hm h)
          (by decide : 4 ≠ 0) (by decide : 4 ≠ 5) hs hm hq hr h
      · exact (ofTy_eq_iff _ _).mp (suffix_nonpair_cancel hΔ hR hp hs hm hq hr h)
  | prod a c ia ic =>
    have hroot := suffix_rootType_cancel hΔ hR hm hq hr h
      (by decide : 3 ≠ 0) (by decide : 3 ≠ 5) rfl
    have ht := rootTag_equivalent hR h.shape_equivalent
    cases b with
    | prod b d =>
      have hl := algebra_pairChild hR h (PairRoot.modal (.modal (.prod (.ofTy a) (.ofTy c)))) false
      have hh := algebra_pairChild hR h (PairRoot.modal (.modal (.prod (.ofTy a) (.ofTy c)))) true
      exact congrArg₂ TypeExpr.prod (ia hm hl) (ic hm hh)
    | _ => simp [CompareTy.ofTy, CompareTy.shape, rootTag, rootType, rootBase] at hroot ht
  | sum a c ia ic =>
    have hroot := suffix_rootType_cancel hΔ hR hm hq hr h
      (by decide : 4 ≠ 0) (by decide : 4 ≠ 5) rfl
    have ht := rootTag_equivalent hR h.shape_equivalent
    cases b with
    | sum b d =>
      have hl := algebra_pairChild hR h (PairRoot.modal (.modal (.sum (.ofTy a) (.ofTy c)))) false
      have hh := algebra_pairChild hR h (PairRoot.modal (.modal (.sum (.ofTy a) (.ofTy c)))) true
      exact congrArg₂ TypeExpr.sum (ia hm hl) (ic hm hh)
    | _ => simp [CompareTy.ofTy, CompareTy.shape, rootTag, rootType, rootBase] at hroot ht

def Noncompose (m : ModExpr) : Prop := ∀ a b, m ≠ .compose a b

theorem noncompose_observe {Δ : Bounds} {m : ModExpr} (hc : Noncompose m)
    (hm : ¬Entails Δ (.defined m)) (a : CompareTy) :
    ComparisonPartialCapsule.observe Δ (.modal a m) = {(a, m)} := by
  cases m
  case compose m n => exact (hc m n rfl).elim
  all_goals rw [ComparisonPartialCapsule.observe]
  all_goals simp [ComparisonPartialCapsule.not_epsilon_of_partial hm, hm]

theorem root_frozen_suffix_mode_eq {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : CompareTy} {m n q r : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (hn : ¬Entails Δ (.defined n))
    (hmc : Noncompose m) (hnc : Noncompose n)
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal a m) q) (.modal (.modal b n) r))
    {kind : Nat} (hk : kind ≠ 0) (hf : kind ≠ 5) (ha : rootTag a.shape = kind) : m = n := by
  have hh := ComparisonPartialCapsule.algebra_sound hΔ (residual_unitShapes hR)
    (algebra_rootType hR h hk ha)
    (show ComparisonPartialCapsule.Atomic
      ((rootType kind (.modal (.modal a m) q)).shape.subst unitShapes) from by
      rw [rootType_shape]
      simp only [rootBase, if_neg hf, CompareTy.shape, ComparisonShape.subst,
        ComparisonPartialCapsule.Atomic])
  simp only [rootType, ComparisonPartialCapsule.observe_modal_total hq,
    ComparisonPartialCapsule.observe_modal_total hr, noncompose_observe hmc hm,
    noncompose_observe hnc hn] at hh
  exact congrArg Prod.snd (hh (Set.mem_singleton _))

theorem nonpair_frozen_suffix_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : Ty} {m n q r : ModExpr}
    (hp : rootTag (CompareTy.ofTy a).shape ≠ 3) (hs : rootTag (CompareTy.ofTy a).shape ≠ 4)
    (hm : ¬Entails Δ (.defined m)) (hn : ¬Entails Δ (.defined n))
    (hmc : Noncompose m) (hnc : Noncompose n)
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal (.ofTy a) m) q)
      (.modal (.modal (.ofTy b) n) r)) : a = b ∧ m = n := by
  have ht := rootTag_equivalent hR h.shape_equivalent
  have hh := algebra_sound hΔ h
  rw [observe_modal_total hq, observe_modal_total hr] at hh
  have hl : ([], (.ofTy a, m)) ∈ (observe Δ (.modal (.ofTy a) m) none).positive := by
    change ([], (.ofTy a, m)) ∈ (observe Δ (.ofTy a) (some m)).positive
    rw [observe_public_nonpair a (some m) hm hp hs]
    exact ⟨_, by change (_, _) ∈ ComparisonPartialCapsule.observe Δ (.modal (.ofTy a) m)
                 rw [noncompose_observe hmc hm]; rfl, rfl⟩
  have hb := hh.1 hl
  change ([], (.ofTy a, m)) ∈ (observe Δ (.ofTy b) (some n)).positive at hb
  rw [observe_public_nonpair b (some n) hn
    (fun hh => hp (ht.trans hh)) (fun hh => hs (ht.trans hh))] at hb
  obtain ⟨other, ho, heq⟩ := hb
  have heq' : other = (.ofTy a, m) := congrArg Prod.snd heq
  change other ∈ ComparisonPartialCapsule.observe Δ (.modal (.ofTy b) n) at ho
  rw [heq', noncompose_observe hnc hn] at ho
  have he : (CompareTy.ofTy a, m) = (.ofTy b, n) := ho
  exact ⟨(ofTy_eq_iff a b).mp (congrArg Prod.fst he), congrArg Prod.snd he⟩

/-- The two exposed frozen stems must match literally. Their total suffixes
remain scalar obligations, so no syntactic choice is made per valuation. -/
theorem public_frozen_stem_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a b : Ty} {m n q r : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (hn : ¬Entails Δ (.defined n))
    (hmc : Noncompose m) (hnc : Noncompose n)
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal (.ofTy a) m) q)
      (.modal (.modal (.ofTy b) n) r)) : a = b ∧ m = n := by
  have equalMode {kind : Nat} (hk : kind ≠ 0) (hf : kind ≠ 5)
      (ha : rootTag (CompareTy.ofTy a).shape = kind) : a = b ∧ m = n := by
    have he := root_frozen_suffix_mode_eq hΔ hR hm hn hmc hnc hq hr h hk hf ha
    subst n
    exact ⟨public_partial_suffix_cancel hΔ hR hm hq hr h, rfl⟩
  by_cases hp : rootTag (CompareTy.ofTy a).shape = 3
  · exact equalMode (by decide) (by decide) hp
  · by_cases hs : rootTag (CompareTy.ofTy a).shape = 4
    · exact equalMode (by decide) (by decide) hs
    · exact nonpair_frozen_suffix_cancel hΔ hR hp hs hm hn hmc hnc hq hr h

theorem internal_frozen_stem_cancel {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (hR : Residual Δ) {a : CompareTy} {b : Ty} {m n q r : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (hn : ¬Entails Δ (.defined n))
    (hmc : Noncompose m) (hnc : Noncompose n)
    (hq : Entails Δ (.defined q)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal a m) q) (.modal (.modal (.ofTy b) n) r)) :
    a = .ofTy b ∧ m = n := by
  have hpartial : ¬Entails Δ (.defined (.compose m q)) :=
    fun hc => hm (Entails.defined_compose_iff.mp hc).1
  have hp : Public a := partial_context_public_below (b := .modal (.modal b n) r) hΔ hpartial
    ((AlgebraSubtype.shaped (.composeRev (a := a) (m := m) (n := q)
      h.wellShaped_left)).trans h)
  obtain ⟨c, rfl⟩ := hp
  obtain ⟨rfl, he⟩ := public_frozen_stem_cancel hΔ hR hm hn hmc hnc hq hr h
  exact ⟨rfl, he⟩

end
end ModalityInference.ComparisonPartialStructuredCapsule
