import ModalityInference.Proofs.Reduction
import ModalityInference.Proofs.Normalization

/-! Local reductions reconstruct declarative entailment of their inputs. -/
namespace ModalityInference

theorem ModExpr.below_leftResidual {η a b c} :
    ModExpr.Below η (.leftResidual a b) c ↔ ModExpr.Below η a (.compose b c) := by
  cases ha : a.eval (some ∘ η) <;> cases hb : b.eval (some ∘ η) <;>
    cases hc : c.eval (some ∘ η) <;>
    simp [ModExpr.Below, ModExpr.eval, ha, hb, hc, Mode.leftResidual_le_iff]

theorem ModExpr.below_rightResidual {η a b c} :
    ModExpr.Below η a (.rightResidual b c) ↔ ModExpr.Below η (.compose a b) c := by
  cases ha : a.eval (some ∘ η) <;> cases hb : b.eval (some ∘ η) <;>
    cases hc : c.eval (some ∘ η) <;>
    simp [ModExpr.Below, ModExpr.eval, ha, hb, hc, Mode.le_rightResidual_iff]

theorem ModExpr.eval_compose_comm (a b : ModExpr) (η : ModVar → Option Mode) :
    (.compose a b : ModExpr).eval η = (.compose b a : ModExpr).eval η := by
  cases ha : a.eval η <;> cases hb : b.eval η <;>
    simp [ModExpr.eval, ha, hb, Mode.compose_comm]

theorem ConstraintReduction.modeModels_backward {cs ds η} (h : ConstraintReduction cs ds)
    (hs : ModeModels ds η) : ModeModels cs η := by
  have hg : ∀ ρ, GroundModels ρ cs ↔ GroundModels ρ ds := fun _ => h.groundModels
  induction h
  case context xs ys before after h ih =>
    simp only [ModeModels, List.mem_append, or_imp, forall_and] at hs ⊢
    exact ⟨⟨hs.1.1, ih hs.1.2 (fun _ => h.groundModels)⟩, hs.2⟩
  all_goals try solve | simp [ModeModels, ModeSatisfies]
  all_goals
    simpa [ModeModels, ModeSatisfies, GroundModels, GroundSatisfies] using
      ((hg ⟨fun _ => .unit Mode.identity, η⟩).mpr
        (by simpa [ModeModels, ModeSatisfies, GroundModels, GroundSatisfies] using hs))

theorem Submode.refl {Δ m} (hm : Entails Δ (.defined m)) : Submode Δ m m :=
  .valid fun η hη =>
    let ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
    ⟨x, x, hx, hx, Mode.le_refl x⟩

theorem Submode.defined {Δ m n} (h : Submode Δ m n) :
    Entails Δ (.defined m) ∧ Entails Δ (.defined n) :=
  ⟨fun _ hη => let ⟨x, _, hx, _, _⟩ := h.denote hη
    Option.isSome_iff_exists.mpr ⟨x, hx⟩,
   fun _ hη => let ⟨_, y, _, hy, _⟩ := h.denote hη
    Option.isSome_iff_exists.mpr ⟨y, hy⟩⟩

theorem Submode.compose_between {Δ m n} (h : Submode Δ m n) :
    Submode Δ m (.compose m n) ∧ Submode Δ (.compose m n) n := by
  refine ⟨.valid (fun η hη => ?_), .valid (fun η hη => ?_)⟩
  all_goals obtain ⟨x, y, hx, hy, hxy⟩ := h.denote hη
  · simpa [ModExpr.Below, ModExpr.eval, hx, hy] using Mode.compose_le_left x hxy
  · simpa [ModExpr.Below, ModExpr.eval, hx, hy] using Mode.compose_le_right y hxy

theorem Subtype.modal_intersection {Δ a b m n}
    (h : Subtype Δ (.modal a m) (.modal b n)) (hmn : Submode Δ m n) :
    Subtype Δ (.modal a (.compose m n)) (.modal b (.compose m n)) := by
  refine (Subtype.congr (.refl (a := a)) (n := .compose m (.compose m n)) ?_).trans
    (Subtype.composeRev.trans ((Subtype.congr h (m := .compose m n) (n := .compose m n) ?_).trans
      (Subtype.compose.trans (.congr .refl ?_))))
  all_goals apply Submode.valid
  all_goals intro η hη
  all_goals obtain ⟨x, y, hx, hy, _⟩ := hmn.denote hη
  all_goals simp [ModExpr.Below, ModExpr.eval, hx, hy]

theorem ConstraintReduction.entails_backward {cs ds Δ} (h : ConstraintReduction cs ds)
    (hs : EntailsAll Δ ds) : EntailsAll Δ cs := by
  have hm : ∀ η, ModeModels ds η → ModeModels cs η := fun _ => h.modeModels_backward
  induction h
  case pair a b c d l r | sum a b c d l r =>
    simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Entails, TypeExpr.definedUnder_modal, TypeExpr.definedUnder_prod,
      TypeExpr.definedUnder_sum] at hs ⊢
    refine ⟨?_, ⟨⟨hs.1.2.1.1, hs.2.1.2.1.1⟩, hs.1.2.1.2⟩,
      ⟨hs.1.2.2.1, hs.2.1.2.2.1⟩, hs.1.2.2.2⟩
    first
    | exact (Subtype.congr .refl hs.2.2.compose_between.1).trans
        ((Subtype.prod (hs.1.1.modal_intersection hs.2.2)
          (hs.2.1.1.modal_intersection hs.2.2)).trans
            (.congr .refl hs.2.2.compose_between.2))
    | exact (Subtype.congr .refl hs.2.2.compose_between.1).trans
        ((Subtype.sum (hs.1.1.modal_intersection hs.2.2)
          (hs.2.1.1.modal_intersection hs.2.2)).trans
            (.congr .refl hs.2.2.compose_between.2))
  case fn a b c d l r =>
    simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Entails, TypeExpr.definedUnder_modal,
      TypeExpr.definedUnder_fn] at hs ⊢
    refine ⟨.fn hs.1.1 hs.2.1.1 hs.2.2,
      ⟨⟨hs.1.2.2, hs.2.1.2.1⟩, hs.2.2.defined.1⟩,
      ⟨hs.1.2.1, hs.2.1.2.2⟩, ?_⟩
    exact fun η hη => Option.isSome_of_isSome_bind (hs.2.2.defined.2 η hη)
  case unit l r | credit l r =>
    simp [EntailsAll, Entails, TypeExpr.DefinedUnder,
      TypeExpr.wellFormedBounds, ModeModels, ModeSatisfies] at hs ⊢
    first
    | exact ⟨.congr .refl hs, hs.defined⟩
    | exact ⟨.credit hs, fun η hη => Option.isSome_of_isSome_bind (hs.defined.1 η hη),
        hs.defined.2⟩
  case context xs ys before after h ih =>
    simp only [EntailsAll, List.mem_append, or_imp, forall_and] at hs ⊢
    exact ⟨⟨hs.1.1, ih hs.1.2 (fun _ => h.modeModels_backward)⟩, hs.2⟩
  all_goals simp only [EntailsAll, List.mem_singleton, forall_eq, Entails]
  all_goals exact .valid fun η hη => hm η (hs.modeModels hη) (.mode _ _) (by simp)

end ModalityInference
