import ModalityInference.Proofs.TypingDefinedness

/-! Ground realization preserves declarative subtyping. Constraint entailment
then preserves all modeled bounds, including type constraints and definedness. -/
namespace ModalityInference

theorem GroundTy.reify_modal_left (a : GroundTy) (m : Mode) (Δ : Bounds) :
    Subtype Δ (a.modal m).reify (.modal a.reify (.const m)) := by
  cases a <;> exact .trans (.congr .refl (.valid fun _ _ =>
    ⟨_, _, rfl, rfl, by simp [Mode.le]⟩)) .composeRev

theorem GroundTy.reify_modal_right (a : GroundTy) (m : Mode) (Δ : Bounds) :
    Subtype Δ (.modal a.reify (.const m)) (a.modal m).reify := by
  cases a <;> exact .trans .compose (.congr .refl (.valid fun _ _ =>
    ⟨_, _, rfl, rfl, by simp [Mode.le]⟩))

theorem Subtype.ground_modal {Δ} {a b : GroundTy} {m n : Mode}
    (h : Subtype Δ a.reify b.reify) (hmn : m.le n = true) :
    Subtype Δ (a.modal m).reify (b.modal n).reify :=
  (a.reify_modal_left m Δ).trans
    ((Subtype.congr h (.valid fun _ _ => ⟨m, n, rfl, rfl, hmn⟩)).trans
      (b.reify_modal_right n Δ))

private def OptSubtype : Option GroundTy → Option GroundTy → Prop
  | none, none => True
  | some a, some b => Subtype [] a.reify b.reify
  | _, _ => False

private theorem OptSubtype.refl (a : Option GroundTy) : OptSubtype a a :=
  match a with
  | none => trivial
  | some _ => Subtype.refl

private theorem OptSubtype.trans {a b c} (hab : OptSubtype a b) (hbc : OptSubtype b c) :
    OptSubtype a c := by
  cases a <;> cases b <;> cases c <;> simp only [OptSubtype] at *
  exact hab.trans hbc

private theorem Subtype.optGround {ρ Δ a b} (h : Subtype Δ a b)
    (hΔ : GroundModels ρ Δ) : OptSubtype (a.realize ρ) (b.realize ρ) := by
  induction h
  case fn a b c d m n _ _ hmode iha ihb =>
    have hmn := hmode.denote hΔ.modeModels
    cases hm : m.eval (some ∘ ρ.modes) <;> cases hn : n.eval (some ∘ ρ.modes) <;>
      simp [ModExpr.Below, ModExpr.eval, ModExpr.top, hm, hn] at hmn
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      simp_all [OptSubtype, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    exact .fn iha ihb (.valid fun _ _ => ⟨_, _, rfl, rfl, hmn⟩)
  case prod a b c d m _ _ iha ihb | sum a b c d m _ _ iha ihb =>
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      cases hm : m.eval (some ∘ ρ.modes) <;>
      simp_all [OptSubtype, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    all_goals
      rename_i x y z r p
      have hfields := And.intro
        ((x.reify_modal_right p []).trans (iha.trans (z.reify_modal_left p [])))
        ((y.reify_modal_right p []).trans (ihb.trans (r.reify_modal_left p [])))
      first | exact .prod hfields.1 hfields.2 | exact .sum hfields.1 hfields.2
  case congr a b m n _ hmode ih =>
    obtain ⟨u, v, hm, hn, huv⟩ := hmode.denote hΔ.modeModels
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      simp_all [OptSubtype, TypeExpr.realize]
    exact ih.ground_modal huv
  case bound a b hc =>
    obtain ⟨x, y, hx, hy, hs⟩ := hΔ (.sub a b) hc
    simpa only [hx, hy] using hs
  all_goals try simp only [TypeExpr.realize_identity, TypeExpr.realize_compose]
  all_goals solve_by_elim [OptSubtype.refl, OptSubtype.trans]

theorem Subtype.ground {ρ Δ a b x y} (h : Subtype Δ a b)
    (hΔ : GroundModels ρ Δ) (ha : a.realize ρ = some x) (hb : b.realize ρ = some y) :
    Subtype [] x.reify y.reify := by
  simpa only [ha, hb] using h.optGround hΔ

theorem Entails.groundSatisfies {ρ Δ c} (h : Entails Δ c) (hΔ : GroundModels ρ Δ) :
    GroundSatisfies ρ c := by
  cases c
  case equiv a b =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := And.intro
      (Option.isSome_iff_exists.mp (h.2.2.1.realize_defined hΔ))
      (Option.isSome_iff_exists.mp (h.2.2.2.realize_defined hΔ))
    exact ⟨x, y, hx, hy, h.1.ground hΔ hx hy, h.2.1.ground hΔ hy hx⟩
  case sub a b =>
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := And.intro
      (Option.isSome_iff_exists.mp (h.2.1.realize_defined hΔ))
      (Option.isSome_iff_exists.mp (h.2.2.realize_defined hΔ))
    exact ⟨x, y, hx, hy, h.1.ground hΔ hx hy⟩
  case equal v a =>
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (h.2.2.realize_defined hΔ)
    exact ⟨x, hx, h.1.ground hΔ rfl hx, h.2.1.ground hΔ hx rfl⟩
  all_goals first | exact h.denote hΔ.modeModels | exact h ρ.modes hΔ.modeModels

theorem EntailsAll.groundModels {ρ Δ cs} (h : EntailsAll Δ cs) (hΔ : GroundModels ρ Δ) :
    GroundModels ρ cs := fun c hc => (h c hc).groundSatisfies hΔ

end ModalityInference
