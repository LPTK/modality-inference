import ModalityInference.ComparisonAlgebra
import ModalityInference.Proofs.ComparisonShapes
import ModalityInference.Proofs.ComparisonLattice

namespace ModalityInference

open ComparisonLattice

theorem TypeExpr.realize_comparisonShape {ρ : GroundAssignment} {a : Ty} {x : GroundTy}
    (h : a.realize ρ = some x) :
    (observe x).shape = (ComparisonShape.ofTy a).subst (fun v => (observe (ρ.types v)).shape) := by
  simpa only [CompareTy.shape_ofTy] using
    CompareTy.realize_shape (a := CompareTy.ofTy a) (by simpa only [CompareTy.realize_ofTy] using h)

theorem GroundModels.comparisonShapes {ρ : GroundAssignment} {Δ : Bounds}
    (h : GroundModels ρ Δ) :
    ComparisonShape.Models Δ (fun v => (observe (ρ.types v)).shape) := by
  intro p hp
  obtain ⟨c, hc, hp⟩ := List.mem_flatMap.mp hp
  cases c <;> simp only [List.mem_singleton, List.not_mem_nil] at hp
  all_goals subst p
  case sub a b =>
    obtain ⟨x, y, hx, hy, hs⟩ := h (.sub a b) hc
    exact (TypeExpr.realize_comparisonShape hx).symm.trans
      ((observe_le_of_groundOrder (GroundOrder.of_subtype hs)).shape.trans (TypeExpr.realize_comparisonShape hy))
  case equiv a b =>
    obtain ⟨x, y, hx, hy, hs, _⟩ := h (.equiv a b) hc
    exact (TypeExpr.realize_comparisonShape hx).symm.trans
      ((observe_le_of_groundOrder (GroundOrder.of_subtype hs)).shape.trans (TypeExpr.realize_comparisonShape hy))
  case equal v a =>
    obtain ⟨y, hy, hs, _⟩ := h (.equal v a) hc
    exact (observe_le_of_groundOrder (GroundOrder.of_subtype hs)).shape.trans (TypeExpr.realize_comparisonShape hy)

theorem CompareTy.realize_defined_of_modes {Δ : Bounds} {ρ : GroundAssignment} {a : CompareTy}
    (hs : a.WellShaped Δ)
    (hshape : ComparisonShape.Models Δ (fun v => (observe (ρ.types v)).shape))
    (hm : ModeModels a.wellFormedBounds ρ.modes) : ∃ x, a.realize ρ = some x := by
  induction a <;> simp only [CompareTy.WellShaped] at hs
  all_goals simp only [CompareTy.wellFormedBounds, ModeModels, List.mem_append, or_imp,
    forall_and, List.mem_singleton, forall_eq, ModeSatisfies] at hm
  case join a b iha ihb | meet a b iha ihb =>
    obtain ⟨x, hx⟩ := iha hs.1 hm.1
    obtain ⟨y, hy⟩ := ihb hs.2.1 hm.2
    have hxy := (CompareTy.realize_shape hx).trans
      ((hs.2.2 _ hshape).trans (CompareTy.realize_shape hy).symm)
    first
      | simpa only [CompareTy.realize, hx, hy, bind, Option.bind_some] using
          (groundBlend_exists_iff true x y).mpr hxy
      | simpa only [CompareTy.realize, hx, hy, bind, Option.bind_some] using
          (groundBlend_exists_iff false x y).mpr hxy
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    obtain ⟨x, hx⟩ := iha hs.1 hm.1
    obtain ⟨y, hy⟩ := ihb hs.2 hm.2
    simp only [CompareTy.realize, hx, hy, bind, pure, Option.bind_some,
      Option.some.injEq, exists_eq']
  case modal a m ih =>
    obtain ⟨x, hx⟩ := ih hs hm.1
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hm.2
    exact ⟨x.modal n, by simp only [CompareTy.realize, hx, hn, bind, pure, Option.bind_some]⟩
  all_goals exact ⟨_, rfl⟩

theorem CompareTy.DefinedUnder.realize_defined {Δ : Bounds} {ρ : GroundAssignment} {a : CompareTy}
    (h : a.DefinedUnder Δ) (hs : a.WellShaped Δ) (hΔ : GroundModels ρ Δ) :
    ∃ x, a.realize ρ = some x :=
  CompareTy.realize_defined_of_modes hs hΔ.comparisonShapes (h ρ.modes hΔ.modeModels)

theorem ComparisonLattice.observe_clip_identity (a : GroundTy) :
    (observe a).clip Mode.identity = observe a := by
  simpa only [GroundTy.modal_identity] using (observe_modal a Mode.identity).symm

theorem ComparisonLattice.groundBlend_prod {p : Bool} {a b c d ac bd : GroundTy}
    (hac : groundBlend p a c = some ac) (hbd : groundBlend p b d = some bd) :
    ∃ v, groundBlend p (.prod a b Mode.identity) (.prod c d Mode.identity) = some v ∧
      v.Equivalent (.prod ac bd Mode.identity) := by
  have hp : Profile.blend p (observe (.prod a b Mode.identity))
      (observe (.prod c d Mode.identity)) = some (.prod (observe ac) (observe bd) Mode.identity) := by
    simp only [observe, observe_clip_identity, Profile.blend, groundBlend_observe hac,
      groundBlend_observe hbd, Profile.blendMode_self, bind, pure, Option.bind_some]
  refine ⟨(Profile.prod (observe ac) (observe bd) Mode.identity).realize, ?_, ?_⟩
  · simp only [groundBlend, hp, Option.map_some]
  · apply (equivalent_iff_observe_eq _ _).mpr
    rw [observe_realize (Profile.blend_valid (observe_valid _) (observe_valid _) hp)]
    simp only [observe, observe_clip_identity]

theorem ComparisonLattice.groundBlend_sum {p : Bool} {a b c d ac bd : GroundTy}
    (hac : groundBlend p a c = some ac) (hbd : groundBlend p b d = some bd) :
    ∃ v, groundBlend p (.sum a b Mode.identity) (.sum c d Mode.identity) = some v ∧
      v.Equivalent (.sum ac bd Mode.identity) := by
  have hp : Profile.blend p (observe (.sum a b Mode.identity))
      (observe (.sum c d Mode.identity)) = some (.sum (observe ac) (observe bd) Mode.identity) := by
    simp only [observe, observe_clip_identity, Profile.blend, groundBlend_observe hac,
      groundBlend_observe hbd, Profile.blendMode_self, bind, pure, Option.bind_some]
  refine ⟨(Profile.sum (observe ac) (observe bd) Mode.identity).realize, ?_, ?_⟩
  · simp only [groundBlend, hp, Option.map_some]
  · apply (equivalent_iff_observe_eq _ _).mpr
    rw [observe_realize (Profile.blend_valid (observe_valid _) (observe_valid _) hp)]
    simp only [observe, observe_clip_identity]

theorem ComparisonLattice.groundBlend_fn {p : Bool} {a b c d ac bd : GroundTy}
    (hac : groundBlend (!p) a c = some ac) (hbd : groundBlend p b d = some bd) :
    ∃ v, groundBlend p (.fn a b Mode.identity) (.fn c d Mode.identity) = some v ∧
      v.Equivalent (.fn ac bd Mode.identity) := by
  have hp : Profile.blend p (observe (.fn a b Mode.identity))
      (observe (.fn c d Mode.identity)) = some (.fn (observe ac) (observe bd) (Mode.identity.compose Mode.top)) := by
    simp only [observe, Profile.blend, groundBlend_observe hac,
      groundBlend_observe hbd, Profile.blendMode_self, bind, pure, Option.bind_some]
  refine ⟨(Profile.fn (observe ac) (observe bd) (Mode.identity.compose Mode.top)).realize, ?_, ?_⟩
  · simp only [groundBlend, hp, Option.map_some]
  · apply (equivalent_iff_observe_eq _ _).mpr
    rw [observe_realize (Profile.blend_valid (observe_valid _) (observe_valid _) hp)]
    simp only [observe]

namespace ComparisonAlgebra

theorem Compatible.realize {Δ ρ a b} (h : Compatible Δ a b) (hΔ : GroundModels ρ Δ) :
    ∃ x y, a.realize ρ = some x ∧ b.realize ρ = some y ∧ (observe x).shape = (observe y).shape := by
  obtain ⟨x, hx⟩ := h.2.1.realize_defined h.1.1 hΔ
  obtain ⟨y, hy⟩ := h.2.2.realize_defined h.1.2.1 hΔ
  exact ⟨x, y, hx, hy, (CompareTy.realize_shape hx).trans
    ((h.1.2.2 _ hΔ.comparisonShapes).trans (CompareTy.realize_shape hy).symm)⟩

theorem realize_typeOp (p : Bool) (ρ : GroundAssignment) (a b : CompareTy) :
    (typeOp p a b).realize ρ = (do groundBlend p (← a.realize ρ) (← b.realize ρ)) := by
  cases p <;> rfl

theorem eval_modeOp {ρ : ModVar → Option Mode} {m n : ModExpr} {x y : Mode}
    (hm : m.eval ρ = some x) (hn : n.eval ρ = some y) (p : Bool) :
    (modeOp p m n).eval ρ = some (Profile.blendMode p x y) := by
  cases p <;> simp only [modeOp, Profile.blendMode, Bool.false_eq_true, if_false, if_true,
    ModExpr.eval, hm, hn, bind, pure, Option.bind_some]

theorem Equation.ground {Δ : Bounds} {ρ : GroundAssignment} {a b : CompareTy}
    (h : Equation Δ a b) (hΔ : GroundModels ρ Δ) :
    ∃ x y, a.realize ρ = some x ∧ b.realize ρ = some y ∧ x.Equivalent y := by
  cases h
  case modal a b m p hab hm =>
    obtain ⟨x, y, hx, hy, hxy⟩ := hab.realize hΔ
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hm _ hΔ.modeModels)
    obtain ⟨z, hz⟩ := (groundBlend_exists_iff p x y).mpr hxy
    obtain ⟨v, hv, heq⟩ := groundBlend_modal hz u
    refine ⟨z.modal u, v, ?_, ?_, heq.symm⟩
    all_goals simp only [CompareTy.realize, realize_typeOp, hx, hy, hu, hz, hv,
      bind, pure, Option.bind_some]
  case distrib a b c p hab hac =>
    obtain ⟨x, y, hx, hy, hxy⟩ := hab.realize hΔ
    obtain ⟨x', z, hx', hz, hxz⟩ := hac.realize hΔ
    have heq : x' = x := Option.some.inj (hx'.symm.trans hx)
    subst x'
    obtain ⟨bc, hbc⟩ := (groundBlend_exists_iff (!p) y z).mpr (hxy.symm.trans hxz)
    obtain ⟨ab, hab⟩ := (groundBlend_exists_iff p x y).mpr hxy
    obtain ⟨ac, hac⟩ := (groundBlend_exists_iff p x z).mpr hxz
    obtain ⟨l, hl⟩ := (groundBlend_exists_iff p x bc).mpr
      (hxy.trans (Profile.blend_shape (groundBlend_observe hbc)).symm)
    obtain ⟨r, hr⟩ := (groundBlend_exists_iff (!p) ab ac).mpr
      ((Profile.blend_shape (groundBlend_observe hab)).trans
        (Profile.blend_shape (groundBlend_observe hac)).symm)
    refine ⟨l, r, ?_, ?_, groundBlend_distrib hbc hab hac hl hr⟩
    all_goals simp only [realize_typeOp, hx, hy, hz, hbc, hab, hac, hl, hr,
      bind, Option.bind_some]
  case scalar a m n p hs hd hm hn =>
    obtain ⟨x, hx⟩ := hd.realize_defined hs hΔ
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hm _ hΔ.modeModels)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hn _ hΔ.modeModels)
    obtain ⟨z, hz, heq⟩ := groundBlend_mode (p := p) x u v
    refine ⟨x.modal (Profile.blendMode p u v), z, ?_, ?_, heq.symm⟩
    all_goals simp only [CompareTy.realize, realize_typeOp, hx, hu, hv, hz,
      eval_modeOp hu hv p, bind, pure, Option.bind_some]
  case prod a b c d p hac hbd =>
    obtain ⟨x, z, hx, hz, hxz⟩ := hac.realize hΔ
    obtain ⟨y, w, hy, hw, hyw⟩ := hbd.realize hΔ
    obtain ⟨ac, hac⟩ := (groundBlend_exists_iff p x z).mpr hxz
    obtain ⟨bd, hbd⟩ := (groundBlend_exists_iff p y w).mpr hyw
    obtain ⟨v, hv, heq⟩ := groundBlend_prod hac hbd
    refine ⟨v, .prod ac bd Mode.identity, ?_, ?_, heq⟩
    all_goals simp only [CompareTy.realize, realize_typeOp, hx, hy, hz, hw, hac, hbd, hv,
      bind, pure, Option.bind_some]
  case sum a b c d p hac hbd =>
    obtain ⟨x, z, hx, hz, hxz⟩ := hac.realize hΔ
    obtain ⟨y, w, hy, hw, hyw⟩ := hbd.realize hΔ
    obtain ⟨ac, hac⟩ := (groundBlend_exists_iff p x z).mpr hxz
    obtain ⟨bd, hbd⟩ := (groundBlend_exists_iff p y w).mpr hyw
    obtain ⟨v, hv, heq⟩ := groundBlend_sum hac hbd
    refine ⟨v, .sum ac bd Mode.identity, ?_, ?_, heq⟩
    all_goals simp only [CompareTy.realize, realize_typeOp, hx, hy, hz, hw, hac, hbd, hv,
      bind, pure, Option.bind_some]
  case fn a b c d p hac hbd =>
    obtain ⟨x, z, hx, hz, hxz⟩ := hac.realize hΔ
    obtain ⟨y, w, hy, hw, hyw⟩ := hbd.realize hΔ
    obtain ⟨ac, hac⟩ := (groundBlend_exists_iff (!p) x z).mpr hxz
    obtain ⟨bd, hbd⟩ := (groundBlend_exists_iff p y w).mpr hyw
    obtain ⟨v, hv, heq⟩ := groundBlend_fn hac hbd
    refine ⟨v, .fn ac bd Mode.identity, ?_, ?_, heq⟩
    all_goals simp only [CompareTy.realize, realize_typeOp, hx, hy, hz, hw, hac, hbd, hv,
      bind, pure, Option.bind_some]

theorem shape_typeOp (p : Bool) (a b : CompareTy) : (typeOp p a b).shape = a.shape := by
  cases p <;> rfl

theorem typeOp_wellShaped (p : Bool) (Δ : Bounds) (a b : CompareTy) :
    (typeOp p a b).WellShaped Δ ↔
      a.WellShaped Δ ∧ b.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape b.shape := by
  cases p <;> rfl

theorem Equation.shape_eq {Δ : Bounds} {a b : CompareTy} (h : Equation Δ a b) :
    a.shape = b.shape := by
  cases h <;> simp only [shape_typeOp, CompareTy.shape]

theorem Equation.wellShaped {Δ : Bounds} {a b : CompareTy} (h : Equation Δ a b) :
    a.WellShaped Δ ∧ b.WellShaped Δ := by
  cases h
  case distrib a b c p hab hac =>
    simp only [typeOp_wellShaped, shape_typeOp]
    exact ⟨⟨hab.1.1, ⟨hab.1.2.1, hac.1.2.1, hab.1.2.2.symm.trans hac.1.2.2⟩, hab.1.2.2⟩,
      ⟨hab.1, hac.1, ComparisonShape.Equivalent.refl⟩⟩
  case modal a b m p hab hm =>
    simpa only [CompareTy.WellShaped, typeOp_wellShaped, CompareTy.shape] using And.intro hab.1 hab.1
  case scalar a m n p hs _ _ _ =>
    exact ⟨hs, (typeOp_wellShaped p Δ _ _).mpr ⟨hs, hs, ComparisonShape.Equivalent.refl⟩⟩
  case prod a b c d p hac hbd | sum a b c d p hac hbd | fn a b c d p hac hbd =>
    simp only [typeOp_wellShaped, CompareTy.WellShaped, CompareTy.shape]
    refine ⟨⟨⟨hac.1.1, hbd.1.1⟩, ⟨hac.1.2.1, hbd.1.2.1⟩, ?_⟩, hac.1, hbd.1⟩
    intro ρ hρ
    simp only [ComparisonShape.subst, hac.1.2.2 ρ hρ, hbd.1.2.2 ρ hρ]

/-- Clamping is justified by the ground bounds supplied by the surrounding
subtyping derivation; every displayed realization is the original partial one. -/
theorem clamp_ground {ρ : GroundAssignment} {b a t : CompareTy} {m : ModExpr}
    {x y z : GroundTy} {u : Mode}
    (hb : b.realize ρ = some x) (ha : a.realize ρ = some y) (ht : t.realize ρ = some z)
    (hm : m.eval (some ∘ ρ.modes) = some u) (hba : GroundOrder x y) (hat : GroundOrder y z) :
    ∃ v, (CompareTy.meet (.join a (.modal b m)) (.modal t m)).realize ρ = some v ∧
      v.Equivalent (y.modal u) := by
  obtain ⟨j, hj⟩ := (groundBlend_exists_iff true y (x.modal u)).mpr
    (by simpa only [observe_modal, Profile.shape_clip] using (observe_le_of_groundOrder hba).shape.symm)
  obtain ⟨v, hv, heq⟩ := groundBlend_clamp hba hat u hj
  exact ⟨v, by simp only [CompareTy.realize, hb, ha, ht, hm, hj, hv,
    bind, pure, Option.bind_some], heq⟩

end ComparisonAlgebra

theorem AlgebraSubtype.shape_invariant {Δ a b} (h : AlgebraSubtype Δ a b) :
    a.WellShaped Δ ∧ b.WellShaped Δ ∧ ComparisonShape.Equivalent Δ a.shape b.shape := by
  induction h
  case shaped h => exact h.shape_invariant
  case equation h => exact ⟨h.wellShaped.1, h.wellShaped.2, fun _ _ => congrArg _ h.shape_eq⟩
  case equationRev h => exact ⟨h.wellShaped.2, h.wellShaped.1, fun _ _ => congrArg _ h.shape_eq.symm⟩
  all_goals simp_all [ComparisonAlgebra.Compatible, CompareTy.WellShaped, CompareTy.shape,
    ComparisonShape.Equivalent, ComparisonShape.subst]

theorem AlgebraSubtype.wellShaped_left {Δ a b} (h : AlgebraSubtype Δ a b) :
    a.WellShaped Δ := h.shape_invariant.1

theorem AlgebraSubtype.wellShaped_right {Δ a b} (h : AlgebraSubtype Δ a b) :
    b.WellShaped Δ := h.shape_invariant.2.1

theorem AlgebraSubtype.shape_equivalent {Δ a b} (h : AlgebraSubtype Δ a b) :
    ComparisonShape.Equivalent Δ a.shape b.shape := h.shape_invariant.2.2

theorem AlgebraSubtype.refl {Δ a} (h : a.WellShaped Δ) : AlgebraSubtype Δ a a :=
  .shaped (.refl h)

theorem AlgebraSubtype.no_unit_credit_upper {Δ a} {ρ : TypeVar → ComparisonShape}
    (hρ : ComparisonShape.Models Δ ρ) (hu : AlgebraSubtype Δ .unit a)
    (hc : AlgebraSubtype Δ .credit a) : False := by
  have h := (hu.shape_equivalent ρ hρ).trans (hc.shape_equivalent ρ hρ).symm
  cases h

theorem ShapedEntails.to_algebra {Δ c} (h : ShapedEntails Δ c) : AlgebraEntails Δ c := by
  cases c <;> simp only [ShapedEntails, AlgebraEntails] at *
  all_goals first
    | exact h
    | exact ⟨.shaped h.1, h.2⟩
    | exact ⟨.shaped h.1, .shaped h.2.1, h.2.2⟩

theorem ShapedEntailsAll.to_algebra {Δ cs} (h : ShapedEntailsAll Δ cs) :
    AlgebraEntailsAll Δ cs := fun c hc => (h c hc).to_algebra

theorem ShapedSubsumes.to_algebra {Δ source target} (h : ShapedSubsumes Δ source target) :
    AlgebraSubsumes Δ source target :=
  match h with | ⟨σ, hσ, hs, hb, ht⟩ => ⟨σ, hσ, hs, hb.to_algebra, .shaped ht⟩

theorem Subsumes.to_algebra {Δ source target} (h : Subsumes Δ source target) :
    AlgebraSubsumes Δ source target := h.to_shaped.to_algebra

end ModalityInference
