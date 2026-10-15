import ModalityInference.Proofs.ComparisonAlgebra
import ModalityInference.Proofs.GroundInstantiation

/-! Ground soundness of the internal comparison algebra. A compositional total
completion of partial annotations interprets intermediate lattice expressions;
it agrees with the original partial interpretation whenever that is defined. -/
namespace ModalityInference

open ComparisonLattice

namespace ModExpr

def complete (ρ : ModVar → Mode) : ModExpr → Mode
  | .const m => m
  | .var v => ρ v
  | .compose a b => (a.complete ρ).compose (b.complete ρ)
  | .meet a b => (a.complete ρ).meet (b.complete ρ)
  | .join a b => (a.complete ρ).join (b.complete ρ)
  | .leftResidual a b => ((a.complete ρ).leftResidual (b.complete ρ)).getD Mode.identity
  | .rightResidual a b => ((a.complete ρ).rightResidual (b.complete ρ)).getD Mode.identity
  | .close a => (a.complete ρ).close
  | .closeInv a => (a.complete ρ).closeInv
  | .future a => (a.complete ρ).future
  | .capture a => (a.complete ρ).capture

theorem complete_of_eval {ρ : ModVar → Mode} {m : ModExpr} {n : Mode}
    (h : m.eval (some ∘ ρ) = some n) : m.complete ρ = n := by
  induction m generalizing n <;>
    simp only [eval, bind, pure, Option.bind_eq_some_iff, Option.some.injEq,
      Function.comp_apply] at h
  all_goals
    first
    | exact h
    | (rcases h with ⟨x, hx, y, hy, h⟩; simp_all [complete])

end ModExpr

namespace CompareTy

def complete (ρ : GroundAssignment) : CompareTy → GroundTy
  | .var v => ρ.types v
  | .unit => .unit Mode.identity
  | .credit => .credit Mode.identity
  | .prod a b => .prod (a.complete ρ) (b.complete ρ) Mode.identity
  | .sum a b => .sum (a.complete ρ) (b.complete ρ) Mode.identity
  | .fn a b => .fn (a.complete ρ) (b.complete ρ) Mode.identity
  | .modal a m => (a.complete ρ).modal (m.complete ρ.modes)
  | .join a b => (groundBlend true (a.complete ρ) (b.complete ρ)).getD (a.complete ρ)
  | .meet a b => (groundBlend false (a.complete ρ) (b.complete ρ)).getD (a.complete ρ)

theorem complete_of_realize {ρ : GroundAssignment} {a : CompareTy} {x : GroundTy}
    (h : a.realize ρ = some x) : a.complete ρ = x := by
  induction a generalizing x <;>
    simp only [realize, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  all_goals
    first
    | exact h
    | (rcases h with ⟨u, hu, v, hv, h⟩;
       simp_all [complete, ModExpr.complete_of_eval])

theorem complete_shape {Δ : Bounds} {ρ : GroundAssignment} {a : CompareTy}
    (hs : a.WellShaped Δ) (hΔ : GroundModels ρ Δ) :
    (observe (a.complete ρ)).shape =
      a.shape.subst (fun v => (observe (ρ.types v)).shape) := by
  induction a <;> simp only [WellShaped] at hs
  case join a b iha ihb | meet a b iha ihb =>
    have he := (iha hs.1).trans
      ((hs.2.2 _ hΔ.comparisonShapes).trans (ihb hs.2.1).symm)
    first
    | (obtain ⟨x, hx⟩ := (groundBlend_exists_iff true _ _).mpr he;
       simpa only [complete, hx, Option.getD_some, shape] using
         (Profile.blend_shape (groundBlend_observe hx)).trans (iha hs.1))
    | (obtain ⟨x, hx⟩ := (groundBlend_exists_iff false _ _).mpr he;
       simpa only [complete, hx, Option.getD_some, shape] using
         (Profile.blend_shape (groundBlend_observe hx)).trans (iha hs.1))
  all_goals simp_all [complete, observe, observe_modal, Profile.shape, shape,
    ComparisonShape.subst]

theorem complete_blend {Δ : Bounds} {ρ : GroundAssignment} {a b : CompareTy}
    (hs : (.join a b : CompareTy).WellShaped Δ) (hΔ : GroundModels ρ Δ) (p : Bool) :
    groundBlend p (a.complete ρ) (b.complete ρ) =
      some ((ComparisonAlgebra.typeOp p a b).complete ρ) := by
  obtain ⟨x, hx⟩ := (groundBlend_exists_iff p _ _).mpr
    ((a.complete_shape hs.1 hΔ).trans
      ((hs.2.2 _ hΔ.comparisonShapes).trans (b.complete_shape hs.2.1 hΔ).symm))
  cases p <;> simp only [ComparisonAlgebra.typeOp, Bool.false_eq_true, if_false,
    if_true, complete, hx, Option.getD_some]

end CompareTy

theorem Submode.complete {Δ : Bounds} {ρ : GroundAssignment} {m n : ModExpr}
    (h : Submode Δ m n) (hΔ : GroundModels ρ Δ) :
    (m.complete ρ.modes).le (n.complete ρ.modes) = true := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h.denote hΔ.modeModels
  simpa only [ModExpr.complete_of_eval hx, ModExpr.complete_of_eval hy] using hxy

theorem ShapedSubtype.complete {Δ : Bounds} {ρ : GroundAssignment} {a b : CompareTy}
    (h : ShapedSubtype Δ a b) (hΔ : GroundModels ρ Δ) :
    GroundOrder (a.complete ρ) (b.complete ρ) := by
  induction h
  case joinLeast a b c hac hbc iha ihb =>
    exact (groundBlend_universal
      (CompareTy.complete_blend (ShapedSubtype.joinLeast hac hbc).wellShaped_left hΔ true)
      (c.complete ρ)).mpr ⟨iha, ihb⟩
  case meetGreatest a b c hab hac iha ihb =>
    exact (groundBlend_universal
      (CompareTy.complete_blend (ShapedSubtype.meetGreatest hab hac).wellShaped_right hΔ false)
      (a.complete ρ)).mpr ⟨iha, ihb⟩
  case joinLeft a b hs =>
    exact ((groundBlend_universal (CompareTy.complete_blend hs hΔ true)
      ((a.join b).complete ρ)).mp (GroundOrder.refl _)).1
  case joinRight a b hs =>
    exact ((groundBlend_universal (CompareTy.complete_blend hs hΔ true)
      ((a.join b).complete ρ)).mp (GroundOrder.refl _)).2
  case meetLeft a b hs =>
    exact ((groundBlend_universal (CompareTy.complete_blend hs hΔ false)
      ((a.meet b).complete ρ)).mp (GroundOrder.refl _)).1
  case meetRight a b hs =>
    exact ((groundBlend_universal (CompareTy.complete_blend hs hΔ false)
      ((a.meet b).complete ρ)).mp (GroundOrder.refl _)).2
  case bound a b hc =>
    obtain ⟨x, y, hx, hy, hxy⟩ := hΔ (.sub a b) hc
    simpa only [CompareTy.complete_of_realize (by simpa using hx :
      (CompareTy.ofTy a).realize ρ = some x),
      CompareTy.complete_of_realize (by simpa using hy :
        (CompareTy.ofTy b).realize ρ = some y)] using GroundOrder.of_subtype hxy
  case congr a b m n hab hmn ih => exact ih.modal (hmn.complete hΔ)
  case prod a b c d m hac hbd iha ihb | sum a b c d m hac hbd iha ihb =>
    simp only [CompareTy.complete, GroundTy.modal, Mode.identity_compose] at *
    first | exact .prod (Mode.le_refl _) iha ihb | exact .sum (Mode.le_refl _) iha ihb
  case fn a b c d m n hca hbd hmn iha ihb =>
    have hh := hmn.complete hΔ
    simp only [CompareTy.complete, GroundTy.modal, Mode.identity_compose]
    exact .fn iha ihb
      (by simpa [ModExpr.complete, ModExpr.top, Mode.compose, Mode.top] using
        ((Mode.le_iff _ _).mp hh).1)
      (by simpa [ModExpr.complete, ModExpr.top, Mode.compose, Mode.top] using
        ((Mode.le_iff _ _).mp hh).2.1)
  case credit m n hmn =>
    simpa only [CompareTy.complete, ModExpr.complete, GroundTy.modal,
      Mode.identity_compose] using GroundOrder.credit (hmn.complete hΔ)
  all_goals try simp only [CompareTy.complete, ModExpr.complete, ModExpr.epsilon,
    GroundTy.modal_identity, GroundTy.modal_compose]
  all_goals solve_by_elim [GroundOrder.refl, GroundOrder.trans]

theorem ComparisonAlgebra.Equation.complete {Δ : Bounds} {ρ : GroundAssignment}
    {a b : CompareTy} (h : Equation Δ a b) (hΔ : GroundModels ρ Δ) :
    (a.complete ρ).Equivalent (b.complete ρ) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h.ground hΔ
  simpa only [CompareTy.complete_of_realize hx, CompareTy.complete_of_realize hy] using hxy

theorem AlgebraSubtype.complete {Δ : Bounds} {ρ : GroundAssignment} {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (hΔ : GroundModels ρ Δ) :
    GroundOrder (a.complete ρ) (b.complete ρ) := by
  induction h
  case clamp b a t m _ _ _ _ _ hba hat | clampRev b a t m _ _ _ _ _ hba hat =>
    obtain ⟨j, hj⟩ := (groundBlend_exists_iff true (a.complete ρ)
      ((b.complete ρ).modal (m.complete ρ.modes))).mpr
      (by simpa only [observe_modal, Profile.shape_clip] using
        (observe_le_of_groundOrder hba).shape.symm)
    obtain ⟨v, hv, heq⟩ := groundBlend_clamp hba hat (m.complete ρ.modes) hj
    simp only [CompareTy.complete, hj, Option.getD_some, hv]
    first | exact heq.2 | exact heq.1
  case shaped h => exact h.complete hΔ
  case trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  case equation h => exact (h.complete hΔ).1
  case equationRev h => exact (h.complete hΔ).2
  case congr a b m n hab hmn ih => exact ih.modal (hmn.complete hΔ)
  case prod a b c d m hac hbd iha ihb | sum a b c d m hac hbd iha ihb =>
    simp only [CompareTy.complete, GroundTy.modal, Mode.identity_compose] at *
    first | exact .prod (Mode.le_refl _) iha ihb | exact .sum (Mode.le_refl _) iha ihb
  case fn a b c d m n hca hbd hmn iha ihb =>
    have hh := hmn.complete hΔ
    simp only [CompareTy.complete, GroundTy.modal, Mode.identity_compose]
    exact .fn iha ihb
      (by simpa [ModExpr.complete, ModExpr.top, Mode.compose, Mode.top] using
        ((Mode.le_iff _ _).mp hh).1)
      (by simpa [ModExpr.complete, ModExpr.top, Mode.compose, Mode.top] using
        ((Mode.le_iff _ _).mp hh).2.1)
  case joinLeast a b c hac hbc iha ihb =>
    exact (groundBlend_universal
      (CompareTy.complete_blend (AlgebraSubtype.joinLeast hac hbc).wellShaped_left hΔ true)
      (c.complete ρ)).mpr ⟨iha, ihb⟩
  case meetGreatest a b c hab hac iha ihb =>
    exact (groundBlend_universal
      (CompareTy.complete_blend (AlgebraSubtype.meetGreatest hab hac).wellShaped_right hΔ false)
      (a.complete ρ)).mpr ⟨iha, ihb⟩

/-- Arbitrary internal derivations preserve the original ground order whenever
both endpoints realize; no definedness premise is imposed on intermediate
lattice expressions. -/
theorem AlgebraSubtype.ground {Δ : Bounds} {ρ : GroundAssignment} {a b : CompareTy}
    {x y : GroundTy} (h : AlgebraSubtype Δ a b) (hΔ : GroundModels ρ Δ)
    (ha : a.realize ρ = some x) (hb : b.realize ρ = some y) : GroundOrder x y := by
  simpa only [CompareTy.complete_of_realize ha, CompareTy.complete_of_realize hb] using
    h.complete hΔ

def CompareGroundSatisfies (ρ : GroundAssignment) : CompareConstraint → Prop
  | .sub a b => ∃ x y, a.realize ρ = some x ∧ b.realize ρ = some y ∧ GroundOrder x y
  | .mode a b => a.Below ρ.modes b
  | .defined m => m.WellFormed ρ.modes
  | .equal v a => ∃ x, a.realize ρ = some x ∧ (ρ.types v).Equivalent x
  | .equiv a b => ∃ x y, a.realize ρ = some x ∧ b.realize ρ = some y ∧ x.Equivalent y

def CompareGroundModels (ρ : GroundAssignment) (cs : CompareBounds) : Prop :=
  ∀ c ∈ cs, CompareGroundSatisfies ρ c

theorem AlgebraEntails.groundSatisfies {Δ : Bounds} {ρ : GroundAssignment}
    {c : CompareConstraint} (h : AlgebraEntails Δ c) (hΔ : GroundModels ρ Δ) :
    CompareGroundSatisfies ρ c := by
  cases c
  case sub a b =>
    obtain ⟨x, hx⟩ := h.2.1.realize_defined h.1.wellShaped_left hΔ
    obtain ⟨y, hy⟩ := h.2.2.realize_defined h.1.wellShaped_right hΔ
    exact ⟨x, y, hx, hy, h.1.ground hΔ hx hy⟩
  case equiv a b =>
    obtain ⟨x, hx⟩ := h.2.2.1.realize_defined h.1.wellShaped_left hΔ
    obtain ⟨y, hy⟩ := h.2.2.2.realize_defined h.1.wellShaped_right hΔ
    exact ⟨x, y, hx, hy, h.1.ground hΔ hx hy, h.2.1.ground hΔ hy hx⟩
  case equal v a =>
    obtain ⟨x, hx⟩ := h.2.2.realize_defined h.1.wellShaped_right hΔ
    exact ⟨x, hx, h.1.ground hΔ rfl hx, h.2.1.ground hΔ hx rfl⟩
  case mode a b => exact h.denote hΔ.modeModels
  case defined m => exact h ρ.modes hΔ.modeModels

theorem AlgebraEntailsAll.groundModels {Δ : Bounds} {ρ : GroundAssignment}
    {cs : CompareBounds} (h : AlgebraEntailsAll Δ cs) (hΔ : GroundModels ρ Δ) :
    CompareGroundModels ρ cs := fun c hc => (h c hc).groundSatisfies hΔ

/-- Complete internal type images to ordinary ground types. Successful original
evaluations are preserved, and unquantified names keep their ambient values. -/
def CompareSubstitution.ground (σ : CompareSubstitution) (ρ : GroundAssignment) : GroundAssignment :=
  ⟨fun v => (σ.type v).complete ρ, fun v => (σ.mode v).complete ρ.modes⟩

theorem ModExpr.eval_compareGround {σ : CompareSubstitution} {ρ : GroundAssignment}
    {m : ModExpr} {n : Mode} (h : (m.subst σ.mode).eval (some ∘ ρ.modes) = some n) :
    m.eval (some ∘ (σ.ground ρ).modes) = some n := by
  rw [ModExpr.eval_subst] at h
  exact m.eval_refinement (fun v n hn => by
    simp only [CompareSubstitution.ground, Function.comp_apply, ModExpr.complete_of_eval hn]) h

theorem TypeExpr.realize_compareGround {σ : CompareSubstitution} {ρ : GroundAssignment}
    (a : Ty) {x : GroundTy} (h : (σ.ty a).realize ρ = some x) :
    a.realize (σ.ground ρ) = some x := by
  induction a generalizing x <;>
    simp only [CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst, CompareTy.realize,
      TypeExpr.realize, bind, pure, Option.bind_eq_some_iff] at *
  case var v => exact congrArg some (CompareTy.complete_of_realize h)
  case modal a m ih =>
    exact let ⟨x, hx, n, hn, ht⟩ := h
      ⟨x, ih hx, n, ModExpr.eval_compareGround hn, ht⟩
  all_goals aesop

theorem CompareGroundSatisfies.pullback {σ : CompareSubstitution} {ρ : GroundAssignment}
    {c : Constraint} (h : CompareGroundSatisfies ρ (σ.constraint c)) :
    GroundSatisfies (σ.ground ρ) c := by
  cases c
  case equal v a =>
    cases v <;> simp only [CompareSubstitution.constraint, CompareGroundSatisfies,
      GroundSatisfies] at h ⊢
    case flex n =>
      cases he : σ.types.lookup n <;> simp only [he] at h
      case some t =>
        obtain ⟨x, y, hx, hy, hs⟩ := h
        refine ⟨y, a.realize_compareGround hy, ?_, ?_⟩
        all_goals simp only [CompareSubstitution.ground, CompareSubstitution.type,
          he, Option.getD_some, CompareTy.complete_of_realize hx]
        · exact hs.1.to_subtype
        · exact hs.2.to_subtype
      case none =>
        obtain ⟨y, hy, hs⟩ := h
        refine ⟨y, a.realize_compareGround hy, ?_, ?_⟩
        all_goals simp only [CompareSubstitution.ground, CompareSubstitution.type,
          he, Option.getD_none, CompareTy.complete]
        · exact hs.1.to_subtype
        · exact hs.2.to_subtype
    case rigid n =>
      obtain ⟨y, hy, hs⟩ := h
      exact ⟨y, a.realize_compareGround hy, hs.1.to_subtype, hs.2.to_subtype⟩
  case sub a b =>
    exact let ⟨x, y, hx, hy, hs⟩ := h
      ⟨x, y, a.realize_compareGround hx, b.realize_compareGround hy, hs.to_subtype⟩
  case equiv a b =>
    exact let ⟨x, y, hx, hy, hs⟩ := h
      ⟨x, y, a.realize_compareGround hx, b.realize_compareGround hy,
        hs.1.to_subtype, hs.2.to_subtype⟩
  case mode a b =>
    exact let ⟨x, y, hx, hy, hs⟩ := h
      ⟨x, y, ModExpr.eval_compareGround hx, ModExpr.eval_compareGround hy, hs⟩
  case defined m =>
    exact let ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
      Option.isSome_iff_exists.mpr ⟨n, ModExpr.eval_compareGround hn⟩

theorem CompareGroundModels.pullback {σ : CompareSubstitution} {ρ : GroundAssignment}
    {cs : Bounds} (h : CompareGroundModels ρ (σ.bounds cs)) :
    GroundModels (σ.ground ρ) cs :=
  fun c hc => (h (σ.constraint c) (List.mem_map.mpr ⟨c, hc, rfl⟩)).pullback

private theorem lookup_none_of_not_key {α : Type} {xs : List (Nat × α)} {n : Nat}
    (h : n ∉ xs.map Prod.fst) : xs.lookup n = none := by
  exact List.lookup_eq_none_iff.mpr fun p hp => by
    simpa only [bne_iff_ne] using
      (fun he : n = p.1 => h (List.mem_map.mpr ⟨p, hp, he.symm⟩))

theorem CompareInstantiates.ground {σ : CompareSubstitution} {s : Scheme}
    {ρ : GroundAssignment} (h : CompareInstantiates s σ)
    (hb : CompareGroundModels ρ (σ.bounds s.bounds)) :
    GroundInstantiates ρ s (σ.ground ρ) := by
  refine ⟨?_, ?_, hb.pullback⟩
  all_goals rintro (n | n) hv
  case refine_1.flex =>
    have he : σ.types.lookup n = none := lookup_none_of_not_key fun hn =>
      hv (List.mem_map.mpr ⟨n, h.1.mem_iff.mp hn, rfl⟩)
    simp [CompareSubstitution.ground, CompareSubstitution.type, CompareTy.complete, he]
  case refine_2.flex =>
    have he : σ.modes.lookup n = none := lookup_none_of_not_key fun hn =>
      hv (List.mem_map.mpr ⟨n, h.2.mem_iff.mp hn, rfl⟩)
    simp [CompareSubstitution.ground, CompareSubstitution.mode, ModExpr.complete, he]
  all_goals rfl

end ModalityInference
