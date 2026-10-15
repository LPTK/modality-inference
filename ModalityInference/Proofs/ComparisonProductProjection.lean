import ModalityInference.Proofs.ComparisonStructuralProjection

namespace ModalityInference.ComparisonStructuralProjection

open ComparisonAlgebra

def pairHead : Bool → ComparisonShape → Bool
  | false, .prod _ _ | true, .sum _ _ => true
  | _, _ => false

theorem pairHead_subst (s : ComparisonShape) (isSum : Bool) :
    pairHead isSum (s.subst unitShapes) = pairHead isSum s := by
  cases isSum <;> cases s <;> rfl

theorem pairHead_equivalent {Δ : Bounds} (hΔ : Residual Δ) {a b : ComparisonShape}
    (h : ComparisonShape.Equivalent Δ a b) (isSum : Bool) : pairHead isSum a = pairHead isSum b := by
  have hh := congrArg (pairHead isSum) (h unitShapes (residual_unitShapes hΔ))
  simpa only [pairHead_subst] using hh

inductive PairRoot : Bool → CompareTy → Prop where
  | prod (a b : CompareTy) : PairRoot false (.prod a b)
  | sum (a b : CompareTy) : PairRoot true (.sum a b)
  | modal {isSum a m} : PairRoot isSum a → PairRoot isSum (.modal a m)
  | join {isSum a b} : PairRoot isSum a → PairRoot isSum b → PairRoot isSum (.join a b)
  | meet {isSum a b} : PairRoot isSum a → PairRoot isSum b → PairRoot isSum (.meet a b)

theorem PairRoot.head {isSum : Bool} {a : CompareTy} (h : PairRoot isSum a) :
    pairHead isSum a.shape = true := by
  induction h <;> first | rfl | assumption

theorem PairRoot.of_head {Δ : Bounds} (hΔ : Residual Δ) {a : CompareTy}
    (hs : a.WellShaped Δ) (isSum : Bool) (hh : pairHead isSum a.shape = true) : PairRoot isSum a := by
  induction a with
  | prod a b => cases isSum; exact .prod a b; contradiction
  | sum a b => cases isSum; contradiction; exact .sum a b
  | modal a m ih => exact .modal (ih hs hh)
  | join a b ih₁ ih₂ =>
    exact .join (ih₁ hs.1 hh) (ih₂ hs.2.1 ((pairHead_equivalent hΔ hs.2.2 isSum).symm.trans hh))
  | meet a b ih₁ ih₂ =>
    exact .meet (ih₁ hs.1 hh) (ih₂ hs.2.1 ((pairHead_equivalent hΔ hs.2.2 isSum).symm.trans hh))
  | var | unit | credit | fn => cases isSum <;> contradiction

theorem PairRoot.transport {Δ : Bounds} (hΔ : Residual Δ) {isSum : Bool} {a b : CompareTy}
    (ha : PairRoot isSum a) (hb : b.WellShaped Δ)
    (he : ComparisonShape.Equivalent Δ a.shape b.shape) : PairRoot isSum b :=
  .of_head hΔ hb isSum ((pairHead_equivalent hΔ he isSum).symm.trans ha.head)

def pairChild (right : Bool) : CompareTy → CompareTy
  | .prod a b | .sum a b => if right then b else a
  | .modal a m => .modal (pairChild right a) m
  | .join a b => .join (pairChild right a) (pairChild right b)
  | .meet a b => .meet (pairChild right a) (pairChild right b)
  | _ => .unit

theorem pairChild_shape {isSum : Bool} {a : CompareTy} (ha : PairRoot isSum a) :
    a.shape = (if isSum then ComparisonShape.sum else ComparisonShape.prod)
      (pairChild false a).shape (pairChild true a).shape := by
  induction ha <;> simp_all only [CompareTy.shape, pairChild, Bool.false_eq_true, if_false, if_true]

theorem pairChild_equivalent {Δ : Bounds} {isSum : Bool} {a b : CompareTy}
    (ha : PairRoot isSum a) (hb : PairRoot isSum b)
    (he : ComparisonShape.Equivalent Δ a.shape b.shape) (right : Bool) :
    ComparisonShape.Equivalent Δ (pairChild right a).shape (pairChild right b).shape := by
  intro ρ hρ
  have hh := he ρ hρ
  rw [pairChild_shape ha, pairChild_shape hb] at hh
  cases isSum <;> cases right <;>
    first | exact (ComparisonShape.prod.inj hh).1 | exact (ComparisonShape.prod.inj hh).2
          | exact (ComparisonShape.sum.inj hh).1 | exact (ComparisonShape.sum.inj hh).2

theorem pairChild_shaped {Δ : Bounds} {isSum : Bool} {a : CompareTy}
    (ha : PairRoot isSum a) (hs : a.WellShaped Δ) (right : Bool) :
    (pairChild right a).WellShaped Δ := by
  induction ha with
  | prod a b | sum a b => cases right <;> first | exact hs.1 | exact hs.2
  | modal ha ih => exact ih hs
  | join ha hb ih₁ ih₂ | meet ha hb ih₁ ih₂ =>
    exact ⟨ih₁ hs.1, ih₂ hs.2.1, pairChild_equivalent ha hb hs.2.2 right⟩

theorem pairChild_defined {Δ : Bounds} {isSum : Bool} {a : CompareTy}
    (ha : PairRoot isSum a) (hd : a.DefinedUnder Δ) (right : Bool) :
    (pairChild right a).DefinedUnder Δ := by
  induction ha with
  | prod a b => cases right <;> first
      | exact (CompareTy.definedUnder_prod_iff.mp hd).1
      | exact (CompareTy.definedUnder_prod_iff.mp hd).2
  | sum a b => cases right <;> first
      | exact (CompareTy.definedUnder_sum_iff.mp hd).1
      | exact (CompareTy.definedUnder_sum_iff.mp hd).2
  | modal ha ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp hd
    exact CompareTy.definedUnder_modal_iff.mpr ⟨ih hh.1, hh.2⟩
  | join ha hb ih₁ ih₂ =>
    exact CompareTy.definedUnder_join_iff.mpr
      ⟨ih₁ (CompareTy.definedUnder_join_iff.mp hd).1, ih₂ (CompareTy.definedUnder_join_iff.mp hd).2⟩
  | meet ha hb ih₁ ih₂ =>
    exact CompareTy.definedUnder_meet_iff.mpr
      ⟨ih₁ (CompareTy.definedUnder_meet_iff.mp hd).1, ih₂ (CompareTy.definedUnder_meet_iff.mp hd).2⟩

theorem pairChild_compatible {Δ : Bounds} {isSum : Bool} {a b : CompareTy}
    (ha : PairRoot isSum a) (hb : PairRoot isSum b) (hc : Compatible Δ a b) (right : Bool) :
    Compatible Δ (pairChild right a) (pairChild right b) :=
  ⟨⟨pairChild_shaped ha hc.1.1 right, pairChild_shaped hb hc.1.2.1 right,
    pairChild_equivalent ha hb hc.1.2.2 right⟩,
   pairChild_defined ha hc.2.1 right, pairChild_defined hb hc.2.2 right⟩

theorem PairRoot.modal_inv {isSum : Bool} {a : CompareTy} {m : ModExpr}
    (h : PairRoot isSum (.modal a m)) : PairRoot isSum a := by cases h; assumption

theorem PairRoot.typeOp_inv {isSum p : Bool} {a b : CompareTy}
    (h : PairRoot isSum (typeOp p a b)) : PairRoot isSum a ∧ PairRoot isSum b := by
  cases p <;> cases h <;> exact ⟨by assumption, by assumption⟩

@[simp] theorem pairChild_typeOp (right p : Bool) (a b : CompareTy) :
    pairChild right (typeOp p a b) = typeOp p (pairChild right a) (pairChild right b) := by
  cases p <;> rfl


theorem pairChild_equation {Δ : Bounds} {isSum : Bool} {a b : CompareTy}
    (h : Equation Δ a b) (ha : PairRoot isSum a) (right : Bool) :
    AlgebraSubtype Δ (pairChild right a) (pairChild right b) ∧
      AlgebraSubtype Δ (pairChild right b) (pairChild right a) := by
  have hs := pairChild_shaped ha h.wellShaped.1 right
  cases h with
  | distrib p hab hac =>
    have hh := ha.typeOp_inv
    have hbc := hh.2.typeOp_inv
    have hab' := pairChild_compatible hh.1 hbc.1 hab right
    have hac' := pairChild_compatible hh.1 hbc.2 hac right
    simpa only [pairChild_typeOp] using
      And.intro (AlgebraSubtype.equation (.distrib p hab' hac'))
        (AlgebraSubtype.equationRev (.distrib p hab' hac'))
  | modal p hab hm =>
    have hh := ha.modal_inv.typeOp_inv
    have hab' := pairChild_compatible hh.1 hh.2 hab right
    simpa only [pairChild, pairChild_typeOp] using
      And.intro (AlgebraSubtype.equation (.modal p hab' hm))
        (AlgebraSubtype.equationRev (.modal p hab' hm))
  | scalar p has had hm hn =>
    have ha' := ha.modal_inv
    simpa only [pairChild, pairChild_typeOp] using
      And.intro (AlgebraSubtype.equation (.scalar p
        (pairChild_shaped ha' has right) (pairChild_defined ha' had right) hm hn))
        (AlgebraSubtype.equationRev (.scalar p
          (pairChild_shaped ha' has right) (pairChild_defined ha' had right) hm hn))
  | prod p hac hbd =>
    cases right <;> cases p
    all_goals exact ⟨.refl hs, .refl hs⟩
  | sum p hac hbd =>
    cases right <;> cases p
    all_goals exact ⟨.refl hs, .refl hs⟩
  | fn p hac hbd =>
    have hh := ha.typeOp_inv
    cases hh.1


theorem bound_not_pair {Δ : Bounds} (hΔ : Residual Δ) {isSum : Bool} {a b : Ty}
    (hab : .sub a b ∈ Δ) : ¬ PairRoot isSum (.ofTy a) := by
  intro ha
  obtain ⟨x, y, m, n, hx, hy⟩ := List.forall_iff_forall_mem.mp hΔ (.sub a b) hab
  have hh := ha.head
  rw [CompareTy.shape_ofTy, ← TypeExpr.outer_comparisonShape a, hx] at hh
  cases isSum <;> contradiction

theorem shaped_pairChild {Δ : Bounds} (hΔ : Residual Δ) {isSum : Bool} {a b : CompareTy}
    (h : ShapedSubtype Δ a b) (ha : PairRoot isSum a) (right : Bool) :
    AlgebraSubtype Δ (pairChild right a) (pairChild right b) := by
  induction h with
  | refl hs => exact .refl (pairChild_shaped ha hs right)
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ ha).trans (ih₂ (ha.transport hΔ h₁.wellShaped_right h₁.shape_equivalent))
  | bound hb => exact False.elim (bound_not_pair hΔ hb ha)
  | identity hs => exact .shaped (.identity (pairChild_shaped ha.modal_inv hs right))
  | identityRev hs => exact .shaped (.identityRev (pairChild_shaped ha hs right))
  | compose hs => exact .shaped (.compose (pairChild_shaped ha.modal_inv.modal_inv hs right))
  | composeRev hs => exact .shaped (.composeRev (pairChild_shaped ha.modal_inv hs right))
  | congr h hm ih => exact .congr (ih ha.modal_inv) hm
  | prod h₁ h₂ ih₁ ih₂ => cases right <;> first | exact .shaped h₁ | exact .shaped h₂
  | sum h₁ h₂ ih₁ ih₂ => cases right <;> first | exact .shaped h₁ | exact .shaped h₂
  | fn hca hbd hm ih₁ ih₂ => cases ha.modal_inv
  | joinLeft hs =>
    have hb := ha.transport hΔ hs.2.1 hs.2.2
    exact .shaped (.joinLeft (pairChild_shaped (.join ha hb) hs right))
  | joinRight hs =>
    have hb := ha.transport hΔ hs.1 hs.2.2.symm
    exact .shaped (.joinRight (pairChild_shaped (.join hb ha) hs right))
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hh := ha.typeOp_inv (p := true)
    exact .joinLeast (ih₁ hh.1) (ih₂ hh.2)
  | meetLeft hs => exact .shaped (.meetLeft (pairChild_shaped ha hs right))
  | meetRight hs => exact .shaped (.meetRight (pairChild_shaped ha hs right))
  | meetGreatest h₁ h₂ ih₁ ih₂ => exact .meetGreatest (ih₁ ha) (ih₂ ha)

/-- Product and sum projections retain every inherited modal action, including
partial actions, throughout an arbitrary algebraic derivation. -/
theorem algebra_pairChild {Δ : Bounds} (hΔ : Residual Δ) {isSum : Bool} {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (ha : PairRoot isSum a) (right : Bool) :
    AlgebraSubtype Δ (pairChild right a) (pairChild right b) := by
  induction h with
  | shaped h => exact shaped_pairChild hΔ h ha right
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ ha).trans (ih₂ (ha.transport hΔ h₁.wellShaped_right h₁.shape_equivalent))
  | equation h => exact (pairChild_equation h ha right).1
  | equationRev h =>
    have hr : PairRoot isSum _ := .of_head hΔ h.wellShaped.1 isSum
      (by rw [h.shape_eq]; exact ha.head)
    exact (pairChild_equation h hr right).2
  | congr h hm ih => exact .congr (ih ha.modal_inv) hm
  | prod h₁ h₂ ih₁ ih₂ => cases right <;> first | exact h₁ | exact h₂
  | sum h₁ h₂ ih₁ ih₂ => cases right <;> first | exact h₁ | exact h₂
  | fn hca hbd hm ih₁ ih₂ => cases ha.modal_inv
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hh := ha.typeOp_inv (p := true)
    exact .joinLeast (ih₁ hh.1) (ih₂ hh.2)
  | meetGreatest h₁ h₂ ih₁ ih₂ => exact .meetGreatest (ih₁ ha) (ih₂ ha)
  | @clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have ar := ha.modal_inv
    have br := ar.transport hΔ h₁.wellShaped_left h₁.shape_equivalent.symm
    have tr := ar.transport hΔ h₂.wellShaped_right h₂.shape_equivalent
    exact .clamp (pairChild_compatible br ar hba right)
      (pairChild_compatible ar tr hat right) hm (ih₁ br) (ih₂ ar)
  | @clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have ar : PairRoot isSum _ := .of_head hΔ hba.1.2.1 isSum ha.head
    have br := ar.transport hΔ h₁.wellShaped_left h₁.shape_equivalent.symm
    have tr := ar.transport hΔ h₂.wellShaped_right h₂.shape_equivalent
    exact .clampRev (pairChild_compatible br ar hba right)
      (pairChild_compatible ar tr hat right) hm (ih₁ br) (ih₂ ar)


/-- Product inversion in the full algebra retains the inherited labels on both
projected children. The labels need not be total. -/
theorem product_inversion {Δ : Bounds} (hΔ : Residual Δ)
    {a b c d : CompareTy} {m n : ModExpr}
    (h : AlgebraSubtype Δ (.modal (.prod a b) m) (.modal (.prod c d) n)) :
    AlgebraSubtype Δ (.modal a m) (.modal c n) ∧
      AlgebraSubtype Δ (.modal b m) (.modal d n) :=
  ⟨algebra_pairChild hΔ h (.modal (.prod a b)) false,
   algebra_pairChild hΔ h (.modal (.prod a b)) true⟩

/-- Sum inversion in the full algebra retains the inherited labels on both
projected children. The labels need not be total. -/
theorem sum_inversion {Δ : Bounds} (hΔ : Residual Δ)
    {a b c d : CompareTy} {m n : ModExpr}
    (h : AlgebraSubtype Δ (.modal (.sum a b) m) (.modal (.sum c d) n)) :
    AlgebraSubtype Δ (.modal a m) (.modal c n) ∧
      AlgebraSubtype Δ (.modal b m) (.modal d n) :=
  ⟨algebra_pairChild hΔ h (.modal (.sum a b)) false,
   algebra_pairChild hΔ h (.modal (.sum a b)) true⟩

end ModalityInference.ComparisonStructuralProjection
