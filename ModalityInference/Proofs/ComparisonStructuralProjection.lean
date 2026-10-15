import ModalityInference.Proofs.ComparisonDefinedCovers
import ModalityInference.Proofs.ComparisonWitnessShapes

/-! Function-child projections preserve the full comparison algebra under
residual declared-head assumptions. Projection reverses lattice operations
and order in domains, and retains them in codomains. Outer function actions
do not affect either child. Partial annotations and arbitrary intermediate
joins and meets are included in the derivation theorem. -/
namespace ModalityInference.ComparisonStructuralProjection

open ComparisonAlgebra

def fnHead : ComparisonShape → Bool
  | .fn _ _ => true
  | _ => false

def unitShapes (_ : TypeVar) : ComparisonShape := .unit

theorem fnHead_subst (s : ComparisonShape) : fnHead (s.subst unitShapes) = fnHead s := by
  cases s <;> rfl

theorem residual_unitShapes {Δ : Bounds} (hΔ : Residual Δ) : ComparisonShape.Models Δ unitShapes := by
  intro pair hp
  obtain ⟨c, hc, hp⟩ := List.mem_flatMap.mp hp
  have hr := List.forall_iff_forall_mem.mp hΔ c hc
  cases c <;> simp only [List.mem_singleton, List.not_mem_nil] at hp
  all_goals try contradiction
  case sub a b =>
    subst pair
    obtain ⟨x, y, m, n, ha, hb⟩ := hr
    have hsa := TypeExpr.outer_comparisonShape a
    have hsb := TypeExpr.outer_comparisonShape b
    rw [ha] at hsa
    rw [hb] at hsb
    simp only [ComparisonShape.ofTy] at hsa hsb
    simp only [← hsa, ← hsb, ComparisonShape.subst, unitShapes]

theorem head_equivalent {Δ : Bounds} (hΔ : Residual Δ) {a b : ComparisonShape}
    (h : ComparisonShape.Equivalent Δ a b) : fnHead a = fnHead b := by
  have hh := congrArg fnHead (h unitShapes (residual_unitShapes hΔ))
  simpa only [fnHead_subst] using hh

inductive FunctionRoot : CompareTy → Prop where
  | fn (a b : CompareTy) : FunctionRoot (.fn a b)
  | modal {a m} : FunctionRoot a → FunctionRoot (.modal a m)
  | join {a b} : FunctionRoot a → FunctionRoot b → FunctionRoot (.join a b)
  | meet {a b} : FunctionRoot a → FunctionRoot b → FunctionRoot (.meet a b)

theorem FunctionRoot.head {a : CompareTy} (h : FunctionRoot a) : fnHead a.shape = true := by
  induction h <;> first | rfl | assumption

theorem FunctionRoot.of_head {Δ : Bounds} (hΔ : Residual Δ) {a : CompareTy}
    (hs : a.WellShaped Δ) (hh : fnHead a.shape = true) : FunctionRoot a := by
  induction a with
  | fn a b => exact .fn a b
  | modal a m ih => exact .modal (ih hs hh)
  | join a b ih₁ ih₂ =>
    exact .join (ih₁ hs.1 hh) (ih₂ hs.2.1 ((head_equivalent hΔ hs.2.2).symm.trans hh))
  | meet a b ih₁ ih₂ =>
    exact .meet (ih₁ hs.1 hh) (ih₂ hs.2.1 ((head_equivalent hΔ hs.2.2).symm.trans hh))
  | var | unit | credit | prod | sum => contradiction

theorem FunctionRoot.transport {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (ha : FunctionRoot a) (hb : b.WellShaped Δ)
    (he : ComparisonShape.Equivalent Δ a.shape b.shape) : FunctionRoot b :=
  .of_head hΔ hb ((head_equivalent hΔ he).symm.trans ha.head)

def fnChild (contra : Bool) : CompareTy → CompareTy
  | .fn a b => if contra then a else b
  | .modal a _ => fnChild contra a
  | .join a b => typeOp (!contra) (fnChild contra a) (fnChild contra b)
  | .meet a b => typeOp contra (fnChild contra a) (fnChild contra b)
  | _ => .unit

theorem fnChild_shape {a : CompareTy} (ha : FunctionRoot a) :
    a.shape = .fn (fnChild true a).shape (fnChild false a).shape := by
  induction ha <;> simp_all only [CompareTy.shape, fnChild, Bool.not_true, Bool.not_false,
    Bool.false_eq_true, if_false, if_true, shape_typeOp]

theorem fnChild_equivalent {Δ : Bounds} {a b : CompareTy} (ha : FunctionRoot a)
    (hb : FunctionRoot b) (he : ComparisonShape.Equivalent Δ a.shape b.shape) (contra : Bool) :
    ComparisonShape.Equivalent Δ (fnChild contra a).shape (fnChild contra b).shape := by
  intro ρ hρ
  have hh := he ρ hρ
  rw [fnChild_shape ha, fnChild_shape hb] at hh
  cases contra
  · exact (ComparisonShape.fn.inj hh).2
  · exact (ComparisonShape.fn.inj hh).1

theorem fnChild_shaped {Δ : Bounds} {a : CompareTy} (ha : FunctionRoot a)
    (hs : a.WellShaped Δ) (contra : Bool) : (fnChild contra a).WellShaped Δ := by
  induction ha with
  | fn a b => cases contra <;> first | exact hs.1 | exact hs.2
  | modal ha ih => exact ih hs
  | join ha hb ih₁ ih₂ =>
    exact (typeOp_wellShaped _ _ _ _).mpr ⟨ih₁ hs.1, ih₂ hs.2.1, fnChild_equivalent ha hb hs.2.2 contra⟩
  | meet ha hb ih₁ ih₂ =>
    exact (typeOp_wellShaped _ _ _ _).mpr ⟨ih₁ hs.1, ih₂ hs.2.1, fnChild_equivalent ha hb hs.2.2 contra⟩

theorem fnChild_defined {Δ : Bounds} {a : CompareTy} (ha : FunctionRoot a)
    (hd : a.DefinedUnder Δ) (contra : Bool) : (fnChild contra a).DefinedUnder Δ := by
  induction ha with
  | fn a b =>
    cases contra <;> first
      | exact (CompareTy.definedUnder_fn_iff.mp hd).1
      | exact (CompareTy.definedUnder_fn_iff.mp hd).2
  | modal ha ih => exact ih (CompareTy.definedUnder_modal_iff.mp hd).1
  | join ha hb ih₁ ih₂ =>
    exact (ComparisonDefinedCovers.typeOp_defined _ _ _ _).mpr
      ⟨ih₁ (CompareTy.definedUnder_join_iff.mp hd).1, ih₂ (CompareTy.definedUnder_join_iff.mp hd).2⟩
  | meet ha hb ih₁ ih₂ =>
    exact (ComparisonDefinedCovers.typeOp_defined _ _ _ _).mpr
      ⟨ih₁ (CompareTy.definedUnder_meet_iff.mp hd).1, ih₂ (CompareTy.definedUnder_meet_iff.mp hd).2⟩

theorem fnChild_compatible {Δ : Bounds} {a b : CompareTy}
    (ha : FunctionRoot a) (hb : FunctionRoot b) (hc : Compatible Δ a b) (contra : Bool) :
    Compatible Δ (fnChild contra a) (fnChild contra b) :=
  ⟨⟨fnChild_shaped ha hc.1.1 contra, fnChild_shaped hb hc.1.2.1 contra,
    fnChild_equivalent ha hb hc.1.2.2 contra⟩,
   fnChild_defined ha hc.2.1 contra, fnChild_defined hb hc.2.2 contra⟩

theorem FunctionRoot.of_typeOp {p : Bool} {a b : CompareTy} (ha : FunctionRoot a)
    (hb : FunctionRoot b) : FunctionRoot (typeOp p a b) := by
  cases p <;> first | exact .join ha hb | exact .meet ha hb

theorem FunctionRoot.typeOp_inv {p : Bool} {a b : CompareTy}
    (h : FunctionRoot (typeOp p a b)) : FunctionRoot a ∧ FunctionRoot b := by
  cases p <;> cases h <;> exact ⟨by assumption, by assumption⟩

def variance (contra p : Bool) : Bool := if contra then !p else p

@[simp] theorem fnChild_typeOp (contra p : Bool) (a b : CompareTy) :
    fnChild contra (typeOp p a b) =
      typeOp (variance contra p) (fnChild contra a) (fnChild contra b) := by
  cases contra <;> cases p <;> rfl

def Rel (Δ : Bounds) (contra : Bool) (a b : CompareTy) : Prop :=
  if contra then AlgebraSubtype Δ b a else AlgebraSubtype Δ a b

theorem sandwich {Δ : Bounds} {b a t : CompareTy} (hba : AlgebraSubtype Δ b a)
    (hat : AlgebraSubtype Δ a t) :
    AlgebraSubtype Δ a (.meet (.join a b) t) ∧ AlgebraSubtype Δ (.meet (.join a b) t) a := by
  have hj : (.join a b : CompareTy).WellShaped Δ :=
    ⟨hba.wellShaped_right, hba.wellShaped_left, hba.shape_equivalent.symm⟩
  have hm : (.meet (.join a b) t : CompareTy).WellShaped Δ :=
    ⟨hj, hat.wellShaped_right, hat.shape_equivalent⟩
  exact ⟨.meetGreatest (.shaped (.joinLeft hj)) hat,
    (AlgebraSubtype.shaped (.meetLeft hm)).trans (.joinLeast (.refl hba.wellShaped_right) hba)⟩

theorem dual_sandwich {Δ : Bounds} {b a t : CompareTy} (hta : AlgebraSubtype Δ t a)
    (hab : AlgebraSubtype Δ a b) :
    AlgebraSubtype Δ a (.join (.meet a b) t) ∧ AlgebraSubtype Δ (.join (.meet a b) t) a := by
  have hm : (.meet a b : CompareTy).WellShaped Δ :=
    ⟨hab.wellShaped_left, hab.wellShaped_right, hab.shape_equivalent⟩
  have hj : (.join (.meet a b) t : CompareTy).WellShaped Δ :=
    ⟨hm, hta.wellShaped_left, hta.shape_equivalent.symm⟩
  exact ⟨(AlgebraSubtype.meetGreatest (.refl hab.wellShaped_left) hab).trans (.shaped (.joinLeft hj)),
    .joinLeast (.shaped (.meetLeft hm)) hta⟩

theorem fnChild_clamp {Δ : Bounds} {b a t : CompareTy} (contra : Bool)
    (hba : Rel Δ contra (fnChild contra b) (fnChild contra a))
    (hat : Rel Δ contra (fnChild contra a) (fnChild contra t)) (m : ModExpr) :
    AlgebraSubtype Δ (fnChild contra (.modal a m))
      (fnChild contra (.meet (.join a (.modal b m)) (.modal t m))) ∧
    AlgebraSubtype Δ (fnChild contra (.meet (.join a (.modal b m)) (.modal t m)))
      (fnChild contra (.modal a m)) := by
  cases contra
  · exact sandwich hba hat
  · exact dual_sandwich hat hba

theorem FunctionRoot.modal_inv {a : CompareTy} {m : ModExpr} (h : FunctionRoot (.modal a m)) :
    FunctionRoot a := by cases h; assumption

theorem typeOp_idem {Δ : Bounds} {a : CompareTy} (hs : a.WellShaped Δ) (p : Bool) :
    AlgebraSubtype Δ a (typeOp p a a) ∧ AlgebraSubtype Δ (typeOp p a a) a := by
  have hj : (.join a a : CompareTy).WellShaped Δ := ⟨hs, hs, ComparisonShape.Equivalent.refl⟩
  cases p
  · exact ⟨.meetGreatest (.refl hs) (.refl hs), .shaped (.meetLeft hj)⟩
  · exact ⟨.shaped (.joinLeft hj), .joinLeast (.refl hs) (.refl hs)⟩

theorem fnChild_equation {Δ : Bounds} {a b : CompareTy} (h : Equation Δ a b)
    (ha : FunctionRoot a) (contra : Bool) :
    AlgebraSubtype Δ (fnChild contra a) (fnChild contra b) ∧
      AlgebraSubtype Δ (fnChild contra b) (fnChild contra a) := by
  have hs := fnChild_shaped ha h.wellShaped.1 contra
  cases h with
  | distrib p hab hac =>
    have hh := ha.typeOp_inv
    have hbc := hh.2.typeOp_inv
    have hab' := fnChild_compatible hh.1 hbc.1 hab contra
    have hac' := fnChild_compatible hh.1 hbc.2 hac contra
    cases contra <;> cases p
    all_goals exact ⟨.equation (.distrib _ hab' hac'), .equationRev (.distrib _ hab' hac')⟩
  | modal p hab hm =>
    cases contra <;> cases p
    all_goals exact ⟨.refl hs, .refl hs⟩
  | scalar p has had hm hn =>
    have hsa := fnChild_shaped ha.modal_inv has contra
    simpa only [fnChild, fnChild_typeOp] using typeOp_idem hsa (variance contra p)
  | prod p hac hbd =>
    have hh := ha.typeOp_inv
    cases hh.1
  | sum p hac hbd =>
    have hh := ha.typeOp_inv
    cases hh.1
  | fn p hac hbd =>
    cases contra <;> cases p
    all_goals exact ⟨.refl hs, .refl hs⟩

theorem Rel.refl {Δ : Bounds} (contra : Bool) {a : CompareTy} (ha : a.WellShaped Δ) :
    Rel Δ contra a a := by cases contra <;> exact AlgebraSubtype.refl ha

theorem Rel.trans {Δ : Bounds} {contra : Bool} {a b c : CompareTy}
    (hab : Rel Δ contra a b) (hbc : Rel Δ contra b c) : Rel Δ contra a c := by
  cases contra
  · exact AlgebraSubtype.trans hab hbc
  · exact AlgebraSubtype.trans hbc hab

theorem bound_not_function {Δ : Bounds} (hΔ : Residual Δ) {a b : Ty}
    (hab : .sub a b ∈ Δ) : ¬ FunctionRoot (.ofTy a) := by
  intro ha
  obtain ⟨x, y, m, n, hx, hy⟩ := List.forall_iff_forall_mem.mp hΔ (.sub a b) hab
  have hh := ha.head
  rw [CompareTy.shape_ofTy, ← TypeExpr.outer_comparisonShape a, hx] at hh
  contradiction

theorem shaped_fnChild {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) (ha : FunctionRoot a) (contra : Bool) :
    Rel Δ contra (fnChild contra a) (fnChild contra b) := by
  induction h with
  | refl hs => exact Rel.refl contra (fnChild_shaped ha hs contra)
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ ha).trans (ih₂ (ha.transport hΔ h₁.wellShaped_right h₁.shape_equivalent))
  | bound hb => exact False.elim (bound_not_function hΔ hb ha)
  | identity hs => exact Rel.refl contra (fnChild_shaped ha.modal_inv hs contra)
  | identityRev hs => exact Rel.refl contra (fnChild_shaped ha hs contra)
  | compose hs => exact Rel.refl contra (fnChild_shaped ha.modal_inv.modal_inv hs contra)
  | composeRev hs => exact Rel.refl contra (fnChild_shaped ha.modal_inv hs contra)
  | congr h hm ih => exact ih ha.modal_inv
  | prod h₁ h₂ ih₁ ih₂ => cases ha.modal_inv
  | sum h₁ h₂ ih₁ ih₂ => cases ha.modal_inv
  | fn hca hbd hm ih₁ ih₂ => cases contra <;> first | exact .shaped hca | exact .shaped hbd
  | joinLeft hs =>
    have hb := ha.transport hΔ hs.2.1 hs.2.2
    have hp := fnChild_shaped (.join ha hb) hs contra
    cases contra
    · exact .shaped (.joinLeft hp)
    · exact .shaped (.meetLeft hp)
  | joinRight hs =>
    have hb := ha.transport hΔ hs.1 hs.2.2.symm
    have hp := fnChild_shaped (.join hb ha) hs contra
    cases contra
    · exact .shaped (.joinRight hp)
    · exact .shaped (.meetRight hp)
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hh := ha.typeOp_inv (p := true)
    have hp := ih₁ hh.1
    have hq := ih₂ hh.2
    cases contra
    · exact .joinLeast hp hq
    · exact .meetGreatest hp hq
  | meetLeft hs =>
    have hp := fnChild_shaped ha hs contra
    cases contra
    · exact .shaped (.meetLeft hp)
    · exact .shaped (.joinLeft hp)
  | meetRight hs =>
    have hp := fnChild_shaped ha hs contra
    cases contra
    · exact .shaped (.meetRight hp)
    · exact .shaped (.joinRight hp)
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    have hp := ih₁ ha
    have hq := ih₂ ha
    cases contra
    · exact .meetGreatest hp hq
    · exact .joinLeast hp hq

/-- Project an arbitrary algebraic derivation at a function root. No
endpoint-definedness premise is imposed. -/
theorem algebra_fnChild {Δ : Bounds} (hΔ : Residual Δ) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (ha : FunctionRoot a) (contra : Bool) :
    Rel Δ contra (fnChild contra a) (fnChild contra b) := by
  induction h with
  | shaped h => exact shaped_fnChild hΔ h ha contra
  | trans h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ ha).trans (ih₂ (ha.transport hΔ h₁.wellShaped_right h₁.shape_equivalent))
  | equation h =>
    have he := fnChild_equation h ha contra
    cases contra
    · exact he.1
    · exact he.2
  | equationRev h =>
    have hr : FunctionRoot _ := .of_head hΔ h.wellShaped.1 (by rw [h.shape_eq]; exact ha.head)
    have he := fnChild_equation h hr contra
    cases contra
    · exact he.2
    · exact he.1
  | congr h hm ih => exact ih ha.modal_inv
  | prod h₁ h₂ ih₁ ih₂ => cases ha.modal_inv
  | sum h₁ h₂ ih₁ ih₂ => cases ha.modal_inv
  | fn hca hbd hm ih₁ ih₂ => cases contra <;> first | exact hca | exact hbd
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hh := ha.typeOp_inv (p := true)
    have hp := ih₁ hh.1
    have hq := ih₂ hh.2
    cases contra
    · exact .joinLeast hp hq
    · exact .meetGreatest hp hq
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    have hp := ih₁ ha
    have hq := ih₂ ha
    cases contra
    · exact .meetGreatest hp hq
    · exact .joinLeast hp hq
  | @clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have ar := ha.modal_inv
    have br := ar.transport hΔ h₁.wellShaped_left h₁.shape_equivalent.symm
    have hp := fnChild_clamp contra (ih₁ br) (ih₂ ar) m
    cases contra
    · exact hp.1
    · exact hp.2
  | @clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have ar : FunctionRoot _ := .of_head hΔ hba.1.2.1 ha.head
    have br := ar.transport hΔ h₁.wellShaped_left h₁.shape_equivalent.symm
    have hp := fnChild_clamp contra (ih₁ br) (ih₂ ar) m
    cases contra
    · exact hp.2
    · exact hp.1

/-- Function inversion remains valid in the full guarded comparison algebra. -/
theorem function_inversion {Δ : Bounds} (hΔ : Residual Δ)
    {a b c d : CompareTy} {m n : ModExpr}
    (h : AlgebraSubtype Δ (.modal (.fn a b) m) (.modal (.fn c d) n)) :
    AlgebraSubtype Δ c a ∧ AlgebraSubtype Δ b d :=
  ⟨algebra_fnChild hΔ h (.modal (.fn a b)) true,
   algebra_fnChild hΔ h (.modal (.fn a b)) false⟩

end ModalityInference.ComparisonStructuralProjection
