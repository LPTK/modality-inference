import ModalityInference.Proofs.ComparisonProductProjection

/-! Constructor projections at a resolved shape not named by the declared
context. Structural bounds at other shapes remain available. -/

namespace ModalityInference.ComparisonUnanchoredProjection

open ComparisonAlgebra ComparisonStructuralProjection

structure Zone (Δ : Bounds) (ρ : TypeVar → ComparisonShape) (s : ComparisonShape) : Prop where
  models : ComparisonShape.Models Δ ρ
  names : ∀ v, ρ v ≠ s
  bounds : ∀ {a b}, Constraint.sub a b ∈ Δ → (CompareTy.ofTy a).shape.subst ρ ≠ s

theorem pairRoot_of_resolved {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) {a : CompareTy}
    (hs : a.WellShaped Δ) (isSum : Bool) (hr : pairHead isSum s = true)
    (he : a.shape.subst ρ = s) : PairRoot isSum a := by
  induction a with
  | var v => exact False.elim (hz.names v he)
  | prod a b =>
    cases isSum
    · exact .prod a b
    · rw [← he] at hr
      simp [CompareTy.shape, ComparisonShape.subst, pairHead] at hr
  | sum a b =>
    cases isSum
    · rw [← he] at hr
      simp [CompareTy.shape, ComparisonShape.subst, pairHead] at hr
    · exact .sum a b
  | modal a m ih => exact .modal (ih hs he)
  | join a b ih₁ ih₂ =>
    exact .join (ih₁ hs.1 he) (ih₂ hs.2.1 ((hs.2.2 ρ hz.models).symm.trans he))
  | meet a b ih₁ ih₂ =>
    exact .meet (ih₁ hs.1 he) (ih₂ hs.2.1 ((hs.2.2 ρ hz.models).symm.trans he))
  | unit | credit | fn =>
    rw [← he] at hr
    cases isSum <;> simp [CompareTy.shape, ComparisonShape.subst, pairHead] at hr


theorem shaped_pairChild {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) {isSum : Bool}
    (hr : pairHead isSum s = true) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) (he : a.shape.subst ρ = s) (right : Bool) :
    AlgebraSubtype Δ (pairChild right a) (pairChild right b) := by
  have ha := pairRoot_of_resolved hz h.wellShaped_left isSum hr he
  induction h with
  | refl hs => exact .refl (pairChild_shaped ha hs right)
  | trans h₁ h₂ ih₁ ih₂ =>
    have he' := (h₁.shape_equivalent ρ hz.models).symm.trans he
    exact (ih₁ he ha).trans
      (ih₂ he' (pairRoot_of_resolved hz h₁.wellShaped_right isSum hr he'))
  | bound hb => exact False.elim (hz.bounds hb he)
  | identity hs => exact .shaped (.identity (pairChild_shaped ha.modal_inv hs right))
  | identityRev hs => exact .shaped (.identityRev (pairChild_shaped ha hs right))
  | compose hs => exact .shaped (.compose (pairChild_shaped ha.modal_inv.modal_inv hs right))
  | composeRev hs => exact .shaped (.composeRev (pairChild_shaped ha.modal_inv hs right))
  | congr h hm ih => exact .congr (ih he ha.modal_inv) hm
  | prod h₁ h₂ ih₁ ih₂ => cases right <;> first | exact .shaped h₁ | exact .shaped h₂
  | sum h₁ h₂ ih₁ ih₂ => cases right <;> first | exact .shaped h₁ | exact .shaped h₂
  | fn hca hbd hm ih₁ ih₂ => cases ha.modal_inv
  | joinLeft hs =>
    have he' := (hs.2.2 ρ hz.models).symm.trans he
    have hb := pairRoot_of_resolved hz hs.2.1 isSum hr he'
    exact .shaped (.joinLeft (pairChild_shaped (.join ha hb) hs right))
  | joinRight hs =>
    have he' := (hs.2.2 ρ hz.models).trans he
    have hb := pairRoot_of_resolved hz hs.1 isSum hr he'
    exact .shaped (.joinRight (pairChild_shaped (.join hb ha) hs right))
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hh := ha.typeOp_inv (p := true)
    have he' := ((h₁.shape_equivalent.trans h₂.shape_equivalent.symm) ρ hz.models).symm.trans he
    exact .joinLeast (ih₁ he hh.1) (ih₂ he' hh.2)
  | meetLeft hs => exact .shaped (.meetLeft (pairChild_shaped ha hs right))
  | meetRight hs => exact .shaped (.meetRight (pairChild_shaped ha hs right))
  | meetGreatest h₁ h₂ ih₁ ih₂ => exact .meetGreatest (ih₁ he ha) (ih₂ he ha)


/-- Structural projection only requires the particular resolved root to be
absent from names and declared edges; other shapes may have structural bounds. -/
theorem algebra_pairChild {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) {isSum : Bool}
    (hr : pairHead isSum s = true) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (he : a.shape.subst ρ = s) (right : Bool) :
    AlgebraSubtype Δ (pairChild right a) (pairChild right b) := by
  have ha := pairRoot_of_resolved hz h.wellShaped_left isSum hr he
  induction h with
  | shaped h => exact shaped_pairChild hz hr h he right
  | trans h₁ h₂ ih₁ ih₂ =>
    have he' := (h₁.shape_equivalent ρ hz.models).symm.trans he
    exact (ih₁ he ha).trans
      (ih₂ he' (pairRoot_of_resolved hz h₁.wellShaped_right isSum hr he'))
  | equation h => exact (pairChild_equation h ha right).1
  | @equationRev a b h =>
    have he' : a.shape.subst ρ = s := by rw [h.shape_eq]; exact he
    have hr' := pairRoot_of_resolved hz h.wellShaped.1 isSum hr he'
    exact (pairChild_equation h hr' right).2
  | congr h hm ih => exact .congr (ih he ha.modal_inv) hm
  | prod h₁ h₂ ih₁ ih₂ => cases right <;> first | exact h₁ | exact h₂
  | sum h₁ h₂ ih₁ ih₂ => cases right <;> first | exact h₁ | exact h₂
  | fn hca hbd hm ih₁ ih₂ => cases ha.modal_inv
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hh := ha.typeOp_inv (p := true)
    have he' := ((h₁.shape_equivalent.trans h₂.shape_equivalent.symm) ρ hz.models).symm.trans he
    exact .joinLeast (ih₁ he hh.1) (ih₂ he' hh.2)
  | meetGreatest h₁ h₂ ih₁ ih₂ => exact .meetGreatest (ih₁ he ha) (ih₂ he ha)
  | @clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have ar := ha.modal_inv
    have heb := (h₁.shape_equivalent ρ hz.models).trans he
    have het := (h₂.shape_equivalent ρ hz.models).symm.trans he
    have br := pairRoot_of_resolved hz h₁.wellShaped_left isSum hr heb
    have tr := pairRoot_of_resolved hz h₂.wellShaped_right isSum hr het
    exact .clamp (pairChild_compatible br ar hba right)
      (pairChild_compatible ar tr hat right) hm (ih₁ heb br) (ih₂ he ar)
  | @clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have ar := pairRoot_of_resolved hz hba.1.2.1 isSum hr he
    have heb := (h₁.shape_equivalent ρ hz.models).trans he
    have het := (h₂.shape_equivalent ρ hz.models).symm.trans he
    have br := pairRoot_of_resolved hz h₁.wellShaped_left isSum hr heb
    have tr := pairRoot_of_resolved hz h₂.wellShaped_right isSum hr het
    exact .clampRev (pairChild_compatible br ar hba right)
      (pairChild_compatible ar tr hat right) hm (ih₁ heb br) (ih₂ he ar)


theorem functionRoot_of_resolved {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) {a : CompareTy}
    (hs : a.WellShaped Δ) (hr : fnHead s = true)
    (he : a.shape.subst ρ = s) : FunctionRoot a := by
  induction a with
  | var v => exact False.elim (hz.names v he)
  | fn a b => exact .fn a b
  | modal a m ih => exact .modal (ih hs he)
  | join a b ih₁ ih₂ =>
    exact .join (ih₁ hs.1 he) (ih₂ hs.2.1 ((hs.2.2 ρ hz.models).symm.trans he))
  | meet a b ih₁ ih₂ =>
    exact .meet (ih₁ hs.1 he) (ih₂ hs.2.1 ((hs.2.2 ρ hz.models).symm.trans he))
  | unit | credit | prod | sum =>
    rw [← he] at hr
    simp [CompareTy.shape, ComparisonShape.subst, fnHead] at hr

theorem shaped_fnChild {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) (hr : fnHead s = true) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) (he : a.shape.subst ρ = s) (contra : Bool) :
    Rel Δ contra (fnChild contra a) (fnChild contra b) := by
  have ha := functionRoot_of_resolved hz h.wellShaped_left hr he
  induction h with
  | refl hs => exact Rel.refl contra (fnChild_shaped ha hs contra)
  | trans h₁ h₂ ih₁ ih₂ =>
    have he' := (h₁.shape_equivalent ρ hz.models).symm.trans he
    exact (ih₁ he ha).trans
      (ih₂ he' (functionRoot_of_resolved hz h₁.wellShaped_right hr he'))
  | bound hb => exact False.elim (hz.bounds hb he)
  | identity hs => exact Rel.refl contra (fnChild_shaped ha.modal_inv hs contra)
  | identityRev hs => exact Rel.refl contra (fnChild_shaped ha hs contra)
  | compose hs => exact Rel.refl contra (fnChild_shaped ha.modal_inv.modal_inv hs contra)
  | composeRev hs => exact Rel.refl contra (fnChild_shaped ha.modal_inv hs contra)
  | congr h hm ih => exact ih he ha.modal_inv
  | prod h₁ h₂ ih₁ ih₂ => cases ha.modal_inv
  | sum h₁ h₂ ih₁ ih₂ => cases ha.modal_inv
  | fn hca hbd hm ih₁ ih₂ => cases contra <;> first | exact .shaped hca | exact .shaped hbd
  | joinLeft hs =>
    have he' := (hs.2.2 ρ hz.models).symm.trans he
    have hb := functionRoot_of_resolved hz hs.2.1 hr he'
    have hp := fnChild_shaped (.join ha hb) hs contra
    cases contra
    · exact .shaped (.joinLeft hp)
    · exact .shaped (.meetLeft hp)
  | joinRight hs =>
    have he' := (hs.2.2 ρ hz.models).trans he
    have hb := functionRoot_of_resolved hz hs.1 hr he'
    have hp := fnChild_shaped (.join hb ha) hs contra
    cases contra
    · exact .shaped (.joinRight hp)
    · exact .shaped (.meetRight hp)
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hh := ha.typeOp_inv (p := true)
    have he' := ((h₁.shape_equivalent.trans h₂.shape_equivalent.symm) ρ hz.models).symm.trans he
    have hp := ih₁ he hh.1
    have hq := ih₂ he' hh.2
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
    have hp := ih₁ he ha
    have hq := ih₂ he ha
    cases contra
    · exact .meetGreatest hp hq
    · exact .joinLeast hp hq


theorem algebra_fnChild {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hz : Zone Δ ρ s) (hr : fnHead s = true) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) (he : a.shape.subst ρ = s) (contra : Bool) :
    Rel Δ contra (fnChild contra a) (fnChild contra b) := by
  have ha := functionRoot_of_resolved hz h.wellShaped_left hr he
  induction h with
  | shaped h => exact shaped_fnChild hz hr h he contra
  | trans h₁ h₂ ih₁ ih₂ =>
    have he' := (h₁.shape_equivalent ρ hz.models).symm.trans he
    exact (ih₁ he ha).trans
      (ih₂ he' (functionRoot_of_resolved hz h₁.wellShaped_right hr he'))
  | equation h =>
    have he := fnChild_equation h ha contra
    cases contra
    · exact he.1
    · exact he.2
  | @equationRev a b h =>
    have he' : a.shape.subst ρ = s := by rw [h.shape_eq]; exact he
    have hr' := functionRoot_of_resolved hz h.wellShaped.1 hr he'
    have he := fnChild_equation h hr' contra
    cases contra
    · exact he.2
    · exact he.1
  | congr h hm ih => exact ih he ha.modal_inv
  | prod h₁ h₂ ih₁ ih₂ => cases ha.modal_inv
  | sum h₁ h₂ ih₁ ih₂ => cases ha.modal_inv
  | fn hca hbd hm ih₁ ih₂ => cases contra <;> first | exact hca | exact hbd
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    have hh := ha.typeOp_inv (p := true)
    have he' := ((h₁.shape_equivalent.trans h₂.shape_equivalent.symm) ρ hz.models).symm.trans he
    have hp := ih₁ he hh.1
    have hq := ih₂ he' hh.2
    cases contra
    · exact .joinLeast hp hq
    · exact .meetGreatest hp hq
  | meetGreatest h₁ h₂ ih₁ ih₂ =>
    have hp := ih₁ he ha
    have hq := ih₂ he ha
    cases contra
    · exact .meetGreatest hp hq
    · exact .joinLeast hp hq
  | @clamp b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have ar := ha.modal_inv
    have heb := (h₁.shape_equivalent ρ hz.models).trans he
    have br := functionRoot_of_resolved hz h₁.wellShaped_left hr heb
    have hp := fnChild_clamp contra (ih₁ heb br) (ih₂ he ar) m
    cases contra
    · exact hp.1
    · exact hp.2
  | @clampRev b a t m hba hat hm h₁ h₂ ih₁ ih₂ =>
    have ar := functionRoot_of_resolved hz hba.1.2.1 hr he
    have heb := (h₁.shape_equivalent ρ hz.models).trans he
    have br := functionRoot_of_resolved hz h₁.wellShaped_left hr heb
    have hp := fnChild_clamp contra (ih₁ heb br) (ih₂ he ar) m
    cases contra
    · exact hp.2
    · exact hp.1


end ModalityInference.ComparisonUnanchoredProjection
