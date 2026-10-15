import ModalityInference.Proofs.ComparisonRootProjection

namespace ModalityInference.ComparisonSkeletonCoordinates

open ComparisonAlgebra ComparisonStructuralProjection

namespace Normalization

theorem pairRoot {Δ : Bounds} (hΔ : Residual Δ) {a : CompareTy} (hs : a.WellShaped Δ)
    (isSum : Bool) {s t : ComparisonShape}
    (he : ComparisonShape.Equivalent Δ a.shape
      ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t)) : PairRoot isSum a := by
  apply PairRoot.of_head hΔ hs isSum
  have hh := pairHead_equivalent hΔ he isSum
  cases isSum <;> exact hh

theorem pairShapes {Δ : Bounds} {a : CompareTy} {isSum : Bool} (ha : PairRoot isSum a)
    {s t : ComparisonShape}
    (he : ComparisonShape.Equivalent Δ a.shape
      ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t)) :
    ComparisonShape.Equivalent Δ (pairChild false a).shape s ∧
      ComparisonShape.Equivalent Δ (pairChild true a).shape t := by
  constructor <;> intro ρ hρ <;> have hh := he ρ hρ
  all_goals rw [pairChild_shape ha] at hh
  all_goals cases isSum
  all_goals first
    | exact (ComparisonShape.prod.inj hh).1
    | exact (ComparisonShape.prod.inj hh).2
    | exact (ComparisonShape.sum.inj hh).1
    | exact (ComparisonShape.sum.inj hh).2

theorem fnRoot {Δ : Bounds} (hΔ : Residual Δ) {a : CompareTy} (hs : a.WellShaped Δ)
    {s t : ComparisonShape} (he : ComparisonShape.Equivalent Δ a.shape (.fn s t)) : FunctionRoot a :=
  FunctionRoot.of_head hΔ hs (head_equivalent hΔ he)

theorem fnShapes {Δ : Bounds} {a : CompareTy} (ha : FunctionRoot a)
    {s t : ComparisonShape} (he : ComparisonShape.Equivalent Δ a.shape (.fn s t)) :
    ComparisonShape.Equivalent Δ (fnChild true a).shape s ∧
      ComparisonShape.Equivalent Δ (fnChild false a).shape t := by
  constructor <;> intro ρ hρ <;> have hh := he ρ hρ
  all_goals rw [fnChild_shape ha] at hh
  · exact (ComparisonShape.fn.inj hh).1
  · exact (ComparisonShape.fn.inj hh).2

end Normalization

/-- Normalize a defined internal witness at a compatible structural shape.
Opaque leaves remain genuine algebraic types; each structural coordinate is
an explicit expression extracted from the original witness. -/
def normalize {Δ : Bounds} (hΔ : Residual Δ) :
    (s : ComparisonShape) → (a : CompareTy) → a.WellShaped Δ → a.DefinedUnder Δ →
      ComparisonShape.Equivalent Δ a.shape s → Tree Δ s
  | .var _, a, hs, hd, he => .atom ⟨a, hs, hd, he⟩
  | .unit, a, _, hd, _ => .unit (rootGuarded a hd)
  | .credit, a, _, hd, _ => .credit (rootGuarded a hd)
  | .prod s t, a, hs, hd, he =>
    let hr := Normalization.pairRoot hΔ hs false he
    let hh := Normalization.pairShapes hr he
    .prod (normalize hΔ s (pairChild false a) (pairChild_shaped hr hs false)
        (pairChild_defined hr hd false) hh.1)
      (normalize hΔ t (pairChild true a) (pairChild_shaped hr hs true)
        (pairChild_defined hr hd true) hh.2) (rootGuarded a hd)
  | .sum s t, a, hs, hd, he =>
    let hr := Normalization.pairRoot hΔ hs true he
    let hh := Normalization.pairShapes hr he
    .sum (normalize hΔ s (pairChild false a) (pairChild_shaped hr hs false)
        (pairChild_defined hr hd false) hh.1)
      (normalize hΔ t (pairChild true a) (pairChild_shaped hr hs true)
        (pairChild_defined hr hd true) hh.2) (rootGuarded a hd)
  | .fn s t, a, hs, hd, he =>
    let hr := Normalization.fnRoot hΔ hs he
    let hh := Normalization.fnShapes hr he
    .fn (normalize hΔ s (fnChild true a) (fnChild_shaped hr hs true)
        (fnChild_defined hr hd true) hh.1)
      (normalize hΔ t (fnChild false a) (fnChild_shaped hr hs false)
        (fnChild_defined hr hd false) hh.2) (rootGuarded a hd)

/-- One normalization preserves every algebraic comparison simultaneously.
Only its endpoints must be defined; the derivation may use arbitrary partial
intermediates. -/
theorem normalize_le {Δ : Bounds} (hΔ : Residual Δ) {s : ComparisonShape}
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ a b) (ea : ComparisonShape.Equivalent Δ a.shape s)
    (eb : ComparisonShape.Equivalent Δ b.shape s) :
    Tree.Le (normalize hΔ s a h.wellShaped_left ha ea)
      (normalize hΔ s b h.wellShaped_right hb eb) := by
  induction s generalizing a b with
  | var v => exact h
  | unit =>
    apply rootGuarded_le hΔ h ha hb
    · exact (rootTag_equivalent hΔ ea) ▸ (by decide : rootTag ComparisonShape.unit ≠ 0)
    · exact (rootTag_equivalent hΔ ea) ▸ (by decide : rootTag ComparisonShape.unit ≠ 5)
  | credit =>
    apply rootGuarded_le hΔ h ha hb
    · exact (rootTag_equivalent hΔ ea) ▸ (by decide : rootTag ComparisonShape.credit ≠ 0)
    · exact (rootTag_equivalent hΔ ea) ▸ (by decide : rootTag ComparisonShape.credit ≠ 5)
  | prod s t ih₁ ih₂ | sum s t ih₁ ih₂ =>
    dsimp only [normalize, Tree.Le]
    refine ⟨?_, ?_, ?_⟩
    · apply ih₁
      first
      | exact algebra_pairChild hΔ h (Normalization.pairRoot hΔ h.wellShaped_left false ea) false
      | exact algebra_pairChild hΔ h (Normalization.pairRoot hΔ h.wellShaped_left true ea) false
    · apply ih₂
      first
      | exact algebra_pairChild hΔ h (Normalization.pairRoot hΔ h.wellShaped_left false ea) true
      | exact algebra_pairChild hΔ h (Normalization.pairRoot hΔ h.wellShaped_left true ea) true
    · apply rootGuarded_le hΔ h ha hb
      all_goals rw [rootTag_equivalent hΔ ea]
      all_goals simp only [rootTag]; decide
  | fn s t ih₁ ih₂ =>
    dsimp only [normalize, Tree.Le]
    refine ⟨?_, ?_, ?_⟩
    · apply ih₁
      exact algebra_fnChild hΔ h (Normalization.fnRoot hΔ h.wellShaped_left ea) true
    · apply ih₂
      exact algebra_fnChild hΔ h (Normalization.fnRoot hΔ h.wellShaped_left ea) false
    · exact rootGuarded_futureLe hΔ h ha hb (rootTag_equivalent hΔ ea)


theorem rootGuarded_modal {Δ : Bounds} (a : CompareTy) (hd : a.DefinedUnder Δ)
    (m : GuardedMode Δ) :
    Scalar.equivalent
      (rootGuarded (.modal a m.expression) (CompareTy.definedUnder_modal_iff.mpr ⟨hd, m.defined⟩))
      (Scalar.compose (rootGuarded a hd) m) := by
  constructor <;> intro η hη
  all_goals dsimp only [rootGuarded, rootValue, rootExpr, ModExpr.complete, Scalar.compose]
  all_goals rw [ModExpr.complete_of_eval (m.eval η hη)]; exact Mode.le_refl _

theorem rootGuarded_modal_future {Δ : Bounds} (a : CompareTy) (hd : a.DefinedUnder Δ)
    (m : GuardedMode Δ) :
    Scalar.futureEquivalent
      (rootGuarded (.modal a m.expression) (CompareTy.definedUnder_modal_iff.mpr ⟨hd, m.defined⟩))
      (Scalar.compose (rootGuarded a hd) m) :=
  ⟨fun η hη => Mode.compose_le_right Mode.top ((rootGuarded_modal a hd m).1 η hη),
   fun η hη => Mode.compose_le_right Mode.top ((rootGuarded_modal a hd m).2 η hη)⟩

/-- Normalization commutes with every certified-total inherited action. -/
theorem normalize_modal {Δ : Bounds} (hΔ : Residual Δ) (s : ComparisonShape)
    (a : CompareTy) (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (he : ComparisonShape.Equivalent Δ a.shape s) (m : GuardedMode Δ) :
    Tree.Equivalent
      (normalize hΔ s (.modal a m.expression) hs
        (CompareTy.definedUnder_modal_iff.mpr ⟨hd, m.defined⟩) he)
      (Tree.modal m (normalize hΔ s a hs hd he)) := by
  induction s generalizing a with
  | var v => exact ⟨AlgebraSubtype.refl hs, AlgebraSubtype.refl hs⟩
  | unit | credit => exact rootGuarded_modal a hd m
  | prod s t ih₁ ih₂ =>
    have hp := Normalization.pairRoot hΔ hs false he
    have hl := ih₁ (pairChild false a) (pairChild_shaped hp hs false)
      (pairChild_defined hp hd false) (Normalization.pairShapes hp he).1
    have hr := ih₂ (pairChild true a) (pairChild_shaped hp hs true)
      (pairChild_defined hp hd true) (Normalization.pairShapes hp he).2
    exact ⟨⟨hl.1, hr.1, (rootGuarded_modal a hd m).1⟩,
      ⟨hl.2, hr.2, (rootGuarded_modal a hd m).2⟩⟩
  | sum s t ih₁ ih₂ =>
    have hp := Normalization.pairRoot hΔ hs true he
    have hl := ih₁ (pairChild false a) (pairChild_shaped hp hs false)
      (pairChild_defined hp hd false) (Normalization.pairShapes hp he).1
    have hr := ih₂ (pairChild true a) (pairChild_shaped hp hs true)
      (pairChild_defined hp hd true) (Normalization.pairShapes hp he).2
    exact ⟨⟨hl.1, hr.1, (rootGuarded_modal a hd m).1⟩,
      ⟨hl.2, hr.2, (rootGuarded_modal a hd m).2⟩⟩
  | fn s t ih₁ ih₂ =>
    exact ⟨⟨Tree.Le.refl _, Tree.Le.refl _, (rootGuarded_modal_future a hd m).1⟩,
      ⟨Tree.Le.refl _, Tree.Le.refl _, (rootGuarded_modal_future a hd m).2⟩⟩


/-- The retraction fixes every defined public type. -/
theorem normalize_public_correct {Δ : Bounds} (hΔ : Residual Δ) (a : Ty)
    (ha : (CompareTy.ofTy a).DefinedUnder Δ) :
    let tree := normalize hΔ (ComparisonShape.ofTy a) (.ofTy a)
      (CompareTy.wellShaped_ofTy a Δ) ha (by rw [CompareTy.shape_ofTy]; exact .refl)
    AlgebraSubtype Δ tree.reify (.ofTy a) ∧ AlgebraSubtype Δ (.ofTy a) tree.reify := by
  induction a with
  | var v => exact ⟨.refl trivial, .refl trivial⟩
  | unit | credit => exact ⟨.identity trivial, .identityRev trivial⟩
  | prod a b ih₁ ih₂ =>
    have h₁ := ih₁ (CompareTy.definedUnder_prod_iff.mp ha).1
    have h₂ := ih₂ (CompareTy.definedUnder_prod_iff.mp ha).2
    have he := Scalar.submode (Scalar.refl (Scalar.identity (Δ := Δ)))
    exact ⟨(AlgebraSubtype.prod (.congr h₁.1 he) (.congr h₂.1 he)).trans
      (.identity (CompareTy.wellShaped_ofTy (.prod a b) Δ)),
      (AlgebraSubtype.identityRev (CompareTy.wellShaped_ofTy (.prod a b) Δ)).trans
        (.prod (.congr h₁.2 he) (.congr h₂.2 he))⟩
  | sum a b ih₁ ih₂ =>
    have h₁ := ih₁ (CompareTy.definedUnder_sum_iff.mp ha).1
    have h₂ := ih₂ (CompareTy.definedUnder_sum_iff.mp ha).2
    have he := Scalar.submode (Scalar.refl (Scalar.identity (Δ := Δ)))
    exact ⟨(AlgebraSubtype.sum (.congr h₁.1 he) (.congr h₂.1 he)).trans
      (.identity (CompareTy.wellShaped_ofTy (.sum a b) Δ)),
      (AlgebraSubtype.identityRev (CompareTy.wellShaped_ofTy (.sum a b) Δ)).trans
        (.sum (.congr h₁.2 he) (.congr h₂.2 he))⟩
  | fn a b ih₁ ih₂ =>
    have h₁ := ih₁ (CompareTy.definedUnder_fn_iff.mp ha).1
    have h₂ := ih₂ (CompareTy.definedUnder_fn_iff.mp ha).2
    have he := Scalar.future_submode (Scalar.future_refl (Scalar.identity (Δ := Δ)))
    exact ⟨(AlgebraSubtype.fn h₁.2 h₂.1 he).trans
      (.identity (CompareTy.wellShaped_ofTy (.fn a b) Δ)),
      (AlgebraSubtype.identityRev (CompareTy.wellShaped_ofTy (.fn a b) Δ)).trans
        (.fn h₁.1 h₂.2 he)⟩
  | modal a m ih =>
    have hd := (CompareTy.definedUnder_modal_iff.mp ha).1
    have hm := (CompareTy.definedUnder_modal_iff.mp ha).2
    let mode := GuardedMode.ofDefined m hm
    let tree := normalize hΔ (ComparisonShape.ofTy a) (.ofTy a)
      (CompareTy.wellShaped_ofTy a Δ) hd (by rw [CompareTy.shape_ofTy]; exact .refl)
    have hn := normalize_modal hΔ (ComparisonShape.ofTy a) (.ofTy a)
      (CompareTy.wellShaped_ofTy a Δ) hd
      (by rw [CompareTy.shape_ofTy]; exact .refl) mode
    have hc := Tree.reify_modal tree mode
    have hh := ih hd
    have hs := Scalar.submode (Scalar.refl mode)
    exact ⟨(Tree.reify_le hn.1).trans (hc.1.trans (.congr hh.1 hs)),
      (AlgebraSubtype.congr hh.2 hs).trans (hc.2.trans (Tree.reify_le hn.2))⟩

end ModalityInference.ComparisonSkeletonCoordinates
