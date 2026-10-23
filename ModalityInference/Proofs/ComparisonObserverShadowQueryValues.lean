import ModalityInference.Proofs.ComparisonObserverShadowAnchors
import ModalityInference.Proofs.ComparisonFiniteControlRange

/-! Fresh shadow names leave arbitrary defined comparison queries unchanged,
including their internal joins and meets. Such queries need no raw equality
anchor: their observer patterns can be retained directly during extraction. -/
namespace ModalityInference.ComparisonObserverShadowQueryValues

open ComparisonObserverShadowPresentation ComparisonObserverRangeTransfer
  ComparisonObserverRangeProduct ComparisonObserverGluing ComparisonObserverRepresentatives
  ComparisonAlgebra ComparisonStructuralObservers ComparisonObserverBoundary

noncomputable section

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)

theorem original_value (a : CompareTy) (ha : a.DefinedUnder Δ) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn (originalAssign hn)) a g =
      booleanValue g.observer a := by
  induction a generalizing g with
  | var v => exact ofType_val hn (.var v) (var_defined Δ v) g
  | unit => exact data_represents hn g _ ha
  | credit => exact data_represents hn g _ ha
  | prod a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_prod_iff.mp ha
    calc
      _ = (data hn g).value (.prod a b) := by
        simp only [ComparisonObserverMachine.value,nodes,
          ComparisonStructuralLayout.Constructor.kind,Data.value,Branch.value,
          ComparisonStructuralObservers.leftSign,iha ha,ihb hb]
      _ = _ := data_represents hn g _ (CompareTy.definedUnder_prod_iff.mpr ⟨ha,hb⟩)
  | sum a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_sum_iff.mp ha
    calc
      _ = (data hn g).value (.sum a b) := by
        simp only [ComparisonObserverMachine.value,nodes,
          ComparisonStructuralLayout.Constructor.kind,Data.value,Branch.value,
          ComparisonStructuralObservers.leftSign,iha ha,ihb hb]
      _ = _ := data_represents hn g _ (CompareTy.definedUnder_sum_iff.mpr ⟨ha,hb⟩)
  | fn a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_fn_iff.mp ha
    calc
      _ = (data hn g).value (.fn a b) := by
        simp only [ComparisonObserverMachine.value,nodes,
          ComparisonStructuralLayout.Constructor.kind,Data.value,Branch.value,
          ComparisonStructuralObservers.leftSign,iha ha,ihb hb]
      _ = _ := data_represents hn g _ (CompareTy.definedUnder_fn_iff.mpr ⟨ha,hb⟩)
  | modal a m ih =>
    obtain ⟨ha,hm⟩ := CompareTy.definedUnder_modal_iff.mp ha
    change g.transition.apply m _ = _
    rw [ih ha]
    exact g.action m hm _ (representable hn ha)
  | join a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_join_iff.mp ha
    exact congrArg₂ (· || ·) (iha ha g) (ihb hb g)
  | meet a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_meet_iff.mp ha
    exact congrArg₂ (· && ·) (iha ha g) (ihb hb g)

theorem value_assign_congr (assign other : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (a : CompareTy) (heq : ∀ v ∈ types a, assign v = other v) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn assign) a g =
      ComparisonObserverMachine.value (nodes hn other) a g := by
  induction a generalizing g with
  | var v => exact congrArg (fun x => (x g).val) (heq v (Finset.mem_singleton_self v))
  | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb
  | join a b iha ihb | meet a b iha ihb =>
    have ea := iha (fun v hv => heq v (Finset.mem_union_left _ hv))
    have eb := ihb (fun v hv => heq v (Finset.mem_union_right _ hv))
    simp only [ComparisonObserverMachine.value,nodes,ea,eb]
  | modal a m ih => exact congrArg (g.transition.apply m) (ih heq g)

variable {P : Type*} [Preorder P] [Fintype P]
    (I : ComparisonRelativeIntervals.IntervalData (ComparisonObserverRangeProduct.Value Δ) P)

theorem fresh_value (base : Nat) (a : CompareTy) (ha : a.DefinedUnder Δ)
    (hfresh : ∀ v ∈ types a, v.index < base) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn (shadowAssign I (originalAssign hn) base)) a g =
      (ofType hn a ha g).val := by
  rw [ofType_val]
  exact (value_assign_congr hn _ _ a
    (fun v hv => shadowAssign_fresh I (originalAssign hn) base v (hfresh v hv)) g).trans
      (original_value hn a ha g)

omit hn I in
theorem modes_fixed {ms : ModVar → ModExpr} (a : CompareTy)
    (h : ∀ v ∈ modes a, ms v = .var v) : a.subst CompareTy.var ms = a := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb
  | join a b iha ihb | meet a b iha ihb =>
    simp only [modes,Finset.mem_union,or_imp,forall_and] at h
    simp only [CompareTy.subst,iha h.1,ihb h.2]
  | modal a m ih =>
    have hm : m.subst ms = m := by
      rw [ModExpr.subst_congr m (τ := ModExpr.var)
        (fun v hv => h v (Finset.mem_union_right _ hv))]
      exact ModExpr.subst_id m
    simp only [CompareTy.subst,hm,ih (fun v hv => h v (Finset.mem_union_left _ hv))]

omit hn I in
theorem evaluate_eq_eval {names : List ModVar} {State : Type}
    {ns : State → ComparisonObserverMachine.Node State}
    (hr : ComparisonObserverMachine.RangeClosed Δ ns) (hnames : Δ.modVars ⊆ names.toFinset)
    (a : CompareTy) (ha : a.DefinedUnder Δ) (hs : modes a ⊆ names.toFinset) :
    ComparisonFiniteControlRange.evaluate hr hnames a ha =
      ComparisonObserverFiniteRange.eval hr a ha :=
  ComparisonObserverFiniteRange.value_ext (fun i => congrArg
    (fun t => ComparisonObserverMachine.value ns t i)
    (modes_fixed a (fun v hv => by simp only [ComparisonModeRestriction.restrict,if_pos (hs hv)])))

end
end ModalityInference.ComparisonObserverShadowQueryValues
