import ModalityInference.Proofs.ComparisonObserverShadowEncoding

/-! Fresh shadow names preserve the interpretation of original raw anchors.
Both directions of a defined anchor equality can therefore be included among
the finite diagram's certified raw rows. -/
namespace ModalityInference.ComparisonObserverShadowPresentation

open ComparisonObserverRangeTransfer ComparisonObserverRangeProduct ComparisonObserverGluing
  ComparisonObserverRepresentatives ComparisonAlgebra ComparisonStructuralObservers

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)

def originalAssign (v : TypeVar) : ComparisonObserverRangeProduct.Value Δ :=
  ofType hn (.var v) (var_defined Δ v)

theorem original_value (a : Ty) (ha : a.DefinedUnder Δ) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn (originalAssign hn)) (.ofTy a) g =
      booleanValue g.observer (.ofTy a) := by
  induction a generalizing g with
  | var v => exact ofType_val hn (.var v) (var_defined Δ v) g
  | unit => exact data_represents hn g _ ((CompareTy.definedUnder_ofTy _ _).mpr ha)
  | credit => exact data_represents hn g _ ((CompareTy.definedUnder_ofTy _ _).mpr ha)
  | prod a b iha ihb =>
    have hab := CompareTy.definedUnder_prod_iff.mp ((CompareTy.definedUnder_ofTy _ _).mpr ha)
    have ea := iha ((CompareTy.definedUnder_ofTy _ _).mp hab.1)
    have eb := ihb ((CompareTy.definedUnder_ofTy _ _).mp hab.2)
    calc
      _ = (data hn g).value (.prod (.ofTy a) (.ofTy b)) := by
        simp only [CompareTy.ofTy,ComparisonObserverMachine.value,nodes,
          ComparisonStructuralLayout.Constructor.kind,Data.value,Branch.value,
          ComparisonStructuralObservers.leftSign,ea,eb]
      _ = _ := data_represents hn g _ ((CompareTy.definedUnder_ofTy _ _).mpr ha)
  | sum a b iha ihb =>
    have hab := CompareTy.definedUnder_sum_iff.mp ((CompareTy.definedUnder_ofTy _ _).mpr ha)
    have ea := iha ((CompareTy.definedUnder_ofTy _ _).mp hab.1)
    have eb := ihb ((CompareTy.definedUnder_ofTy _ _).mp hab.2)
    calc
      _ = (data hn g).value (.sum (.ofTy a) (.ofTy b)) := by
        simp only [CompareTy.ofTy,ComparisonObserverMachine.value,nodes,
          ComparisonStructuralLayout.Constructor.kind,Data.value,Branch.value,
          ComparisonStructuralObservers.leftSign,ea,eb]
      _ = _ := data_represents hn g _ ((CompareTy.definedUnder_ofTy _ _).mpr ha)
  | fn a b iha ihb =>
    have hab := CompareTy.definedUnder_fn_iff.mp ((CompareTy.definedUnder_ofTy _ _).mpr ha)
    have ea := iha ((CompareTy.definedUnder_ofTy _ _).mp hab.1)
    have eb := ihb ((CompareTy.definedUnder_ofTy _ _).mp hab.2)
    calc
      _ = (data hn g).value (.fn (.ofTy a) (.ofTy b)) := by
        simp only [CompareTy.ofTy,ComparisonObserverMachine.value,nodes,
          ComparisonStructuralLayout.Constructor.kind,Data.value,Branch.value,
          ComparisonStructuralObservers.leftSign,ea,eb]
      _ = _ := data_represents hn g _ ((CompareTy.definedUnder_ofTy _ _).mpr ha)
  | modal a m ih =>
    have ham := CompareTy.definedUnder_modal_iff.mp ((CompareTy.definedUnder_ofTy _ _).mpr ha)
    change g.transition.apply m _ = _
    rw [ih ((CompareTy.definedUnder_ofTy _ _).mp ham.1)]
    exact g.action m ham.2 _ (representable hn ham.1)

theorem value_assign_congr (assign other : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (a : Ty) (heq : ∀ v ∈ a.typeVars, assign v = other v) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn assign) (.ofTy a) g =
      ComparisonObserverMachine.value (nodes hn other) (.ofTy a) g := by
  induction a generalizing g with
  | var v => exact congrArg (fun x => (x g).val) (heq v (by simp [TypeExpr.typeVars]))
  | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    have ea := iha (fun v hv => heq v (Finset.mem_union_left _ hv))
    have eb := ihb (fun v hv => heq v (Finset.mem_union_right _ hv))
    simp only [CompareTy.ofTy,ComparisonObserverMachine.value,nodes,ea,eb]
  | modal a m ih =>
    exact congrArg (g.transition.apply m) (ih heq g)

variable {P : Type*} [Preorder P] [Fintype P]
    (I : ComparisonRelativeIntervals.IntervalData (ComparisonObserverRangeProduct.Value Δ) P)

theorem fresh_anchor_value (base : Nat) (a : Ty) (ha : a.DefinedUnder Δ)
    (hfresh : ∀ v ∈ a.typeVars, v.index < base) (g : Child Δ) :
    ComparisonObserverMachine.value (nodes hn (shadowAssign I (originalAssign hn) base)) (.ofTy a) g =
      (ofType hn (.ofTy a) ((CompareTy.definedUnder_ofTy _ _).mpr ha) g).val := by
  rw [ofType_val]
  exact (value_assign_congr hn _ _ a
    (fun v hv => shadowAssign_fresh I (originalAssign hn) base v (hfresh v hv)) g).trans
      (original_value hn a ha g)

omit I in
theorem head_anchor_lower (term : P → CompareTy)
    (horder : ∀ p q, p ≤ q ↔ AlgebraSubtype Δ (term p) (term q))
    (base : Nat) (p : P) (a : Ty) (ha : a.DefinedUnder Δ) (ht : term p = .ofTy a) :
    shadowAssign (headIntervals term horder) (originalAssign hn) base (shadowName base (p,false)) =
      ofType hn (.ofTy a) ((CompareTy.definedUnder_ofTy _ _).mpr ha) := by
  let c := represented (representable hn ((CompareTy.definedUnder_ofTy _ _).mpr ha))
  have hp : ComparisonObserverHeadCuts.LowerInhabited (Δ := Δ) (shape := .unit) (term p) := by
    rw [ht]
    exact ⟨c,.refl c.shaped⟩
  rw [named_head_lower term horder (originalAssign hn) base p hp]
  have h := ComparisonObserverShadowRows.lower_defined c
  apply ComparisonObserverRangeProduct.value_ext
  intro g
  change ComparisonObserverHeadCuts.lowerBit (term p) g.observer = (embed c g).val
  rw [ht]
  exact congrArg (fun x => (x g).val) h

omit I in
theorem head_anchor_upper (term : P → CompareTy)
    (horder : ∀ p q, p ≤ q ↔ AlgebraSubtype Δ (term p) (term q))
    (base : Nat) (p : P) (a : Ty) (ha : a.DefinedUnder Δ) (ht : term p = .ofTy a) :
    shadowAssign (headIntervals term horder) (originalAssign hn) base (shadowName base (p,true)) =
      ofType hn (.ofTy a) ((CompareTy.definedUnder_ofTy _ _).mpr ha) := by
  let c := represented (representable hn ((CompareTy.definedUnder_ofTy _ _).mpr ha))
  have hp : ComparisonObserverHeadCuts.UpperInhabited (Δ := Δ) (shape := .unit) (term p) := by
    rw [ht]
    exact ⟨c,.refl c.shaped⟩
  rw [named_head_upper term horder (originalAssign hn) base p hp]
  have h := ComparisonObserverShadowRows.upper_defined c
  apply ComparisonObserverRangeProduct.value_ext
  intro g
  change ComparisonObserverHeadCuts.upperBit (term p) g.observer = (embed c g).val
  rw [ht]
  exact congrArg (fun x => (x g).val) h

def anchor_le (base : Nat) (a : Ty) (ha : a.DefinedUnder Δ)
    (hfresh : ∀ v ∈ a.typeVars, v.index < base) (v : TypeVar)
    (h : shadowAssign I (originalAssign hn) base v =
      ofType hn (.ofTy a) ((CompareTy.definedUnder_ofTy _ _).mpr ha)) :
    RawRow hn (shadowAssign I (originalAssign hn) base) where
  pair := (a,.var v)
  defined := ⟨ha,raw_var_defined Δ v⟩
  sound g := by
    rw [fresh_anchor_value hn I base a ha hfresh g]
    change _ ≤ (shadowAssign I (originalAssign hn) base v g).val
    rw [h]

def le_anchor (base : Nat) (a : Ty) (ha : a.DefinedUnder Δ)
    (hfresh : ∀ v ∈ a.typeVars, v.index < base) (v : TypeVar)
    (h : shadowAssign I (originalAssign hn) base v =
      ofType hn (.ofTy a) ((CompareTy.definedUnder_ofTy _ _).mpr ha)) :
    RawRow hn (shadowAssign I (originalAssign hn) base) where
  pair := (.var v,a)
  defined := ⟨raw_var_defined Δ v,ha⟩
  sound g := by
    rw [fresh_anchor_value hn I base a ha hfresh g]
    change (shadowAssign I (originalAssign hn) base v g).val ≤ _
    rw [h]

omit I in
/-- A finite family of original heads, with any finite collection of the
sound raw rows above, has a finite optional-cut diagram preserving its
original boundary order. All cut-presence flags are retained exactly. -/
theorem finite_head_diagram (term : P → CompareTy)
    (horder : ∀ p q, p ≤ q ↔ AlgebraSubtype Δ (term p) (term q)) (base : Nat)
    (rs : List (RawRow hn (shadowAssign (headIntervals term horder) (originalAssign hn) base))) :
    let source := headIntervals term horder
    let assign := shadowAssign source (originalAssign hn) base
    let S := named source (originalAssign hn) base
    let rows := orderRows assign S.shadowVars ++ RawRow.rows hn assign rs
    ∃ count ≤ ComparisonObserverBoundary.sizeBound (context Δ rows) (S.shadowVars.map CompareTy.var),
      ∃ machine : ComparisonObserverMachine.Machine count,
        ∃ hc : ComparisonObserverMachine.Certified (context Δ rows) machine,
        ∃ J : ComparisonRelativeIntervals.IntervalData (ComparisonObserverFiniteRange.Value machine) P,
          (∀ p, J.lower p = if ComparisonObserverHeadCuts.LowerInhabited (Δ := Δ) (shape := .unit) (term p)
            then some (ComparisonObserverFiniteRange.atom hc.range (shadowName base (p,false))) else none) ∧
          (∀ p, J.upper p = if ComparisonObserverHeadCuts.UpperInhabited (Δ := Δ) (shape := .unit) (term p)
            then some (ComparisonObserverFiniteRange.atom hc.range (shadowName base (p,true))) else none) := by
  classical
  dsimp only
  let source := headIntervals term horder
  let assign := shadowAssign source (originalAssign hn) base
  let S := named source (originalAssign hn) base
  obtain ⟨count,hcount,machine,hc,J,hlo,hup,_⟩ := S.finite_realization hn
    (RawRow.rows hn assign rs) (RawRow.rows_defined hn assign rs) (RawRow.rows_sound hn assign rs)
  refine ⟨count,hcount,machine,hc,J,?_,?_⟩
  · intro p
    rw [hlo p]
    dsimp [S,named,source,headIntervals]
    split <;> rfl
  · intro p
    rw [hup p]
    dsimp [S,named,source,headIntervals]
    split <;> rfl

end
end ModalityInference.ComparisonObserverShadowPresentation
