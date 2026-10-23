import ModalityInference.Proofs.ComparisonObserverShadowConstructorRows
import ModalityInference.Proofs.ComparisonObserverShadowAnchorRows
import ModalityInference.Proofs.ComparisonRelativeIndexedRows

/-! Certified constructor shadow rows combine the entire defined range algebra
with the recorded head rows in finite indexed constructor tables. -/
namespace ModalityInference.ComparisonObserverShadowConstructorTables

open ComparisonRawHeadFiniteOrbits ComparisonRawHeadFiniteRows ComparisonFiniteControls
  ComparisonStructuralLayout ComparisonObserverHeadCuts ComparisonObserverShadowPresentation
  ComparisonObserverShadowActionRows ComparisonObserverShadowActions
  ComparisonObserverShadowConstructorRows ComparisonRelativeMixedRows

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
  {B : Boundary Δ} {names : List ModVar} {base : Nat}
  {extra : List (RawRow hn (assign hn B names base))}
  (R : Realization hn B names base extra)

def definedOp (k : Constructor) (m : Control Δ names)
    (a b : ComparisonObserverFiniteRange.Value R.machine) :
    ComparisonObserverFiniteRange.Value R.machine :=
  ComparisonFiniteControlRange.action R.modal R.range m
    (ComparisonObserverFiniteRange.op R.range k a b)

theorem lower_named {p : Point B names} {a : ComparisonObserverFiniteRange.Value R.machine}
    (ha : R.interval.lower p = some a) :
    LowerInhabited (Δ := Δ) (shape := .unit) p.term ∧
      a = ComparisonObserverFiniteRange.atom R.certified.range (shadowName base (p,false)) := by
  have hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term := by
    by_contra hp
    rw [R.lower_eq p,if_neg hp] at ha
    cases ha
  exact ⟨hp,by simpa only [R.lower_eq p,if_pos hp,Option.some.injEq] using ha.symm⟩

theorem upper_named {p : Point B names} {a : ComparisonObserverFiniteRange.Value R.machine}
    (ha : R.interval.upper p = some a) :
    UpperInhabited (Δ := Δ) (shape := .unit) p.term ∧
      a = ComparisonObserverFiniteRange.atom R.certified.range (shadowName base (p,true)) := by
  have hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term := by
    by_contra hp
    rw [R.upper_eq p,if_neg hp] at ha
    cases ha
  exact ⟨hp,by simpa only [R.upper_eq p,if_pos hp,Option.some.injEq] using ha.symm⟩

variable (hrows : ComparisonObserverShadowConstructorRows.rows hn B names base ⊆ extra)

include hrows

theorem fn_lower_shadow (m : Control Δ names) {p q r : Point B names}
    {a b : ComparisonObserverFiniteRange.Value R.machine} (hr : FnRow m p q r)
    (ha : R.interval.upper p = some a) (hb : R.interval.lower q = some b) :
    ∃ c, R.interval.lower r = some c ∧ definedOp R .fn m a b ≤ c := by
  obtain ⟨row,rfl,rfl,rfl⟩ := hr
  obtain ⟨hp,rfl⟩ := upper_named R ha
  obtain ⟨hq,rfl⟩ := lower_named R hb
  refine ⟨ComparisonObserverFiniteRange.atom R.certified.range
    (shadowName base (row.atOutput m,false)),
    (R.lower_eq _).trans (if_pos (fn_lower_inhabited hn row m hp hq)),?_⟩
  intro i
  change (R.machine i).action (expression m)
    (ComparisonObserverFiniteRange.op R.range .fn _ _ i).val ≤ _
  simpa only [ComparisonObserverFiniteRange.op_val,ComparisonObserverFiniteRange.atom_val,
    ComparisonObserverMachine.sign,Constructor.dual,Bool.true_and,if_true,
    lowerFnRow,RawRow.op_le,rawOp,CompareTy.ofTy,ComparisonObserverMachine.value]
    using R.extra_bound (hrows (fnRows_subset hn B names base
      (lowerFnRow_mem hn B names base row m hp hq))) i

theorem fn_upper_shadow (m : Control Δ names) {p q r : Point B names}
    {a b : ComparisonObserverFiniteRange.Value R.machine} (hr : FnRow m p q r)
    (ha : R.interval.lower p = some a) (hb : R.interval.upper q = some b) :
    ∃ c, R.interval.upper r = some c ∧ c ≤ definedOp R .fn m a b := by
  obtain ⟨row,rfl,rfl,rfl⟩ := hr
  obtain ⟨hp,rfl⟩ := lower_named R ha
  obtain ⟨hq,rfl⟩ := upper_named R hb
  refine ⟨ComparisonObserverFiniteRange.atom R.certified.range
    (shadowName base (row.atOutput m,true)),
    (R.upper_eq _).trans (if_pos (fn_upper_inhabited hn row m hp hq)),?_⟩
  intro i
  change _ ≤ (R.machine i).action (expression m)
    (ComparisonObserverFiniteRange.op R.range .fn _ _ i).val
  simpa only [ComparisonObserverFiniteRange.op_val,ComparisonObserverFiniteRange.atom_val,
    ComparisonObserverMachine.sign,Constructor.dual,Bool.true_and,if_true,
    upperFnRow,RawRow.le_op,rawOp,CompareTy.ofTy,ComparisonObserverMachine.value]
    using R.extra_bound (hrows (fnRows_subset hn B names base
      (upperFnRow_mem hn B names base row m hp hq))) i

theorem pair_lower_shadow {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (m : Control Δ names) {p q r : Point B names}
    {a b : ComparisonObserverFiniteRange.Value R.machine} (hr : PairRow k m p q r)
    (ha : R.interval.lower p = some a) (hb : R.interval.lower q = some b) :
    ∃ c, R.interval.lower r = some c ∧ definedOp R k m a b ≤ c := by
  obtain ⟨row,rfl,rfl,rfl⟩ := hr
  obtain ⟨hp,rfl⟩ := lower_named R ha
  obtain ⟨hq,rfl⟩ := lower_named R hb
  refine ⟨ComparisonObserverFiniteRange.atom R.certified.range
    (shadowName base (row.atOutput m,false)),
    (R.lower_eq _).trans (if_pos (pair_lower_inhabited hn hk row m hp hq)),?_⟩
  intro i
  change (R.machine i).action (expression m)
    (ComparisonObserverFiniteRange.op R.range k _ _ i).val ≤ _
  have h := R.extra_bound (hrows (pairRows_subset hn B names base hk
    (lowerPairRow_mem hn B names base hk row m hp hq))) i
  rcases hk with rfl | rfl <;>
    simpa only [ComparisonObserverFiniteRange.op_val,ComparisonObserverFiniteRange.atom_val,
      ComparisonObserverMachine.sign,Constructor.dual,Bool.and_false,if_false,
      lowerPairRow,RawRow.op_le,rawOp,Constructor.kind,CompareTy.ofTy,
      ComparisonObserverMachine.value] using h

theorem pair_upper_shadow {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (m : Control Δ names) {p q r : Point B names}
    {a b : ComparisonObserverFiniteRange.Value R.machine} (hr : PairRow k m p q r)
    (ha : R.interval.upper p = some a) (hb : R.interval.upper q = some b) :
    ∃ c, R.interval.upper r = some c ∧ c ≤ definedOp R k m a b := by
  obtain ⟨row,rfl,rfl,rfl⟩ := hr
  obtain ⟨hp,rfl⟩ := upper_named R ha
  obtain ⟨hq,rfl⟩ := upper_named R hb
  refine ⟨ComparisonObserverFiniteRange.atom R.certified.range
    (shadowName base (row.atOutput m,true)),
    (R.upper_eq _).trans (if_pos (pair_upper_inhabited hn hk row m hp hq)),?_⟩
  intro i
  change _ ≤ (R.machine i).action (expression m)
    (ComparisonObserverFiniteRange.op R.range k _ _ i).val
  have h := R.extra_bound (hrows (pairRows_subset hn B names base hk
    (upperPairRow_mem hn B names base hk row m hp hq))) i
  rcases hk with rfl | rfl <;>
    simpa only [ComparisonObserverFiniteRange.op_val,ComparisonObserverFiniteRange.atom_val,
      ComparisonObserverMachine.sign,Constructor.dual,Bool.and_false,if_false,
      upperPairRow,RawRow.le_op,rawOp,Constructor.kind,CompareTy.ofTy,
      ComparisonObserverMachine.value] using h

theorem pair_compatible {k : Constructor} (hk : k = .prod ∨ k = .sum) :
    ComparisonRelativeIndexedRows.Compatibility R.interval false false (· ≤ ·)
      (definedOp R k) (PairRow k) where
  compatible m := {
    defined_mono := fun ha hb =>
      ComparisonObserverFiniteRange.modal_mono R.range R.modal (expression m) (expression_defined m)
        (ComparisonObserverFiniteRange.pair_mono R.range k hk ha hb)
    partial_mono := fun hr hs ha hb =>
      ComparisonRawHeadFiniteRows.pair_cross hk le_rfl hr hs ha hb
    lower_shadow := pair_lower_shadow R hrows hk m
    upper_shadow := pair_upper_shadow R hrows hk m
  }
  defined_index h a b := ComparisonFiniteControlRange.action_index R.modal R.range
    (ComparisonObserverFiniteRange.op R.range k a b) h
  boundary_cross h hr hs ha hb := ComparisonRawHeadFiniteRows.pair_cross hk h hr hs ha hb

theorem fn_compatible :
    ComparisonRelativeIndexedRows.Compatibility R.interval true false FutureLe
      (definedOp R .fn) FnRow where
  compatible m := {
    defined_mono := fun ha hb =>
      ComparisonObserverFiniteRange.modal_mono R.range R.modal (expression m) (expression_defined m)
        (ComparisonObserverFiniteRange.fn_mono R.range ha hb)
    partial_mono := fun hr hs ha hb =>
      ComparisonRawHeadFiniteRows.fn_cross (le_future_self m) hr hs ha hb
    lower_shadow := fn_lower_shadow R hrows m
    upper_shadow := fn_upper_shadow R hrows m
  }
  defined_index h a b :=
    ComparisonFiniteControlRange.action_fn_index R.modal R.range R.coherent h a b
  boundary_cross h hr hs ha hb := ComparisonRawHeadFiniteRows.fn_cross h hr hs ha hb

def pairTable {k : Constructor} (hk : k = .prod ∨ k = .sum) :
    ComparisonRelativeTables.IndexedTable R.interval.embed (Control Δ names) false false :=
  (pair_compatible R hrows hk).table (fun _ => le_rfl) (fun h₁ h₂ => h₁.trans h₂)

def fnTable :
    ComparisonRelativeTables.IndexedTable R.interval.embed (Control Δ names) true false :=
  (fn_compatible R hrows).table le_future_self FutureLe.trans

theorem pairTable_defined {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (m : Control Δ names) (a b : ComparisonObserverFiniteRange.Value R.machine) :
    (pairTable R hrows hk).extend m (R.interval.embed (.inl a)) (R.interval.embed (.inl b)) =
      R.interval.embed (.inl (definedOp R k m a b)) :=
  (pair_compatible R hrows hk).extend_defined (fun _ => le_rfl)
    (fun h₁ h₂ => h₁.trans h₂) m a b

theorem pairTable_boundary {k : Constructor} (hk : k = .prod ∨ k = .sum)
    {m : Control Δ names} {a b c : Point B names} (hr : PairRow k m a b c) :
    (pairTable R hrows hk).extend m (R.interval.embed (.inr a)) (R.interval.embed (.inr b)) =
      R.interval.embed (.inr c) :=
  (pair_compatible R hrows hk).extend_boundary (fun _ => le_rfl)
    (fun h₁ h₂ => h₁.trans h₂) hr

theorem fnTable_defined (m : Control Δ names)
    (a b : ComparisonObserverFiniteRange.Value R.machine) :
    (fnTable R hrows).extend m (R.interval.embed (.inl a)) (R.interval.embed (.inl b)) =
      R.interval.embed (.inl (definedOp R .fn m a b)) :=
  (fn_compatible R hrows).extend_defined le_future_self FutureLe.trans m a b

theorem fnTable_boundary {m : Control Δ names} {a b c : Point B names}
    (hr : FnRow m a b c) :
    (fnTable R hrows).extend m (R.interval.embed (.inr a)) (R.interval.embed (.inr b)) =
      R.interval.embed (.inr c) :=
  (fn_compatible R hrows).extend_boundary le_future_self FutureLe.trans hr

end
end ModalityInference.ComparisonObserverShadowConstructorTables
