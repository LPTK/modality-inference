import ModalityInference.Proofs.ComparisonObserverActions
import ModalityInference.Proofs.ComparisonDefinedRoot

/-! A structural root with genuine observers of its resolved child shapes
extends to an observer of the full root algebra. Whole declared bounds and
the guarded constructor action laws remain explicit. -/
namespace ModalityInference.ComparisonShapedObserverGluing

open ComparisonAlgebra ComparisonStructuralLattice ComparisonStructuralObservers
  ComparisonObserverActions

def leftShape : ComparisonShape → ComparisonShape
  | .prod a _ | .sum a _ | .fn a _ => a
  | _ => .unit

def rightShape : ComparisonShape → ComparisonShape
  | .prod _ b | .sum _ b | .fn _ b => b
  | _ => .unit

def Root (kind : Kind) (shape : ComparisonShape) : Prop :=
  shape=kind.shape (leftShape shape) (rightShape shape)

structure Child (Δ : Bounds) (shape : ComparisonShape) where
  observer : LatticeHom (Order Δ shape) Bool
  transition : Transition Δ
  action : ∀m, Entails Δ (.defined m) → ∀a, Representable Δ shape a →
    transition.apply m (booleanValue observer a)=booleanValue observer (.modal a m)

def Child.Range {Δ shape} (g : Child Δ shape) (x : Bool) : Prop :=
  ∃a : Carrier Δ shape, ComparisonAlgebra.observer g.observer a=x

abbrev Branch (Δ : Bounds) (shape : ComparisonShape) :=
  Child Δ (leftShape shape) ⊕ Child Δ (rightShape shape)

noncomputable def branchValue {Δ shape} (b : Branch Δ shape) (k : Kind) (a c : CompareTy) : Bool :=
  match b with
  | .inl g => leftSign k (booleanValue g.observer a)
  | .inr g => booleanValue g.observer c

def branchSign {Δ shape} (b : Branch Δ shape) (k : Kind) (x : Bool) : Bool :=
  match b with | .inl _ => leftSign k x | .inr _ => x

def branchRange {Δ shape} (b : Branch Δ shape) (x : Bool) : Prop :=
  match b with | .inl g => g.Range x | .inr g => g.Range x

def branchTransition {Δ shape} (b : Branch Δ shape) : Transition Δ :=
  match b with | .inl g => g.transition | .inr g => g.transition

structure Data (Δ : Bounds) (shape : ComparisonShape) where
  transition : Transition Δ
  atom : TypeVar → Bool
  unitValue : Bool
  creditValue : Bool
  branch : Kind → Branch Δ shape

noncomputable def Data.value {Δ shape} (d : Data Δ shape) : CompareTy → Bool
  | .var v => d.atom v
  | .unit => d.unitValue
  | .credit => d.creditValue
  | .prod a b => branchValue (d.branch .prod) .prod a b
  | .sum a b => branchValue (d.branch .sum) .sum a b
  | .fn a b => branchValue (d.branch .fn) .fn a b
  | .modal a m => d.transition.apply m (d.value a)
  | .join a b => d.value a || d.value b
  | .meet a b => d.value a && d.value b

structure Coherent {Δ shape} (d : Data Δ shape) : Prop where
  pair : ∀k, k=Kind.prod ∨ k=Kind.sum → Root k shape → ∀m,
    Entails Δ (.defined m) → ∀x, branchRange (d.branch k) x →
      d.transition.apply m ((branchTransition (d.branch k)).apply m x)=d.transition.apply m x
  fn : Root Kind.fn shape → ∀m n, Submode Δ m (.compose n .top) → ∀x,
    branchRange (d.branch .fn) x →
      d.transition.apply m (branchSign (d.branch .fn) .fn x) ≤
        d.transition.apply n (branchSign (d.branch .fn) .fn x)

def BoundsHold {Δ shape} (d : Data Δ shape) : Prop :=
  ∀a b, Constraint.sub a b∈Δ → ComparisonShape.Equivalent Δ (ComparisonShape.ofTy a) shape →
    d.value (.ofTy a)≤d.value (.ofTy b)

theorem Child.range_value {Δ shape} (g : Child Δ shape) {a : CompareTy}
    (ha : Representable Δ shape a) : g.Range (booleanValue g.observer a) :=
  ⟨represented ha,(booleanValue_represented g.observer a ha).symm⟩

theorem Child.value_mono {Δ shape} (g : Child Δ shape) {a b : CompareTy}
    (ha : Representable Δ shape a) (hb : Representable Δ shape b)
    (h : AlgebraSubtype Δ a b) : booleanValue g.observer a≤booleanValue g.observer b := by
  rw [booleanValue_represented g.observer a ha,booleanValue_represented g.observer b hb]
  exact OrderHomClass.monotone g.observer h

theorem branch_diagonal {Δ shape} (b : Branch Δ shape) (k : Kind) (p : Bool) (a c u v : CompareTy) :
    branchValue b k (typeOp (k.leftSign p) a c) (typeOp p u v)=
      if p then branchValue b k a u || branchValue b k c v
      else branchValue b k a u && branchValue b k c v := by
  cases b <;> cases k <;> cases p <;>
    simp [branchValue,typeOp,leftSign,Kind.leftSign]

theorem branch_pair_mono {Δ shape} (b : Branch Δ shape) {k : Kind}
    (hk : k=.prod ∨ k=.sum) {a c u v : CompareTy}
    (ha : Representable Δ (leftShape shape) a) (hc : Representable Δ (leftShape shape) c)
    (hu : Representable Δ (rightShape shape) u) (hv : Representable Δ (rightShape shape) v)
    (hac : AlgebraSubtype Δ a c) (huv : AlgebraSubtype Δ u v) :
    branchValue b k a u≤branchValue b k c v := by
  cases b with
  | inl g => rcases hk with rfl|rfl <;> exact g.value_mono ha hc hac
  | inr g => exact g.value_mono hu hv huv

theorem branch_fn_mono {Δ shape} (b : Branch Δ shape) {a c u v : CompareTy}
    (ha : Representable Δ (leftShape shape) a) (hc : Representable Δ (leftShape shape) c)
    (hu : Representable Δ (rightShape shape) u) (hv : Representable Δ (rightShape shape) v)
    (hca : AlgebraSubtype Δ c a) (huv : AlgebraSubtype Δ u v) :
    branchValue b .fn a u≤branchValue b .fn c v := by
  cases b with
  | inl g =>
    have hh := g.value_mono hc ha hca
    change (!booleanValue g.observer a)≤(!booleanValue g.observer c)
    cases ea : booleanValue g.observer a <;> cases ec : booleanValue g.observer c <;>
      simp_all [Bool.le_iff_imp]
  | inr g => exact g.value_mono hu hv huv

def Resolved (Δ : Bounds) (shape : ComparisonShape) : Prop :=
  ∀k a b, ComparisonShape.Equivalent Δ (k.shape a b) shape →
    Root k shape ∧ ComparisonShape.Equivalent Δ a (leftShape shape) ∧
      ComparisonShape.Equivalent Δ b (rightShape shape)

theorem resolved_of_normalizer {Δ shape} (φ : TypeVar → ComparisonShape)
    (he : ∀a b, ComparisonShape.Equivalent Δ a b ↔ a.subst φ=b.subst φ)
    (hf : shape.subst φ=shape) : Resolved Δ shape := by
  intro k a b hk
  have h := (he _ _).mp hk
  rw [hf] at h
  cases k <;> cases shape <;>
    simp only [Kind.shape, ComparisonShape.subst, ComparisonShape.prod.injEq,
      ComparisonShape.sum.injEq, ComparisonShape.fn.injEq] at h hf
  all_goals first | contradiction | skip
  all_goals
    rcases h with ⟨ha,hb⟩
    exact ⟨rfl,(he _ _).mpr (ha.trans hf.1.symm),(he _ _).mpr (hb.trans hf.2.symm)⟩

theorem Resolved.children {Δ shape} (hr : Resolved Δ shape) (k : Kind)
    {a b : CompareTy} (h : Representable Δ shape (k.op a b)) :
    Root k shape ∧ Representable Δ (leftShape shape) a ∧
      Representable Δ (rightShape shape) b := by
  have hs : ComparisonShape.Equivalent Δ (k.shape a.shape b.shape) shape := by
    cases k <;> exact h.2.2
  have hd : a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
    cases k
    · exact CompareTy.definedUnder_prod_iff.mp h.2.1
    · exact CompareTy.definedUnder_sum_iff.mp h.2.1
    · exact CompareTy.definedUnder_fn_iff.mp h.2.1
  have hw : a.WellShaped Δ ∧ b.WellShaped Δ := by cases k <;> exact h.1
  exact ⟨(hr k _ _ hs).1,⟨hw.1,hd.1,(hr k _ _ hs).2.1⟩,
    ⟨hw.2,hd.2,(hr k _ _ hs).2.2⟩⟩

theorem representable_modal {Δ shape a m} (ha : Representable Δ shape a)
    (hm : Entails Δ (.defined m)) : Representable Δ shape (.modal a m) :=
  ⟨ha.1,CompareTy.definedUnder_modal_iff.mpr ⟨ha.2.1,hm⟩,ha.2.2⟩

theorem Coherent.pair_action {Δ shape} {d : Data Δ shape} (h : Coherent d)
    {k : Kind} (hk : k=.prod ∨ k=.sum) (hr : Root k shape)
    {a b : CompareTy} (ha : Representable Δ (leftShape shape) a)
    (hb : Representable Δ (rightShape shape) b) {m} (hm : Entails Δ (.defined m)) :
    d.transition.apply m (branchValue (d.branch k) k a b)=
      d.transition.apply m (branchValue (d.branch k) k (.modal a m) (.modal b m)) := by
  cases he : d.branch k with
  | inl g =>
    have hh := h.pair k hk hr m hm _ (show branchRange (d.branch k)
      (booleanValue g.observer a) from by simpa [he,branchRange] using g.range_value ha)
    simp only [he,branchTransition] at hh
    rw [g.action m hm a ha] at hh
    rcases hk with rfl|rfl <;> simpa only [he,branchValue,leftSign] using hh.symm
  | inr g =>
    have hh := h.pair k hk hr m hm _ (show branchRange (d.branch k)
      (booleanValue g.observer b) from by simpa [he,branchRange] using g.range_value hb)
    simp only [he,branchTransition] at hh
    rw [g.action m hm b hb] at hh
    simpa only [he,branchValue] using hh.symm

theorem Coherent.pair_step {Δ shape} {d : Data Δ shape} (h : Coherent d)
    {k : Kind} (hk : k=.prod ∨ k=.sum) (hr : Root k shape)
    {a b c e : CompareTy} (ha : Representable Δ (leftShape shape) a)
    (hb : Representable Δ (rightShape shape) b) (hc : Representable Δ (leftShape shape) c)
    (he : Representable Δ (rightShape shape) e) {m} (hm : Entails Δ (.defined m))
    (h₁ : AlgebraSubtype Δ (.modal a m) (.modal c m))
    (h₂ : AlgebraSubtype Δ (.modal b m) (.modal e m)) :
    d.transition.apply m (branchValue (d.branch k) k a b)≤
      d.transition.apply m (branchValue (d.branch k) k c e) := by
  rw [h.pair_action hk hr ha hb hm,h.pair_action hk hr hc he hm]
  exact d.transition.monotone m hm (branch_pair_mono _ hk
    (representable_modal ha hm) (representable_modal hc hm)
    (representable_modal hb hm) (representable_modal he hm) h₁ h₂)

theorem Coherent.fn_action {Δ shape} {d : Data Δ shape} (h : Coherent d)
    (hr : Root .fn shape) {a b : CompareTy}
    (ha : Representable Δ (leftShape shape) a) (hb : Representable Δ (rightShape shape) b)
    {m n} (hm : Submode Δ m (.compose n .top)) :
    d.transition.apply m (branchValue (d.branch .fn) .fn a b)≤
      d.transition.apply n (branchValue (d.branch .fn) .fn a b) := by
  cases he : d.branch .fn with
  | inl g =>
    have hh := h.fn hr m n hm _ (show branchRange (d.branch .fn)
      (booleanValue g.observer a) from by simpa [he,branchRange] using g.range_value ha)
    simpa only [he,branchValue,branchSign] using hh
  | inr g =>
    have hh := h.fn hr m n hm _ (show branchRange (d.branch .fn)
      (booleanValue g.observer b) from by simpa [he,branchRange] using g.range_value hb)
    simpa only [he,branchValue,branchSign] using hh

theorem Coherent.fn_step {Δ shape} {d : Data Δ shape} (h : Coherent d)
    (hr : Root .fn shape) {a b c e : CompareTy}
    (ha : Representable Δ (leftShape shape) a) (hb : Representable Δ (rightShape shape) b)
    (hc : Representable Δ (leftShape shape) c) (he : Representable Δ (rightShape shape) e)
    {m n} (h₁ : AlgebraSubtype Δ c a) (h₂ : AlgebraSubtype Δ b e)
    (hm : Submode Δ m (.compose n .top)) :
    d.transition.apply m (branchValue (d.branch .fn) .fn a b)≤
      d.transition.apply n (branchValue (d.branch .fn) .fn c e) :=
  (d.transition.monotone m hm.defined.1 (branch_fn_mono _ ha hc hb he h₁ h₂)).trans
    (h.fn_action hr hc he hm)

theorem Data.equation_value {Δ shape} (d : Data Δ shape) {a b}
    (h : ComparisonAlgebra.Equation Δ a b) : d.value a=d.value b := by
  cases h with
  | distrib p hab hac =>
    rename_i a b c
    cases p <;> simp only [typeOp, Bool.false_eq_true, Bool.not_false, Bool.not_true,
      if_false, if_true, Data.value]
    all_goals cases d.value a <;> cases d.value b <;> cases d.value c <;> rfl
  | modal p _ hm =>
    cases p
    · exact d.transition.modal_meet hm _ _
    · exact d.transition.modal_join hm _ _
  | scalar p _ _ hm hn =>
    cases p
    · exact d.transition.meet _ _ hm hn _
    · exact d.transition.join _ _ hm hn _
  | prod p hac hbe =>
    rename_i a b c e
    have hh := branch_diagonal (d.branch .prod) .prod p a c b e
    cases p <;> simpa [Data.value,typeOp,Kind.leftSign] using hh.symm
  | sum p hac hbe =>
    rename_i a b c e
    have hh := branch_diagonal (d.branch .sum) .sum p a c b e
    cases p <;> simpa [Data.value,typeOp,Kind.leftSign] using hh.symm
  | fn p hac hbe =>
    rename_i a b c e
    have hh := branch_diagonal (d.branch .fn) .fn p a c b e
    cases p <;> simpa [Data.value,typeOp,Kind.leftSign] using hh.symm

theorem Data.trace_mono {Δ shape} (d : Data Δ shape) (hr : Resolved Δ shape)
    (hc : Coherent d) (hb : BoundsHold d) {a b}
    (h : ComparisonDefinedRoot.Derivation Δ a b)
    (he : ComparisonShape.Equivalent Δ a.shape shape) : d.value a≤d.value b := by
  induction h with
  | refl _ _ => exact le_rfl
  | bound h _ _ => exact hb _ _ h (by simpa only [CompareTy.shape_ofTy] using he)
  | identity _ _ => exact le_of_eq (d.transition.epsilon _)
  | identityRev _ _ => exact le_of_eq (d.transition.epsilon _).symm
  | compose _ _ hm hn => exact le_of_eq (d.transition.compose _ _ hm hn _).symm
  | composeRev _ _ hm hn => exact le_of_eq (d.transition.compose _ _ hm hn _)
  | trans h₁ _ ih₁ ih₂ =>
    exact (ih₁ he).trans (ih₂ (h₁.subtype.shape_equivalent.symm.trans he))
  | congr _ hm ih =>
    exact (d.transition.monotone _ hm.defined.1 (ih he)).trans (d.transition.submode _ _ hm _)
  | prod h₁ h₂ hs ht =>
    have hst := AlgebraSubtype.prod h₁ h₂
    have hl := hr.children .prod ⟨hst.wellShaped_left,
      (CompareTy.definedUnder_modal_iff.mp hs).1,he⟩
    have hh := hr.children .prod ⟨hst.wellShaped_right,
      (CompareTy.definedUnder_modal_iff.mp ht).1,hst.shape_equivalent.symm.trans he⟩
    exact hc.pair_step (Or.inl rfl) hl.1 hl.2.1 hl.2.2 hh.2.1 hh.2.2
      (CompareTy.definedUnder_modal_iff.mp hs).2 h₁ h₂
  | sum h₁ h₂ hs ht =>
    have hst := AlgebraSubtype.sum h₁ h₂
    have hl := hr.children .sum ⟨hst.wellShaped_left,
      (CompareTy.definedUnder_modal_iff.mp hs).1,he⟩
    have hh := hr.children .sum ⟨hst.wellShaped_right,
      (CompareTy.definedUnder_modal_iff.mp ht).1,hst.shape_equivalent.symm.trans he⟩
    exact hc.pair_step (Or.inr rfl) hl.1 hl.2.1 hl.2.2 hh.2.1 hh.2.2
      (CompareTy.definedUnder_modal_iff.mp hs).2 h₁ h₂
  | fn h₁ h₂ hm hs ht =>
    have hst := AlgebraSubtype.fn h₁ h₂ hm
    have hl := hr.children .fn ⟨hst.wellShaped_left,
      (CompareTy.definedUnder_modal_iff.mp hs).1,he⟩
    have hh := hr.children .fn ⟨hst.wellShaped_right,
      (CompareTy.definedUnder_modal_iff.mp ht).1,hst.shape_equivalent.symm.trans he⟩
    exact hc.fn_step hl.1 hl.2.1 hl.2.2 hh.2.1 hh.2.2 h₁ h₂ hm
  | joinLeft _ => exact Bool.le_iff_imp.mpr (fun h => by simp only [Data.value,h,Bool.true_or])
  | joinRight _ => exact Bool.le_iff_imp.mpr (fun h => by simp only [Data.value,h,Bool.or_true])
  | joinLeast h₁ h₂ ih₁ ih₂ =>
    exact sup_le (ih₁ he) (ih₂ (h₂.subtype.shape_equivalent.trans
      (h₁.subtype.shape_equivalent.symm.trans he)))
  | meetLeft _ => exact Bool.le_iff_imp.mpr (fun h => (Bool.and_eq_true_iff.mp h).1)
  | meetRight _ => exact Bool.le_iff_imp.mpr (fun h => (Bool.and_eq_true_iff.mp h).2)
  | meetGreatest _ _ ih₁ ih₂ => exact le_inf (ih₁ he) (ih₂ he)
  | equation h => exact le_of_eq (d.equation_value h)
  | equationRev h => exact le_of_eq (d.equation_value h).symm
  | clamp h₁ _ hm _ _ ih₁ ih₂ =>
    exact le_of_eq (d.transition.clamp hm (ih₁ (h₁.1.2.2.trans he)) (ih₂ he))
  | clampRev h₁ _ hm _ _ ih₁ ih₂ =>
    exact le_of_eq (d.transition.clamp hm (ih₁ (h₁.1.2.2.trans he)) (ih₂ he)).symm

theorem Data.subtype_mono {Δ shape} (d : Data Δ shape) (hr : Resolved Δ shape)
    (hc : Coherent d) (hb : BoundsHold d) (hΔ : Bounds.TypeBoundsDefined Δ)
    {a b} (ha : Representable Δ shape a) (hb' : Representable Δ shape b)
    (h : AlgebraSubtype Δ a b) : d.value a≤d.value b :=
  d.trace_mono hr hc hb (ComparisonDefinedRoot.derivation hΔ ha.2.1 hb'.2.1 h) ha.2.2

noncomputable def Data.observer {Δ shape} (d : Data Δ shape) (hr : Resolved Δ shape)
    (hc : Coherent d) (hb : BoundsHold d) (hΔ : Bounds.TypeBoundsDefined Δ) :
    LatticeHom (Order Δ shape) Bool where
  toFun := Quotient.lift (fun a : Carrier Δ shape => d.value a.type) (by
    intro a b hab
    have ha : Representable Δ shape a.type := ⟨a.shaped,a.defined,a.shape_eq⟩
    have hb' : Representable Δ shape b.type := ⟨b.shaped,b.defined,b.shape_eq⟩
    exact le_antisymm (d.subtype_mono hr hc hb hΔ ha hb' hab.1)
      (d.subtype_mono hr hc hb hΔ hb' ha hab.2))
  map_sup' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rfl
  map_inf' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rfl

theorem Data.observer_value {Δ shape} (d : Data Δ shape) (hr : Resolved Δ shape)
    (hc : Coherent d) (hb : BoundsHold d) (hΔ : Bounds.TypeBoundsDefined Δ)
    {a} (ha : Representable Δ shape a) :
    booleanValue (d.observer hr hc hb hΔ) a=d.value a :=
  booleanValue_represented _ _ ha

end ModalityInference.ComparisonShapedObserverGluing
