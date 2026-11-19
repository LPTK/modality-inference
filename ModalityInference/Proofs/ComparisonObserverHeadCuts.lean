import ModalityInference.Proofs.ComparisonObserverCutSeparation

/-! Whole cuts of the original comparison order provide optional semantic
shadows for partial endpoints. Their separation is simultaneous over every
defined term of the chosen shape, without a principal-cut assumption. -/
namespace ModalityInference.ComparisonObserverHeadCuts

open ComparisonAlgebra

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} {shape : ComparisonShape}

abbrev DefinedOrder (Δ : Bounds) (shape : ComparisonShape) := ComparisonAlgebra.Order Δ shape

private def below (p : CompareTy) : DefinedOrder Δ shape → Prop :=
  Quotient.lift (fun a : Carrier Δ shape => AlgebraSubtype Δ a.type p)
    (fun _ _ h => propext ⟨fun h₁ => AlgebraSubtype.trans h.2 h₁,fun h₁ => AlgebraSubtype.trans h.1 h₁⟩)

private def above (p : CompareTy) : DefinedOrder Δ shape → Prop :=
  Quotient.lift (fun a : Carrier Δ shape => AlgebraSubtype Δ p a.type)
    (fun _ _ h => propext ⟨fun h₁ => AlgebraSubtype.trans h₁ h.1,fun h₁ => AlgebraSubtype.trans h₁ h.2⟩)

def LowerInhabited (p : CompareTy) : Prop := ∃ a : Carrier Δ shape, AlgebraSubtype Δ a.type p

def UpperInhabited (p : CompareTy) : Prop := ∃ a : Carrier Δ shape, AlgebraSubtype Δ p a.type

def lowerCut (p : CompareTy) (hp : LowerInhabited (Δ := Δ) (shape := shape) p) :
    _root_.Order.Ideal (DefinedOrder Δ shape) where
  carrier := {x | below p x}
  lower' := by
    intro x y hxy hy
    induction x using Antisymmetrization.induction_on
    induction y using Antisymmetrization.induction_on
    exact AlgebraSubtype.trans hxy hy
  nonempty' := by
    obtain ⟨a,ha⟩ := hp
    exact ⟨Order.of a,ha⟩
  directed' := by
    intro x hx y hy
    induction x using Antisymmetrization.induction_on
    induction y using Antisymmetrization.induction_on
    rename_i a b
    exact ⟨Order.of (a.join b),AlgebraSubtype.joinLeast hx hy,Carrier.le_join_left a b,Carrier.le_join_right a b⟩

def upperCut (p : CompareTy) (hp : UpperInhabited (Δ := Δ) (shape := shape) p) :
    _root_.Order.PFilter (DefinedOrder Δ shape) :=
  (_root_.Order.IsPFilter.of_def (F := {x | above p x})
    (by obtain ⟨a,ha⟩ := hp; exact ⟨Order.of a,ha⟩)
    (by
      intro x hx y hy
      induction x using Antisymmetrization.induction_on
      induction y using Antisymmetrization.induction_on
      rename_i a b
      exact ⟨Order.of (a.meet b),AlgebraSubtype.meetGreatest hx hy,Carrier.meet_le_left a b,Carrier.meet_le_right a b⟩)
    (by
      intro x y hxy hx
      induction x using Antisymmetrization.induction_on
      induction y using Antisymmetrization.induction_on
      exact AlgebraSubtype.trans hx hxy)).toPFilter

/-- This separator concerns the original guarded algebra, including arbitrary
partial bounds and endpoints. -/
theorem cut_separator {p q : CompareTy}
    (hp : UpperInhabited (Δ := Δ) (shape := shape) p)
    (hq : LowerInhabited (Δ := Δ) (shape := shape) q)
    (hpq : ¬AlgebraSubtype Δ p q) :
    ∃ f : LatticeHom (DefinedOrder Δ shape) Bool,
      (∀ a : Carrier Δ shape, AlgebraSubtype Δ p a.type → f (Order.of a) = true) ∧
      (∀ a : Carrier Δ shape, AlgebraSubtype Δ a.type q → f (Order.of a) = false) := by
  have hd : Disjoint (↑(upperCut p hp) : Set (DefinedOrder Δ shape))
      (↑(lowerCut q hq) : Set (DefinedOrder Δ shape)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    induction x using Antisymmetrization.induction_on
    exact hpq (hx.trans hy)
  obtain ⟨f,hf,hg⟩ := ComparisonObserverCutSeparation.filter_ideal_separator
    (upperCut p hp) (lowerCut q hq) hd
  exact ⟨f,fun a ha => hf (Order.of a) ha,fun a ha => hg (Order.of a) ha⟩

def lowerShadow (p : CompareTy) : Set (LatticeHom (DefinedOrder Δ shape) Bool) :=
  {f | ∃ a : Carrier Δ shape, AlgebraSubtype Δ a.type p ∧ f (Order.of a) = true}

def upperShadow (p : CompareTy) : Set (LatticeHom (DefinedOrder Δ shape) Bool) :=
  {f | ∀ a : Carrier Δ shape, AlgebraSubtype Δ p a.type → f (Order.of a) = true}

theorem shadow_saturation {p q : CompareTy}
    (hp : UpperInhabited (Δ := Δ) (shape := shape) p)
    (hq : LowerInhabited (Δ := Δ) (shape := shape) q)
    (h : upperShadow (Δ := Δ) (shape := shape) p ⊆ lowerShadow q) : AlgebraSubtype Δ p q := by
  by_contra hpq
  obtain ⟨f,hf,hg⟩ := cut_separator hp hq hpq
  obtain ⟨a,ha,he⟩ := h hf
  exact Bool.false_ne_true ((hg a ha).symm.trans he)

theorem shadow_consistent (p : CompareTy) :
    lowerShadow (Δ := Δ) (shape := shape) p ⊆ upperShadow p := by
  intro f hf a ha
  obtain ⟨b,hb,hv⟩ := hf
  exact (Bool.le_iff_imp.mp (OrderHomClass.monotone f (hb.trans ha))) hv

theorem lowerShadow_mono {p q : CompareTy} (h : AlgebraSubtype Δ p q) :
    lowerShadow (Δ := Δ) (shape := shape) p ⊆ lowerShadow q :=
  fun _ ⟨a,ha,hf⟩ => ⟨a,ha.trans h,hf⟩

theorem upperShadow_mono {p q : CompareTy} (h : AlgebraSubtype Δ p q) :
    upperShadow (Δ := Δ) (shape := shape) p ⊆ upperShadow q :=
  fun _ hf a ha => hf a (h.trans ha)

noncomputable def lowerBit (p : CompareTy) (f : LatticeHom (DefinedOrder Δ shape) Bool) : Bool :=
  decide (f ∈ lowerShadow p)

noncomputable def upperBit (p : CompareTy) (f : LatticeHom (DefinedOrder Δ shape) Bool) : Bool :=
  decide (f ∈ upperShadow p)

/-- A nonempty lower cut attains its supremum at each Boolean observer. The
witness may depend on the observer; no single finite term realizes the cut. -/
theorem lower_attained {p : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := shape) p)
    (f : LatticeHom (DefinedOrder Δ shape) Bool) :
    ∃ a : Carrier Δ shape, AlgebraSubtype Δ a.type p ∧ lowerBit p f = f (Order.of a) := by
  classical
  by_cases h : f ∈ lowerShadow p
  · obtain ⟨a,ha,hf⟩ := h
    exact ⟨a,ha,by simp only [lowerBit,decide_eq_true (show f ∈ lowerShadow p from ⟨a,ha,hf⟩),hf]⟩
  · obtain ⟨a,ha⟩ := hp
    have hf : f (Order.of a) = false := Bool.eq_false_iff.mpr (fun ht => h ⟨a,ha,ht⟩)
    exact ⟨a,ha,by simp only [lowerBit,decide_eq_false h,hf]⟩

/-- Upper cuts likewise attain their Boolean infimum pointwise. -/
theorem upper_attained {p : CompareTy} (hp : UpperInhabited (Δ := Δ) (shape := shape) p)
    (f : LatticeHom (DefinedOrder Δ shape) Bool) :
    ∃ a : Carrier Δ shape, AlgebraSubtype Δ p a.type ∧ upperBit p f = f (Order.of a) := by
  classical
  by_cases h : f ∈ upperShadow p
  · obtain ⟨a,ha⟩ := hp
    exact ⟨a,ha,by simp only [upperBit,decide_eq_true h,h a ha]⟩
  · have hn : ¬∀a : Carrier Δ shape, AlgebraSubtype Δ p a.type → f (Order.of a) = true := h
    push_neg at hn
    obtain ⟨a,ha,hf⟩ := hn
    exact ⟨a,ha,by simp only [upperBit,decide_eq_false h,Bool.eq_false_iff.mpr hf]⟩

theorem lowerBit_mono {p q : CompareTy} (h : AlgebraSubtype Δ p q)
    (f : LatticeHom (DefinedOrder Δ shape) Bool) : lowerBit p f ≤ lowerBit q f := by
  classical
  apply Bool.le_iff_imp.mpr
  intro ht
  exact decide_eq_true (lowerShadow_mono h (of_decide_eq_true ht))

theorem upperBit_mono {p q : CompareTy} (h : AlgebraSubtype Δ p q)
    (f : LatticeHom (DefinedOrder Δ shape) Bool) : upperBit p f ≤ upperBit q f := by
  classical
  apply Bool.le_iff_imp.mpr
  intro ht
  exact decide_eq_true (upperShadow_mono h (of_decide_eq_true ht))

theorem bits_consistent (p : CompareTy) (f : LatticeHom (DefinedOrder Δ shape) Bool) :
    lowerBit p f ≤ upperBit p f := by
  classical
  apply Bool.le_iff_imp.mpr
  intro ht
  exact decide_eq_true (shadow_consistent p (of_decide_eq_true ht))

/-- The same cut-saturation statement in the coordinate representation used
by the all-observer range product. -/
theorem bits_saturation {p q : CompareTy}
    (hp : UpperInhabited (Δ := Δ) (shape := shape) p)
    (hq : LowerInhabited (Δ := Δ) (shape := shape) q)
    (h : ∀ f : LatticeHom (DefinedOrder Δ shape) Bool, upperBit p f ≤ lowerBit q f) :
    AlgebraSubtype Δ p q := by
  apply shadow_saturation hp hq
  intro f hf
  exact of_decide_eq_true (Bool.le_iff_imp.mp (h f) (decide_eq_true hf))

theorem eval_le_lower {p : CompareTy} (a : Carrier Δ shape) (ha : AlgebraSubtype Δ a.type p)
    (f : LatticeHom (DefinedOrder Δ shape) Bool) : f (Order.of a) ≤ lowerBit p f :=
  Bool.le_iff_imp.mpr (fun hv => decide_eq_true ⟨a,ha,hv⟩)

theorem upper_le_eval {p : CompareTy} (a : Carrier Δ shape) (ha : AlgebraSubtype Δ p a.type)
    (f : LatticeHom (DefinedOrder Δ shape) Bool) : upperBit p f ≤ f (Order.of a) :=
  Bool.le_iff_imp.mpr (fun hv => (of_decide_eq_true hv) a ha)

theorem lowerBit_defined (a : Carrier Δ shape) (f : LatticeHom (DefinedOrder Δ shape) Bool) :
    lowerBit a.type f = f (Order.of a) := by
  apply le_antisymm
  · apply Bool.le_iff_imp.mpr
    intro hv
    obtain ⟨b,hb,hf⟩ := of_decide_eq_true hv
    exact Bool.le_iff_imp.mp (OrderHomClass.monotone f hb) hf
  · exact eval_le_lower a (.refl a.shaped) f

theorem upperBit_defined (a : Carrier Δ shape) (f : LatticeHom (DefinedOrder Δ shape) Bool) :
    upperBit a.type f = f (Order.of a) := by
  apply le_antisymm
  · exact upper_le_eval a (.refl a.shaped) f
  · apply Bool.le_iff_imp.mpr
    intro hv
    apply decide_eq_true
    intro b hb
    exact Bool.le_iff_imp.mp (OrderHomClass.monotone f hb) hv

theorem LowerInhabited.mono {p q : CompareTy} (hp : LowerInhabited (Δ := Δ) (shape := shape) p)
    (h : AlgebraSubtype Δ p q) : LowerInhabited (Δ := Δ) (shape := shape) q :=
  hp.imp (fun _ ha => ha.trans h)

theorem UpperInhabited.antitone {p q : CompareTy} (hq : UpperInhabited (Δ := Δ) (shape := shape) q)
    (h : AlgebraSubtype Δ p q) : UpperInhabited (Δ := Δ) (shape := shape) p :=
  hq.imp (fun _ ha => h.trans ha)

end
end ModalityInference.ComparisonObserverHeadCuts
