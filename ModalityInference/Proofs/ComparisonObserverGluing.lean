import ModalityInference.Proofs.ComparisonObserverActions
import ModalityInference.Proofs.ComparisonDefinedRoot
import ModalityInference.Proofs.ComparisonInfeasibleShapes

/-! Root observer extension in a shape context with no finite model. The
context must establish the written guards of its type bounds. Modal transfer
and child range coherence are kept explicit; finite port agreement preserves a
finite boundary without identifying independent constructor observations. -/

namespace ModalityInference.ComparisonObserverGluing

open ComparisonAlgebra ComparisonStructuralLattice ComparisonStructuralObservers
  ComparisonObserverActions

/-- A selected child remains an observer of the original complete child algebra. -/
structure Child (Δ : Bounds) where
  observer : LatticeHom (Order Δ .unit) Bool
  transition : Transition Δ
  action : ∀ m, Entails Δ (.defined m) → ∀ a, Representable Δ .unit a →
    transition.apply m (booleanValue observer a) = booleanValue observer (.modal a m)

def Child.Range {Δ} (g : Child Δ) (x : Bool) : Prop :=
  ∃ a : Carrier Δ .unit, ComparisonAlgebra.observer g.observer a = x

structure Branch (Δ : Bounds) where
  left : Bool
  child : Child Δ

noncomputable def Branch.value {Δ} (b : Branch Δ) (k : Kind) (a c : CompareTy) : Bool :=
  if b.left then leftSign k (booleanValue b.child.observer a)
  else booleanValue b.child.observer c

def Branch.sign {Δ} (b : Branch Δ) (k : Kind) (x : Bool) : Bool :=
  if b.left then leftSign k x else x

structure Data (Δ : Bounds) where
  transition : Transition Δ
  atom : TypeVar → Bool
  unitValue : Bool
  creditValue : Bool
  branch : Kind → Branch Δ

noncomputable def Data.value {Δ} (d : Data Δ) : CompareTy → Bool
  | .var v => d.atom v
  | .unit => d.unitValue
  | .credit => d.creditValue
  | .prod a b => (d.branch .prod).value .prod a b
  | .sum a b => (d.branch .sum).value .sum a b
  | .fn a b => (d.branch .fn).value .fn a b
  | .modal a m => d.transition.apply m (d.value a)
  | .join a b => d.value a || d.value b
  | .meet a b => d.value a && d.value b

/-- Coherence concerns the two Boolean fibers, including whether a fiber is
inhabited. Pair constructors inherit their parent's action; function domains
reverse order and their root action obeys the function rule. -/
structure Coherent {Δ} (d : Data Δ) : Prop where
  pair : ∀ k, k = Kind.prod ∨ k = Kind.sum → ∀ m,
    Entails Δ (.defined m) → ∀ x, (d.branch k).child.Range x →
      d.transition.apply m ((d.branch k).child.transition.apply m x) =
        d.transition.apply m x
  fn : ∀ m n, Submode Δ m (.compose n .top) → ∀ x,
    (d.branch .fn).child.Range x →
      d.transition.apply m ((d.branch .fn).sign .fn x) ≤
        d.transition.apply n ((d.branch .fn).sign .fn x)

def BoundsHold {Δ} (d : Data Δ) : Prop :=
  ∀ a b, Constraint.sub a b ∈ Δ → d.value (.ofTy a) ≤ d.value (.ofTy b)

theorem representable {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    {a : CompareTy} (ha : a.DefinedUnder Δ) : Representable Δ .unit a :=
  ⟨CompareTy.wellShaped_of_no_models hn _, ha,
    ComparisonShape.equivalent_of_no_models hn _ _⟩

theorem Child.range_value {Δ} (g : Child Δ) {a : CompareTy}
    (ha : Representable Δ .unit a) : g.Range (booleanValue g.observer a) :=
  ⟨represented ha, (booleanValue_represented g.observer a ha).symm⟩

theorem value_mono {Δ} (g : Child Δ) {a b : CompareTy}
    (ha : Representable Δ .unit a) (hb : Representable Δ .unit b)
    (h : AlgebraSubtype Δ a b) : booleanValue g.observer a ≤ booleanValue g.observer b := by
  rw [booleanValue_represented g.observer a ha, booleanValue_represented g.observer b hb]
  exact OrderHomClass.monotone g.observer h

theorem Branch.diagonal {Δ} (b : Branch Δ) (k : Kind) (p : Bool) (a c u v : CompareTy) :
    b.value k (typeOp (k.leftSign p) a c) (typeOp p u v) =
      if p then b.value k a u || b.value k c v else b.value k a u && b.value k c v := by
  cases k <;> cases p <;> cases hl : b.left <;>
    simp [Branch.value, hl, typeOp, leftSign, Kind.leftSign]

theorem Branch.mono {Δ} (b : Branch Δ) (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    {a c u v : CompareTy} (ha : a.DefinedUnder Δ) (hc : c.DefinedUnder Δ)
    (hu : u.DefinedUnder Δ) (hv : v.DefinedUnder Δ)
    (hca : AlgebraSubtype Δ c a) (huv : AlgebraSubtype Δ u v) :
    b.value .fn a u ≤ b.value .fn c v := by
  cases hl : b.left
  · simpa only [Branch.value, hl, Bool.false_eq_true, if_false] using
      value_mono b.child (representable hn hu) (representable hn hv) huv
  · have hh := value_mono b.child (representable hn hc) (representable hn ha) hca
    simp only [Branch.value, hl, if_true, leftSign]
    change (!booleanValue b.child.observer a) ≤ (!booleanValue b.child.observer c)
    cases ea : booleanValue b.child.observer a <;> cases ec : booleanValue b.child.observer c <;>
      simp_all [Bool.le_iff_imp]

theorem Branch.pair_mono {Δ} (b : Branch Δ) (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    {k : Kind} (hk : k = .prod ∨ k = .sum)
    {a c u v : CompareTy} (ha : a.DefinedUnder Δ) (hc : c.DefinedUnder Δ)
    (hu : u.DefinedUnder Δ) (hv : v.DefinedUnder Δ)
    (hac : AlgebraSubtype Δ a c) (huv : AlgebraSubtype Δ u v) :
    b.value k a u ≤ b.value k c v := by
  have hh₁ := value_mono b.child (representable hn ha) (representable hn hc) hac
  have hh₂ := value_mono b.child (representable hn hu) (representable hn hv) huv
  rcases hk with rfl | rfl <;> cases hl : b.left <;>
    simpa only [Branch.value, hl, Bool.false_eq_true, if_false, if_true, leftSign]
      using (by first | exact hh₂ | exact hh₁)

theorem Coherent.pair_action {Δ} {d : Data Δ} (h : Coherent d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) {k : Kind} (hk : k = .prod ∨ k = .sum)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    {m} (hm : Entails Δ (.defined m)) :
    d.transition.apply m ((d.branch k).value k a b) =
      d.transition.apply m ((d.branch k).value k (.modal a m) (.modal b m)) := by
  have h₁ := h.pair k hk m hm _ ((d.branch k).child.range_value (representable hn ha))
  have h₂ := h.pair k hk m hm _ ((d.branch k).child.range_value (representable hn hb))
  rw [(d.branch k).child.action m hm a (representable hn ha)] at h₁
  rw [(d.branch k).child.action m hm b (representable hn hb)] at h₂
  cases hl : (d.branch k).left <;> rcases hk with rfl | rfl <;>
    simp only [Branch.value, hl, Bool.false_eq_true, if_false, if_true, leftSign]
  all_goals first | exact h₂.symm | exact h₁.symm

theorem Coherent.pair_step {Δ} {d : Data Δ} (h : Coherent d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) {k : Kind} (hk : k = .prod ∨ k = .sum)
    {a b c e : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hc : c.DefinedUnder Δ) (he : e.DefinedUnder Δ)
    {m} (hm : Entails Δ (.defined m))
    (h₁ : AlgebraSubtype Δ (.modal a m) (.modal c m))
    (h₂ : AlgebraSubtype Δ (.modal b m) (.modal e m)) :
    d.transition.apply m ((d.branch k).value k a b) ≤
      d.transition.apply m ((d.branch k).value k c e) := by
  rw [h.pair_action hn hk ha hb hm, h.pair_action hn hk hc he hm]
  exact d.transition.monotone m hm ((d.branch k).pair_mono hn hk
    (CompareTy.definedUnder_modal_iff.mpr ⟨ha, hm⟩)
    (CompareTy.definedUnder_modal_iff.mpr ⟨hc, hm⟩)
    (CompareTy.definedUnder_modal_iff.mpr ⟨hb, hm⟩)
    (CompareTy.definedUnder_modal_iff.mpr ⟨he, hm⟩) h₁ h₂)

theorem Coherent.fn_action {Δ} {d : Data Δ} (h : Coherent d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) {a b : CompareTy}
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    {m n} (hm : Submode Δ m (.compose n .top)) :
    d.transition.apply m ((d.branch .fn).value .fn a b) ≤
      d.transition.apply n ((d.branch .fn).value .fn a b) := by
  have h₁ := h.fn m n hm _ ((d.branch .fn).child.range_value (representable hn ha))
  have h₂ := h.fn m n hm _ ((d.branch .fn).child.range_value (representable hn hb))
  cases hl : (d.branch .fn).left <;>
    simp only [Branch.value, Branch.sign, hl, Bool.false_eq_true, if_false, if_true] at h₁ h₂ ⊢
  all_goals first | exact h₂ | exact h₁

theorem Coherent.fn_step {Δ} {d : Data Δ} (h : Coherent d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    {a b c e : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hc : c.DefinedUnder Δ) (he : e.DefinedUnder Δ)
    {m n} (h₁ : AlgebraSubtype Δ c a) (h₂ : AlgebraSubtype Δ b e)
    (hm : Submode Δ m (.compose n .top)) :
    d.transition.apply m ((d.branch .fn).value .fn a b) ≤
      d.transition.apply n ((d.branch .fn).value .fn c e) :=
  (d.transition.monotone m hm.defined.1
    ((d.branch .fn).mono hn ha hc hb he h₁ h₂)).trans (h.fn_action hn hc he hm)

theorem Data.equation_value {Δ} (d : Data Δ) {a b}
    (h : ComparisonAlgebra.Equation Δ a b) : d.value a = d.value b := by
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
    have hh := (d.branch .prod).diagonal .prod p a c b e
    cases p <;> simpa [Data.value, typeOp, Kind.leftSign] using hh.symm
  | sum p hac hbe =>
    rename_i a b c e
    have hh := (d.branch .sum).diagonal .sum p a c b e
    cases p <;> simpa [Data.value, typeOp, Kind.leftSign] using hh.symm
  | fn p hac hbe =>
    rename_i a b c e
    have hh := (d.branch .fn).diagonal .fn p a c b e
    cases p <;> simpa [Data.value, typeOp, Kind.leftSign] using hh.symm

theorem Data.trace_mono {Δ} (d : Data Δ) (hc : Coherent d) (hb : BoundsHold d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) {a b}
    (h : ComparisonDefinedRoot.Derivation Δ a b) : d.value a ≤ d.value b := by
  induction h with
  | refl _ _ => exact le_rfl
  | bound h _ _ => exact hb _ _ h
  | identity _ _ => exact le_of_eq (d.transition.epsilon _)
  | identityRev _ _ => exact le_of_eq (d.transition.epsilon _).symm
  | compose _ _ hm hn => exact le_of_eq (d.transition.compose _ _ hm hn _).symm
  | composeRev _ _ hm hn => exact le_of_eq (d.transition.compose _ _ hm hn _)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr _ hm ih =>
    exact (d.transition.monotone _ hm.defined.1 ih).trans (d.transition.submode _ _ hm _)
  | prod h₁ h₂ hs ht =>
    obtain ⟨⟨ha,hb⟩,hm⟩ := (CompareTy.definedUnder_modal_iff.mp hs).imp_left
      CompareTy.definedUnder_prod_iff.mp
    obtain ⟨hc',he⟩ := CompareTy.definedUnder_prod_iff.mp
      (CompareTy.definedUnder_modal_iff.mp ht).1
    exact hc.pair_step hn (Or.inl rfl) ha hb hc' he hm h₁ h₂
  | sum h₁ h₂ hs ht =>
    obtain ⟨⟨ha,hb⟩,hm⟩ := (CompareTy.definedUnder_modal_iff.mp hs).imp_left
      CompareTy.definedUnder_sum_iff.mp
    obtain ⟨hc',he⟩ := CompareTy.definedUnder_sum_iff.mp
      (CompareTy.definedUnder_modal_iff.mp ht).1
    exact hc.pair_step hn (Or.inr rfl) ha hb hc' he hm h₁ h₂
  | fn h₁ h₂ hm hs ht =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_fn_iff.mp
      (CompareTy.definedUnder_modal_iff.mp hs).1
    obtain ⟨hc',he⟩ := CompareTy.definedUnder_fn_iff.mp
      (CompareTy.definedUnder_modal_iff.mp ht).1
    exact hc.fn_step hn ha hb hc' he h₁ h₂ hm
  | joinLeft _ => exact Bool.le_iff_imp.mpr (fun h => by simp only [Data.value, h, Bool.true_or])
  | joinRight _ => exact Bool.le_iff_imp.mpr (fun h => by simp only [Data.value, h, Bool.or_true])
  | joinLeast _ _ ih₁ ih₂ => exact sup_le ih₁ ih₂
  | meetLeft _ => exact Bool.le_iff_imp.mpr (fun h => (Bool.and_eq_true_iff.mp h).1)
  | meetRight _ => exact Bool.le_iff_imp.mpr (fun h => (Bool.and_eq_true_iff.mp h).2)
  | meetGreatest _ _ ih₁ ih₂ => exact le_inf ih₁ ih₂
  | equation h => exact le_of_eq (d.equation_value h)
  | equationRev h => exact le_of_eq (d.equation_value h).symm
  | clamp _ _ hm _ _ ih₁ ih₂ => exact le_of_eq (d.transition.clamp hm ih₁ ih₂)
  | clampRev _ _ hm _ _ ih₁ ih₂ => exact le_of_eq (d.transition.clamp hm ih₁ ih₂).symm

/-- Local constructor coherence and the original declared edges suffice to
extend the root interpretation to all derivable comparisons of defined terms. -/
theorem Data.subtype_mono {Δ} (d : Data Δ) (hc : Coherent d) (hb : BoundsHold d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Bounds.TypeBoundsDefined Δ)
    {a b} (ha : CompareTy.DefinedUnder a Δ) (hb' : CompareTy.DefinedUnder b Δ)
    (h : AlgebraSubtype Δ a b) : d.value a ≤ d.value b :=
  d.trace_mono hc hb hn (ComparisonDefinedRoot.derivation hΔ ha hb' h)

noncomputable def Data.observer {Δ} (d : Data Δ) (hc : Coherent d) (hb : BoundsHold d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Bounds.TypeBoundsDefined Δ) :
    LatticeHom (Order Δ .unit) Bool where
  toFun := Quotient.lift (fun a : Carrier Δ .unit => d.value a.type) (by
    intro a b hab
    exact le_antisymm (d.subtype_mono hc hb hn hΔ a.defined b.defined hab.1)
      (d.subtype_mono hc hb hn hΔ b.defined a.defined hab.2))
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

theorem Data.observer_value {Δ} (d : Data Δ) (hc : Coherent d) (hb : BoundsHold d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Bounds.TypeBoundsDefined Δ)
    (a : Carrier Δ .unit) :
    ComparisonAlgebra.observer (d.observer hc hb hn hΔ) a = d.value a.type := rfl

/-- The finite child observations used by one root interpretation. Modal and
lattice nodes recurse; a structural node delegates its entire child term. -/
def ports : CompareTy → List (Kind × CompareTy)
  | .prod a b => [(.prod, a), (.prod, b)]
  | .sum a b => [(.sum, a), (.sum, b)]
  | .fn a b => [(.fn, a), (.fn, b)]
  | .modal a _ => ports a
  | .join a b | .meet a b => ports a ++ ports b
  | .var _ | .unit | .credit => []

def Data.replace {Δ} (d : Data Δ) (children : Kind → Child Δ) : Data Δ :=
  { d with branch := fun k => { left := (d.branch k).left, child := children k } }

/-- Only inhabited Boolean fibers matter. A replacement preserves the child's
modal transfer on those fibers and does not introduce a new observable value. -/
structure Replacement {Δ} (d : Data Δ) (children : Kind → Child Δ) : Prop where
  range : ∀ k x, (children k).Range x → (d.branch k).child.Range x
  action : ∀ k m, Entails Δ (.defined m) → ∀ x, (children k).Range x →
    (children k).transition.apply m x = (d.branch k).child.transition.apply m x

theorem Coherent.replace {Δ} {d : Data Δ} (hc : Coherent d) {children : Kind → Child Δ}
    (hr : Replacement d children) : Coherent (d.replace children) where
  pair k hk m hm x hx := by
    change d.transition.apply m ((children k).transition.apply m x) = d.transition.apply m x
    rw [hr.action k m hm x hx]
    exact hc.pair k hk m hm x (hr.range k x hx)
  fn m n hm x hx := hc.fn m n hm x (hr.range .fn x hx)

/-- Matching the finite child ports preserves the interpretation of a boundary
term, including compound modalities and nested lattice expressions. -/
theorem Data.replace_value {Δ} (d : Data Δ) (children : Kind → Child Δ) (a : CompareTy)
    (hp : ∀ p ∈ ports a, booleanValue (children p.1).observer p.2 =
      booleanValue (d.branch p.1).child.observer p.2) :
    (d.replace children).value a = d.value a := by
  induction a with
  | var | unit | credit => rfl
  | prod a b =>
    have ha := hp (.prod, a) (by simp [ports])
    have hb := hp (.prod, b) (by simp [ports])
    simp only [Data.value, Data.replace, Branch.value, ha, hb]
  | sum a b =>
    have ha := hp (.sum, a) (by simp [ports])
    have hb := hp (.sum, b) (by simp [ports])
    simp only [Data.value, Data.replace, Branch.value, ha, hb]
  | fn a b =>
    have ha := hp (.fn, a) (by simp [ports])
    have hb := hp (.fn, b) (by simp [ports])
    simp only [Data.value, Data.replace, Branch.value, ha, hb]
  | modal a m ih =>
    exact congrArg (d.transition.apply m) (ih hp)
  | join a b iha ihb =>
    exact congrArg₂ (· || ·) (iha (fun p h => hp p (List.mem_append_left _ h)))
      (ihb (fun p h => hp p (List.mem_append_right _ h)))
  | meet a b iha ihb =>
    exact congrArg₂ (· && ·) (iha (fun p h => hp p (List.mem_append_left _ h)))
      (ihb (fun p h => hp p (List.mem_append_right _ h)))

def DeclaredIn (Δ : Bounds) (boundary : List CompareTy) : Prop :=
  ∀ a b, Constraint.sub a b ∈ Δ → CompareTy.ofTy a ∈ boundary ∧ CompareTy.ofTy b ∈ boundary

def PortsAgree {Δ} (d : Data Δ) (children : Kind → Child Δ) (boundary : List CompareTy) : Prop :=
  ∀ a ∈ boundary, ∀ p ∈ ports a, booleanValue (children p.1).observer p.2 =
    booleanValue (d.branch p.1).child.observer p.2

theorem BoundsHold.replace {Δ} {d : Data Δ} (hb : BoundsHold d)
    {children : Kind → Child Δ} {boundary : List CompareTy}
    (hd : DeclaredIn Δ boundary) (hp : PortsAgree d children boundary) :
    BoundsHold (d.replace children) := by
  intro a b hab
  rw [d.replace_value children _ (hp _ (hd _ _ hab).1),
    d.replace_value children _ (hp _ (hd _ _ hab).2)]
  exact hb a b hab

theorem Data.observer_value_defined {Δ} (d : Data Δ) (hc : Coherent d) (hb : BoundsHold d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Bounds.TypeBoundsDefined Δ)
    {a : CompareTy} (ha : a.DefinedUnder Δ) :
    booleanValue (d.observer hc hb hn hΔ) a = d.value a := by
  rw [booleanValue_represented _ a (representable hn ha)]
  rfl

/-- Replacing the selected child observers extends to an actual parent
observer. Only finitely many child values are checked to retain a given finite
boundary; modal transfers and inhabited fibers enforce constructor coherence. -/
theorem observer_extension {Δ} (d : Data Δ) (hc : Coherent d) (hb : BoundsHold d)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Bounds.TypeBoundsDefined Δ)
    (children : Kind → Child Δ) (hr : Replacement d children)
    (boundary : List CompareTy) (hd : DeclaredIn Δ boundary)
    (hp : PortsAgree d children boundary) :
    ∃ f : LatticeHom (Order Δ .unit) Bool,
      (∀ a, a.DefinedUnder Δ → booleanValue f a = (d.replace children).value a) ∧
      (∀ a ∈ boundary, a.DefinedUnder Δ → booleanValue f a = d.value a) := by
  let f := (d.replace children).observer (hc.replace hr) (hb.replace hd hp) hn hΔ
  have hf (a : CompareTy) (ha : a.DefinedUnder Δ) :
      booleanValue f a = (d.replace children).value a :=
    (d.replace children).observer_value_defined (hc.replace hr) (hb.replace hd hp) hn hΔ ha
  exact ⟨f, hf, fun a ha had => (hf a had).trans (d.replace_value children a (hp a ha))⟩

end ModalityInference.ComparisonObserverGluing
