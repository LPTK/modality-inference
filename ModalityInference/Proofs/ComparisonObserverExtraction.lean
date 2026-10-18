import ModalityInference.Proofs.ComparisonObserverGluing

/-! An actual parent observer determines the root data used by observer gluing.
The selected children are observers of the original algebra, and their choices
are shared across all guarded modalities. This supplies the converse boundary
extension after a compatible replacement of the child observations. -/

namespace ModalityInference.ComparisonObserverGluing

open ComparisonAlgebra ComparisonStructuralLattice ComparisonStructuralObservers
  ComparisonObserverActions

private def unitCarrier (Δ : Bounds) : Carrier Δ .unit where
  type := .unit
  shaped := trivial
  defined := by simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
  shape_eq := .refl

noncomputable def Child.ofObserver {Δ} (f : LatticeHom (Order Δ .unit) Bool) : Child Δ where
  observer := f
  transition := Classical.choose (observer_transition f (unitCarrier Δ))
  action m hm a ha := by
    have h := Classical.choose_spec (observer_transition f (unitCarrier Δ)) m hm (represented ha)
    calc
      (Classical.choose (observer_transition f (unitCarrier Δ))).apply m (booleanValue f a) =
          (Classical.choose (observer_transition f (unitCarrier Δ))).apply m
            (ComparisonAlgebra.observer f (represented ha)) :=
        congrArg _ (booleanValue_represented f a ha)
      _ = ComparisonAlgebra.observer f ((represented ha).modal m hm) := h
      _ = booleanValue f (.modal a m) := (booleanValue_carrier f ((represented ha).modal m hm)).symm

private def intoUnit {Δ shape} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (a : Carrier Δ shape) : Carrier Δ .unit :=
  ⟨a.type, a.shaped, a.defined, ComparisonShape.equivalent_of_no_models hn _ _⟩

noncomputable def rebaseObserver {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (f : LatticeHom (Order Δ .unit) Bool) (shape : ComparisonShape) :
    LatticeHom (Order Δ shape) Bool where
  toFun := Quotient.lift (fun a : Carrier Δ shape => ComparisonAlgebra.observer f (intoUnit hn a)) (by
    intro a b hab
    exact congrArg f (Quotient.sound hab))
  map_sup' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rename_i a b
    change ComparisonAlgebra.observer f (intoUnit hn (a.join b)) = _
    exact observer_join f (intoUnit hn a) (intoUnit hn b)
  map_inf' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rename_i a b
    change ComparisonAlgebra.observer f (intoUnit hn (a.meet b)) = _
    exact observer_meet f (intoUnit hn a) (intoUnit hn b)

theorem rebaseObserver_value {Δ shape} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (f : LatticeHom (Order Δ .unit) Bool) (a : Carrier Δ shape) :
    ComparisonAlgebra.observer (rebaseObserver hn f shape) a = booleanValue f a.type :=
  (booleanValue_carrier f (intoUnit hn a)).symm

theorem branch_exists {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (f : LatticeHom (Order Δ .unit) Bool) (k : Kind) :
    ∃ b : Branch Δ, ∀ a c : CompareTy, a.DefinedUnder Δ → c.DefinedUnder Δ →
      b.value k a c = booleanValue f (k.op a c) := by
  let fk := rebaseObserver hn f (k.shape .unit .unit)
  let z := unitCarrier Δ
  rcases rectangle_factor (fun a c => ComparisonAlgebra.observer fk (opCarrier k a c))
    (observer_rectangle k fk) z z with hl | hr
  · refine ⟨⟨true, Child.ofObserver (leftObserver k fk z)⟩, ?_⟩
    intro a c ha hc
    let A := represented (representable hn ha)
    let C := represented (representable hn hc)
    change leftSign k (booleanValue (leftObserver k fk z) A.type) = booleanValue f (k.op A.type C.type)
    rw [booleanValue_carrier (leftObserver k fk z) A]
    change leftSign k (ComparisonAlgebra.observer (leftObserver k fk z) A) = _
    rw [leftObserver_value]
    rw [← hl A C]
    exact rebaseObserver_value hn f (opCarrier k A C)
  · refine ⟨⟨false, Child.ofObserver (rightObserver k fk z)⟩, ?_⟩
    intro a c ha hc
    let A := represented (representable hn ha)
    let C := represented (representable hn hc)
    change booleanValue (rightObserver k fk z) C.type = booleanValue f (k.op A.type C.type)
    rw [booleanValue_carrier (rightObserver k fk z) C]
    change ComparisonAlgebra.observer (rightObserver k fk z) C = _
    rw [rightObserver_value]
    rw [← hr A C]
    exact rebaseObserver_value hn f (opCarrier k A C)

/-- An interpretation represents an existing parent on every defined type. -/
def Represents {Δ} (d : Data Δ) (f : LatticeHom (Order Δ .unit) Bool) : Prop :=
  ∀ a, a.DefinedUnder Δ → d.value a = booleanValue f a

noncomputable def extracted {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (f : LatticeHom (Order Δ .unit) Bool) : Data Δ where
  transition := (Child.ofObserver f).transition
  atom v := booleanValue f (.var v)
  unitValue := booleanValue f .unit
  creditValue := booleanValue f .credit
  branch k := Classical.choose (branch_exists hn f k)

theorem extracted_represents {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (f : LatticeHom (Order Δ .unit) Bool) : Represents (extracted hn f) f := by
  intro a ha
  induction a with
  | var | unit | credit => rfl
  | prod a b =>
    have hd := CompareTy.definedUnder_prod_iff.mp ha
    exact Classical.choose_spec (branch_exists hn f .prod) a b hd.1 hd.2
  | sum a b =>
    have hd := CompareTy.definedUnder_sum_iff.mp ha
    exact Classical.choose_spec (branch_exists hn f .sum) a b hd.1 hd.2
  | fn a b =>
    have hd := CompareTy.definedUnder_fn_iff.mp ha
    exact Classical.choose_spec (branch_exists hn f .fn) a b hd.1 hd.2
  | modal a m ih =>
    have hd := CompareTy.definedUnder_modal_iff.mp ha
    change (Child.ofObserver f).transition.apply m ((extracted hn f).value a) = _
    rw [ih hd.1]
    exact (Child.ofObserver f).action m hd.2 a (representable hn hd.1)
  | join a b iha ihb =>
    have hd := CompareTy.definedUnder_join_iff.mp ha
    exact congrArg₂ (· || ·) (iha hd.1) (ihb hd.2)
  | meet a b iha ihb =>
    have hd := CompareTy.definedUnder_meet_iff.mp ha
    exact congrArg₂ (· && ·) (iha hd.1) (ihb hd.2)

theorem Represents.bounds {Δ} {d : Data Δ} {f : LatticeHom (Order Δ .unit) Bool}
    (h : Represents d f) (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Bounds.TypeBoundsDefined Δ) : BoundsHold d := by
  intro a b hab
  have hd₁ := (CompareTy.definedUnder_ofTy a Δ).mpr (hΔ a b hab).1
  have hd₂ := (CompareTy.definedUnder_ofTy b Δ).mpr (hΔ a b hab).2
  rw [h _ hd₁, h _ hd₂]
  exact value_mono (Child.ofObserver f) (representable hn hd₁) (representable hn hd₂) (.shaped (.bound hab))

theorem Represents.pair_values {Δ} {d : Data Δ} {f : LatticeHom (Order Δ .unit) Bool}
    (h : Represents d f) (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (isSum : Bool) {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    {m} (hm : Entails Δ (.defined m)) :
    let k := if isSum then Kind.sum else Kind.prod
    d.transition.apply m ((d.branch k).value k a b) =
      d.transition.apply m ((d.branch k).value k (.modal a m) (.modal b m)) := by
  have he := ComparisonStructuralFamily.pair_absorb isSum
    (CompareTy.wellShaped_of_no_models hn a) (CompareTy.wellShaped_of_no_models hn b)
    (GuardedMode.ofDefined m hm)
  have hda : (.modal a m : CompareTy).DefinedUnder Δ :=
    CompareTy.definedUnder_modal_iff.mpr ⟨ha,hm⟩
  have hdb : (.modal b m : CompareTy).DefinedUnder Δ :=
    CompareTy.definedUnder_modal_iff.mpr ⟨hb,hm⟩
  have hs : (CompareTy.modal ((if isSum then CompareTy.sum else CompareTy.prod) a b) m).DefinedUnder Δ := by
    apply CompareTy.definedUnder_modal_iff.mpr
    refine ⟨?_,hm⟩
    cases isSum
    · exact CompareTy.definedUnder_prod_iff.mpr ⟨ha,hb⟩
    · exact CompareTy.definedUnder_sum_iff.mpr ⟨ha,hb⟩
  have ht : (CompareTy.modal ((if isSum then CompareTy.sum else CompareTy.prod)
      (.modal a m) (.modal b m)) m).DefinedUnder Δ := by
    apply CompareTy.definedUnder_modal_iff.mpr
    refine ⟨?_,hm⟩
    cases isSum
    · exact CompareTy.definedUnder_prod_iff.mpr ⟨hda,hdb⟩
    · exact CompareTy.definedUnder_sum_iff.mpr ⟨hda,hdb⟩
  have hv := ComparisonStructuralMatrix.equiv_value f (representable hn hs) (representable hn ht) he
  change booleanValue f (.modal ((if isSum then CompareTy.sum else CompareTy.prod) a b) m) =
    booleanValue f (.modal ((if isSum then CompareTy.sum else CompareTy.prod)
      (.modal a m) (.modal b m)) m) at hv
  rw [← h _ hs, ← h _ ht] at hv
  cases isSum <;> exact hv

theorem Represents.pair_values_kind {Δ} {d : Data Δ} {f : LatticeHom (Order Δ .unit) Bool}
    (h : Represents d f) (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    {k : Kind} (hk : k = .prod ∨ k = .sum)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    {m} (hm : Entails Δ (.defined m)) :
    d.transition.apply m ((d.branch k).value k a b) =
      d.transition.apply m ((d.branch k).value k (.modal a m) (.modal b m)) := by
  rcases hk with rfl | rfl
  · exact h.pair_values hn false ha hb hm
  · exact h.pair_values hn true ha hb hm

theorem Represents.fn_values {Δ} {d : Data Δ} {f : LatticeHom (Order Δ .unit) Bool}
    (h : Represents d f) (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    {m n} (hm : Submode Δ m (.compose n .top)) :
    d.transition.apply m ((d.branch .fn).value .fn a b) ≤
      d.transition.apply n ((d.branch .fn).value .fn a b) := by
  have hd := CompareTy.definedUnder_fn_iff.mpr ⟨ha,hb⟩
  have hs := CompareTy.definedUnder_modal_iff.mpr ⟨hd,hm.defined.1⟩
  have ht := CompareTy.definedUnder_modal_iff.mpr
    ⟨hd,(Entails.defined_compose_iff.mp hm.defined.2).1⟩
  have hv := value_mono (Child.ofObserver f) (representable hn hs) (representable hn ht)
    (AlgebraSubtype.fn (.refl (CompareTy.wellShaped_of_no_models hn a))
      (.refl (CompareTy.wellShaped_of_no_models hn b)) hm)
  change booleanValue f (.modal (.fn a b) m) ≤ booleanValue f (.modal (.fn a b) n) at hv
  rw [← h _ hs, ← h _ ht] at hv
  exact hv

theorem Represents.coherent {Δ} {d : Data Δ} {f : LatticeHom (Order Δ .unit) Bool}
    (h : Represents d f) (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) : Coherent d := by
  let z := unitCarrier Δ
  refine ⟨?_, ?_⟩
  · intro k hk m hm x hx
    obtain ⟨a,hax⟩ := hx
    have hax' : booleanValue (d.branch k).child.observer a.type = x :=
      (booleanValue_carrier _ a).trans hax
    have hact := (d.branch k).child.action m hm a.type ⟨a.shaped,a.defined,a.shape_eq⟩
    rw [hax'] at hact
    have hs (v : Bool) : leftSign k v = v := by rcases hk with rfl | rfl <;> rfl
    cases hl : (d.branch k).left
    · have hv := h.pair_values_kind hn hk z.defined a.defined hm
      simp only [Branch.value, hl, Bool.false_eq_true, if_false] at hv
      rw [hax', ← hact] at hv
      exact hv.symm
    · have hv := h.pair_values_kind hn hk a.defined z.defined hm
      simp only [Branch.value, hl, if_true, hs] at hv
      rw [hax', ← hact] at hv
      exact hv.symm
  · intro m n hm x hx
    obtain ⟨a,hax⟩ := hx
    have hax' : booleanValue (d.branch .fn).child.observer a.type = x :=
      (booleanValue_carrier _ a).trans hax
    cases hl : (d.branch .fn).left
    · have hv := h.fn_values hn z.defined a.defined hm
      simpa only [Branch.value, Branch.sign, hl, Bool.false_eq_true, if_false, hax'] using hv
    · have hv := h.fn_values hn a.defined z.defined hm
      simpa only [Branch.value, Branch.sign, hl, if_true, hax'] using hv

/-- Every actual parent provides coherent root data, including one fixed child
choice for each constructor and full modality transfers. -/
theorem extracted_coherent {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (f : LatticeHom (Order Δ .unit) Bool) : Coherent (extracted hn f) :=
  (extracted_represents hn f).coherent hn

/-- Replacing the child observations of any parent extends to another actual
parent with the same finite boundary values. -/
theorem extracted_extension {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Bounds.TypeBoundsDefined Δ) (f : LatticeHom (Order Δ .unit) Bool)
    (children : Kind → Child Δ) (hr : Replacement (extracted hn f) children)
    (boundary : List CompareTy) (hd : DeclaredIn Δ boundary)
    (hp : PortsAgree (extracted hn f) children boundary) :
    ∃ g : LatticeHom (Order Δ .unit) Bool,
      (∀ a, a.DefinedUnder Δ → booleanValue g a = ((extracted hn f).replace children).value a) ∧
      (∀ a ∈ boundary, a.DefinedUnder Δ → booleanValue g a = booleanValue f a) := by
  have hrep := extracted_represents hn f
  obtain ⟨g,hg,hbound⟩ := observer_extension (extracted hn f) (hrep.coherent hn)
    (hrep.bounds hn hΔ) hn hΔ children hr boundary hd hp
  exact ⟨g,hg,fun a ha had => (hbound a ha had).trans (hrep a had)⟩

end ModalityInference.ComparisonObserverGluing
