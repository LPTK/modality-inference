import ModalityInference.Proofs.ComparisonObserverFiniteSuccessors
import ModalityInference.Proofs.ComparisonObserverMachineTransport
import ModalityInference.Proofs.ComparisonStructuralLayout

/-! Genuine observers on a finite, port-closed boundary fold into one finite
machine. The states retain their original guarded modal action and exact range;
finite successor replacement preserves every boundary observation. -/
namespace ModalityInference.ComparisonObserverFiniteMachine

open ComparisonAlgebra ComparisonStructuralLattice ComparisonStructuralLayout
  ComparisonObserverGluing ComparisonObserverProfileExtension
  ComparisonObserverRepresentatives ComparisonObserverActions ComparisonStructuralObservers

abbrev State {Δ : Bounds} {names : Finset ModVar} (hs : Δ.modVars ⊆ names) (boundary : List CompareTy) :=
  {g : Child Δ // g ∈ representatives hs boundary}

noncomputable def next {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy)
    (g : Child Δ) (k : Kind) : State hs boundary :=
  ⟨Classical.choose (representatives_cover hs boundary ((data hn g).branch k).child),
    (Classical.choose_spec (representatives_cover hs boundary ((data hn g).branch k).child)).1⟩

theorem next_spec {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy)
    (g : Child Δ) (k : Kind) :
    (∀ m, Entails Δ (.defined m) → ∀ x,
      (restrictedChild hs ((data hn g).branch k).child).transition.apply m x =
        (next hs hn boundary g k).val.transition.apply m x) ∧
    (∀ x, (restrictedChild hs ((data hn g).branch k).child).Range x ↔
      (next hs hn boundary g k).val.Range x) ∧
    (∀ a ∈ boundary,
      booleanValue (restrictedChild hs ((data hn g).branch k).child).observer a =
        booleanValue (next hs hn boundary g k).val.observer a) :=
  (Classical.choose_spec (representatives_cover hs boundary ((data hn g).branch k).child)).2

noncomputable def nodes {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy) :
    State hs boundary → ComparisonObserverMachine.Node (State hs boundary) := by
  classical
  exact fun i =>
    { atom := (data hn i.val).atom
      unitValue := (data hn i.val).unitValue
      creditValue := (data hn i.val).creditValue
      action := i.val.transition.apply
      branch := fun k => ⟨((data hn i.val).branch k.kind).left,
        next hs hn boundary i.val k.kind⟩
      range := fun x => decide (i.val.Range x) }

theorem modal_valid {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy) :
    ComparisonObserverMachine.ModalValid Δ (nodes hs hn boundary) where
  monotone i := i.val.transition.monotone
  epsilon i := i.val.transition.epsilon
  compose i := i.val.transition.compose
  join i := i.val.transition.join
  meet i := i.val.transition.meet
  submode i := i.val.transition.submode

theorem range_action {Δ} (g : Child Δ) {m : ModExpr} (hm : Entails Δ (.defined m))
    {x : Bool} (hx : g.Range x) : g.Range (g.transition.apply m x) := by
  obtain ⟨a, rfl⟩ := hx
  have ha : Representable Δ .unit a.type := ⟨a.shaped, a.defined, a.shape_eq⟩
  have hv : booleanValue g.observer a.type = observer g.observer a := booleanValue_carrier _ a
  rw [← hv, g.action m hm a.type ha]
  exact g.range_value ⟨ha.1, CompareTy.definedUnder_modal_iff.mpr ⟨ha.2.1, hm⟩, ha.2.2⟩

theorem branch_range {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (g : Child Δ)
    (k : Kind) {x : Bool} (hx : ((data hn g).branch k).child.Range x) :
    g.Range (((data hn g).branch k).sign k x) := by
  obtain ⟨a, hax⟩ := hx
  have hda : (k.op a.type a.type).DefinedUnder Δ := by
    cases k <;> simp only [Kind.op, CompareTy.definedUnder_prod_iff,
      CompareTy.definedUnder_sum_iff, CompareTy.definedUnder_fn_iff] <;>
      exact ⟨a.defined, a.defined⟩
  have hr := data_range hn g hda
  have hv : (data hn g).value (k.op a.type a.type) =
      ((data hn g).branch k).sign k x := by
    have hx' : booleanValue ((data hn g).branch k).child.observer a.type = x :=
      (booleanValue_carrier _ a).trans hax
    cases k <;> simpa only [Kind.op, Data.value, Branch.value, Branch.sign] using
      congrArg (fun b => if ((data hn g).branch _).left then leftSign _ b else b) hx'
  exact hv ▸ hr

theorem range_closed {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy) :
    ComparisonObserverMachine.RangeClosed Δ (nodes hs hn boundary) := by
  classical
  constructor
  · intro i v
    exact decide_eq_true (data_range hn i.val (a := .var v)
      (by intro η h; simp [CompareTy.wellFormedBounds, ModeModels]))
  · intro i
    exact decide_eq_true (data_range hn i.val (a := .unit)
      (by intro η h; simp [CompareTy.wellFormedBounds, ModeModels]))
  · intro i
    exact decide_eq_true (data_range hn i.val (a := .credit)
      (by intro η h; simp [CompareTy.wellFormedBounds, ModeModels]))
  · intro i k x hx
    have hr : (next hs hn boundary i.val k.kind).val.Range x := of_decide_eq_true hx
    have ho := restrictedChild_range hs _ ((next_spec hs hn boundary i.val k.kind).2.1 x |>.mpr hr)
    have hp := branch_range hn i.val k.kind ho
    apply decide_eq_true
    cases k <;> simpa only [nodes, Constructor.kind, ComparisonObserverMachine.sign,
      Constructor.dual, Bool.and_false, Bool.and_true, Bool.false_eq_true,
      if_false, Branch.sign, leftSign, ite_self] using hp
  · intro i m hm x hx
    exact decide_eq_true (range_action i.val hm (of_decide_eq_true hx))

theorem replacement {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy) (g : Child Δ) :
    Replacement (restrictedData hs (data hn g)) (fun k => (next hs hn boundary g k).val) where
  range k x hx := ((next_spec hs hn boundary g k).2.1 x).mpr hx
  action k m hm x _ := ((next_spec hs hn boundary g k).1 m hm x).symm

theorem coherent {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy) :
    ComparisonObserverMachine.Coherent Δ (nodes hs hn boundary) := by
  classical
  have hc (i : State hs boundary) :=
    (restrictedData_coherent hs (data_coherent hn i.val)).replace (replacement hs hn boundary i.val)
  have ht (i : State hs boundary) (m : ModExpr) (x : Bool) :
      (restrictedData hs (data hn i.val)).transition.apply m x = i.val.transition.apply m x :=
    representatives_transfer_fixed hs i.property m x
  constructor
  · intro i k hk m hm x hx
    have hk' : k.kind = .prod ∨ k.kind = .sum := by rcases hk with rfl | rfl <;> simp [Constructor.kind]
    have hr : (next hs hn boundary i.val k.kind).val.Range x := of_decide_eq_true hx
    have hh := (hc i).pair k.kind hk' m hm x hr
    change (restrictedData hs (data hn i.val)).transition.apply m
      ((next hs hn boundary i.val k.kind).val.transition.apply m x) =
      (restrictedData hs (data hn i.val)).transition.apply m x at hh
    simpa only [ht] using hh
  · intro i m n hm x hx
    have hr : (next hs hn boundary i.val .fn).val.Range x := of_decide_eq_true hx
    have hh := (hc i).fn m n hm x hr
    change (restrictedData hs (data hn i.val)).transition.apply m
      (((data hn i.val).branch .fn).sign .fn x) ≤
      (restrictedData hs (data hn i.val)).transition.apply n
        (((data hn i.val).branch .fn).sign .fn x) at hh
    simpa only [ht, nodes, Constructor.kind, ComparisonObserverMachine.sign,
      Constructor.dual, Bool.and_true, Branch.sign, leftSign] using hh

theorem next_value {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy)
    (g : Child Δ) (k : Kind) {a : CompareTy} (ha : a ∈ boundary)
    (had : a.DefinedUnder Δ)
    (has : ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    booleanValue (next hs hn boundary g k).val.observer a =
      booleanValue ((data hn g).branch k).child.observer a := by
  rw [← (next_spec hs hn boundary g k).2.2 a ha]
  change booleanValue (restrictedObserver hs ((data hn g).branch k).child.observer) a = _
  rw [restrictedObserver_booleanValue hs _ (representable hn had), restrictedType_fixed has]

theorem value_eq {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (boundary : List CompareTy)
    (hp : PortsClosed boundary) :
    ∀ a : CompareTy, a.DefinedUnder Δ →
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a →
      (∀ p ∈ ports a, p.2 ∈ boundary) → ∀ i : State hs boundary,
      ComparisonObserverMachine.value (nodes hs hn boundary) a i =
        booleanValue i.val.observer a := by
  intro a
  induction a with
  | var v =>
    intro ha _ _ i
    exact data_represents hn i.val _ ha
  | unit =>
    intro ha _ _ i
    exact data_represents hn i.val _ ha
  | credit =>
    intro ha _ _ i
    exact data_represents hn i.val _ ha
  | prod a b iha ihb =>
    intro ha hs' hp' i
    obtain ⟨had, hbd⟩ := CompareTy.definedUnder_prod_iff.mp ha
    obtain ⟨has, hbs⟩ := hs'
    have ham := hp' (.prod, a) (by simp [ports])
    have hbm := hp' (.prod, b) (by simp [ports])
    have ea := (iha had has (hp a ham) (next hs hn boundary i.val .prod)).trans
      (next_value hs hn boundary i.val .prod ham had has)
    have eb := (ihb hbd hbs (hp b hbm) (next hs hn boundary i.val .prod)).trans
      (next_value hs hn boundary i.val .prod hbm hbd hbs)
    calc
      _ = (data hn i.val).value (.prod a b) := by
        simp only [ComparisonObserverMachine.value, nodes, Constructor.kind,
          Data.value, Branch.value, leftSign, ea, eb]
      _ = _ := data_represents hn i.val _ ha
  | sum a b iha ihb =>
    intro ha hs' hp' i
    obtain ⟨had, hbd⟩ := CompareTy.definedUnder_sum_iff.mp ha
    obtain ⟨has, hbs⟩ := hs'
    have ham := hp' (.sum, a) (by simp [ports])
    have hbm := hp' (.sum, b) (by simp [ports])
    have ea := (iha had has (hp a ham) (next hs hn boundary i.val .sum)).trans
      (next_value hs hn boundary i.val .sum ham had has)
    have eb := (ihb hbd hbs (hp b hbm) (next hs hn boundary i.val .sum)).trans
      (next_value hs hn boundary i.val .sum hbm hbd hbs)
    calc
      _ = (data hn i.val).value (.sum a b) := by
        simp only [ComparisonObserverMachine.value, nodes, Constructor.kind,
          Data.value, Branch.value, leftSign, ea, eb]
      _ = _ := data_represents hn i.val _ ha
  | fn a b iha ihb =>
    intro ha hs' hp' i
    obtain ⟨had, hbd⟩ := CompareTy.definedUnder_fn_iff.mp ha
    obtain ⟨has, hbs⟩ := hs'
    have ham := hp' (.fn, a) (by simp [ports])
    have hbm := hp' (.fn, b) (by simp [ports])
    have ea := (iha had has (hp a ham) (next hs hn boundary i.val .fn)).trans
      (next_value hs hn boundary i.val .fn ham had has)
    have eb := (ihb hbd hbs (hp b hbm) (next hs hn boundary i.val .fn)).trans
      (next_value hs hn boundary i.val .fn hbm hbd hbs)
    calc
      _ = (data hn i.val).value (.fn a b) := by
        simp only [ComparisonObserverMachine.value, nodes, Constructor.kind,
          Data.value, Branch.value, leftSign, ea, eb]
      _ = _ := data_represents hn i.val _ ha
  | modal a m ih =>
    intro ha hs' hp' i
    obtain ⟨had, hm⟩ := CompareTy.definedUnder_modal_iff.mp ha
    change i.val.transition.apply m (ComparisonObserverMachine.value (nodes hs hn boundary) a i) = _
    rw [ih had hs'.1 hp' i]
    exact i.val.action m hm a (representable hn had)
  | join a b iha ihb =>
    intro ha hs' hp' i
    obtain ⟨had, hbd⟩ := CompareTy.definedUnder_join_iff.mp ha
    have ea := iha had hs'.1 (fun p hm => hp' p (List.mem_append_left _ hm)) i
    have eb := ihb hbd hs'.2 (fun p hm => hp' p (List.mem_append_right _ hm)) i
    have hr := data_represents hn i.val (.join a b) ha
    simp only [Data.value, data_represents hn i.val a had, data_represents hn i.val b hbd] at hr
    exact (congrArg₂ (· || ·) ea eb).trans hr
  | meet a b iha ihb =>
    intro ha hs' hp' i
    obtain ⟨had, hbd⟩ := CompareTy.definedUnder_meet_iff.mp ha
    have ea := iha had hs'.1 (fun p hm => hp' p (List.mem_append_left _ hm)) i
    have eb := ihb hbd hs'.2 (fun p hm => hp' p (List.mem_append_right _ hm)) i
    have hr := data_represents hn i.val (.meet a b) ha
    simp only [Data.value, data_represents hn i.val a had, data_represents hn i.val b hbd] at hr
    exact (congrArg₂ (· && ·) ea eb).trans hr

theorem bounds_hold {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (boundary : List CompareTy) (hp : PortsClosed boundary) (hd : DeclaredIn Δ boundary)
    (hsb : ∀ a ∈ boundary, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    ComparisonObserverMachine.BoundsHold Δ (nodes hs hn boundary) := by
  intro i a b hab
  obtain ⟨ham, hbm⟩ := hd a b hab
  have had := (CompareTy.definedUnder_ofTy a Δ).mpr (hΔ a b hab).1
  have hbd := (CompareTy.definedUnder_ofTy b Δ).mpr (hΔ a b hab).2
  rw [value_eq hs hn boundary hp _ had (hsb _ ham) (hp _ ham),
    value_eq hs hn boundary hp _ hbd (hsb _ hbm) (hp _ hbm)]
  have hh := data_bounds hn hΔ i.val a b hab
  rw [data_represents hn i.val _ had, data_represents hn i.val _ hbd] at hh
  exact hh

theorem certified {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (boundary : List CompareTy) (hp : PortsClosed boundary) (hd : DeclaredIn Δ boundary)
    (hsb : ∀ a ∈ boundary, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    ComparisonObserverMachine.Certified Δ (nodes hs hn boundary) :=
  ⟨modal_valid hs hn boundary, range_closed hs hn boundary, coherent hs hn boundary,
    bounds_hold hs hn hΔ boundary hp hd hsb⟩

/-- A single finite certified machine realizes all genuine observer patterns
on the boundary. Its size depends on that boundary and modality-name support. -/
theorem bounded_machine {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (boundary : List CompareTy) (hp : PortsClosed boundary) (hd : DeclaredIn Δ boundary)
    (hsb : ∀ a ∈ boundary, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    ∃ count ≤ 2 ^ (2 * (8 + 10 * names.card) + 2 + boundary.length),
      ∃ machine : ComparisonObserverMachine.Machine count,
      ComparisonObserverMachine.Certified Δ machine ∧
      ∀ f : LatticeHom (Order Δ .unit) Bool, ∃ i : Fin count,
        ∀ a ∈ boundary, a.DefinedUnder Δ →
          ComparisonObserverMachine.value machine a i = booleanValue f a := by
  classical
  let e := (Fintype.equivFin (State hs boundary)).symm
  refine ⟨Fintype.card (State hs boundary), ?_,
    ComparisonObserverMachine.transport e (nodes hs hn boundary),
    (certified hs hn hΔ boundary hp hd hsb).transport e, ?_⟩
  · exact (Fintype.card_coe (representatives hs boundary)).le.trans (representatives_card hs boundary)
  · intro f
    obtain ⟨r, hr, _, _, hv⟩ := representatives_cover hs boundary (Child.ofObserver f)
    let j : State hs boundary := ⟨r, hr⟩
    refine ⟨e.symm j, ?_⟩
    intro a ha had
    rw [ComparisonObserverMachine.transport_value, Equiv.apply_symm_apply,
      value_eq hs hn boundary hp _ had (hsb a ha) (hp a ha)]
    change booleanValue r.observer a = booleanValue f a
    rw [← hv a ha]
    change booleanValue (restrictedObserver hs f) a = booleanValue f a
    rw [restrictedObserver_booleanValue hs f (representable hn had),
      restrictedType_fixed (hsb a ha)]

/-- Finite certified machines are an exact bounded test of an individual
defined comparison once its whole declared boundary is included. -/
theorem subtype_iff_bounded_machines {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (boundary : List CompareTy) (hp : PortsClosed boundary) (hd : DeclaredIn Δ boundary)
    (hsb : ∀ a ∈ boundary, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    {a b : CompareTy} (ham : a ∈ boundary) (hbm : b ∈ boundary)
    (had : a.DefinedUnder Δ) (hbd : b.DefinedUnder Δ) :
    AlgebraSubtype Δ a b ↔
      ∀ count ≤ 2 ^ (2 * (8 + 10 * names.card) + 2 + boundary.length),
      ∀ machine : ComparisonObserverMachine.Machine count,
      ComparisonObserverMachine.Certified Δ machine → ∀ i,
        ComparisonObserverMachine.value machine a i ≤ ComparisonObserverMachine.value machine b i := by
  constructor
  · intro hab count _ machine hc i
    exact ComparisonObserverMachine.subtype_mono hc.modal hc.range hc.coherent hc.bounds hΔ had hbd hab i
  · intro hh
    obtain ⟨count, hc, machine, hm, hf⟩ := bounded_machine hs hn hΔ boundary hp hd hsb
    apply (subtype_iff_boolean_observers (represented (representable hn had))
      (represented (representable hn hbd))).mpr
    intro f
    obtain ⟨i, hi⟩ := hf f
    have he := hh count hc machine hm i
    rw [hi a ham had, hi b hbm hbd, booleanValue_represented _ _ (representable hn had),
      booleanValue_represented _ _ (representable hn hbd)] at he
    exact he

end ModalityInference.ComparisonObserverFiniteMachine
