import ModalityInference.ComparisonObserverMachine
import ModalityInference.Proofs.ComparisonTotalDerivation
import ModalityInference.Proofs.ComparisonObserverActions

/-! A recursive family of Boolean observers is sound by induction on fully
defined derivations. The certificate retains each whole declared edge and
checks constructor coherence on a closed overapproximation of child ranges. -/
namespace ModalityInference.ComparisonObserverMachine

open ComparisonAlgebra ComparisonStructuralLayout ComparisonStructuralLattice
  ComparisonObserverActions

variable {State : Type}

@[simp] theorem value_constructor (nodes : State → Node State) (i : State)
    (k : Constructor) (a b : CompareTy) :
    value nodes (k.op a b) i = branchValue nodes i k a b := by
  cases k <;> simp [Constructor.op, value, branchValue, sign, Constructor.dual]

/-- Every modal obligation is relative to the original guard context. -/
structure ModalValid (Δ : Bounds) (nodes : State → Node State) : Prop where
  monotone : ∀ i m, Entails Δ (.defined m) → Monotone ((nodes i).action m)
  epsilon : ∀ i x, (nodes i).action .epsilon x = x
  compose : ∀ i m n, Entails Δ (.defined m) → Entails Δ (.defined n) → ∀ x,
    (nodes i).action (.compose m n) x = (nodes i).action n ((nodes i).action m x)
  join : ∀ i m n, Entails Δ (.defined m) → Entails Δ (.defined n) → ∀ x,
    (nodes i).action (.join m n) x = ((nodes i).action m x || (nodes i).action n x)
  meet : ∀ i m n, Entails Δ (.defined m) → Entails Δ (.defined n) → ∀ x,
    (nodes i).action (.meet m n) x = ((nodes i).action m x && (nodes i).action n x)
  submode : ∀ i m n, Submode Δ m n → ∀ x,
    (nodes i).action m x ≤ (nodes i).action n x

def ModalValid.transition {Δ} {nodes : State → Node State} (h : ModalValid Δ nodes) (i : State) : Transition Δ where
  apply := (nodes i).action
  monotone := h.monotone i
  epsilon := h.epsilon i
  compose := h.compose i
  join := h.join i
  meet := h.meet i
  submode := h.submode i

/-- Closure makes the finite flags cover every value of a defined finite term;
flags need not be exact ranges. -/
structure RangeClosed (Δ : Bounds) (nodes : State → Node State) : Prop where
  atom : ∀ i v, (nodes i).range ((nodes i).atom v) = true
  unit : ∀ i, (nodes i).range (nodes i).unitValue = true
  credit : ∀ i, (nodes i).range (nodes i).creditValue = true
  branch : ∀ i k x, (nodes ((nodes i).branch k).next).range x = true →
    (nodes i).range (sign k ((nodes i).branch k).left x) = true
  modal : ∀ i m, Entails Δ (.defined m) → ∀ x, (nodes i).range x = true →
    (nodes i).range ((nodes i).action m x) = true

theorem RangeClosed.value_mem {Δ nodes} (h : RangeClosed Δ nodes) {a : CompareTy}
    (ha : a.DefinedUnder Δ) (i : State) : (nodes i).range (value nodes a i) = true := by
  induction a generalizing i with
  | var v => exact h.atom i v
  | unit => exact h.unit i
  | credit => exact h.credit i
  | prod a b iha ihb =>
    obtain ⟨ha, hb⟩ := CompareTy.definedUnder_prod_iff.mp ha
    have hl := h.branch i .prod _ (iha ha ((nodes i).branch .prod).next)
    have hr := h.branch i .prod _ (ihb hb ((nodes i).branch .prod).next)
    cases he : ((nodes i).branch .prod).left <;>
      simp_all [value, sign, Constructor.dual]
  | sum a b iha ihb =>
    obtain ⟨ha, hb⟩ := CompareTy.definedUnder_sum_iff.mp ha
    have hl := h.branch i .sum _ (iha ha ((nodes i).branch .sum).next)
    have hr := h.branch i .sum _ (ihb hb ((nodes i).branch .sum).next)
    cases he : ((nodes i).branch .sum).left <;>
      simp_all [value, sign, Constructor.dual]
  | fn a b iha ihb =>
    obtain ⟨ha, hb⟩ := CompareTy.definedUnder_fn_iff.mp ha
    have hl := h.branch i .fn _ (iha ha ((nodes i).branch .fn).next)
    have hr := h.branch i .fn _ (ihb hb ((nodes i).branch .fn).next)
    cases he : ((nodes i).branch .fn).left <;>
      simp_all [value, sign, Constructor.dual]
  | modal a m ih =>
    obtain ⟨ha, hm⟩ := CompareTy.definedUnder_modal_iff.mp ha
    exact h.modal i m hm _ (ih ha i)
  | join a b iha ihb | meet a b iha ihb =>
    have ha' : a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
      simpa only [CompareTy.definedUnder_join_iff, CompareTy.definedUnder_meet_iff] using ha
    have hl := iha ha'.1 i
    have hr := ihb ha'.2 i
    cases he : value nodes a i <;> cases hf : value nodes b i <;> simp_all [value]

structure Coherent (Δ : Bounds) (nodes : State → Node State) : Prop where
  pair : ∀ i k, k = Constructor.prod ∨ k = Constructor.sum → ∀ m,
    Entails Δ (.defined m) → ∀ x,
    (nodes ((nodes i).branch k).next).range x = true →
      (nodes i).action m ((nodes ((nodes i).branch k).next).action m x) =
        (nodes i).action m x
  fn : ∀ i m n, Submode Δ m (.compose n .top) → ∀ x,
    (nodes ((nodes i).branch .fn).next).range x = true →
      (nodes i).action m (sign .fn ((nodes i).branch .fn).left x) ≤
        (nodes i).action n (sign .fn ((nodes i).branch .fn).left x)

def BoundsHold (Δ : Bounds) (nodes : State → Node State) : Prop :=
  ∀ i a b, Constraint.sub a b ∈ Δ → value nodes (.ofTy a) i ≤ value nodes (.ofTy b) i

theorem Coherent.fn_step {Δ} {nodes : State → Node State}
    (hc : Coherent Δ nodes) (hr : RangeClosed Δ nodes) (hmv : ModalValid Δ nodes)
    {a b c d : CompareTy} (hc' : c.DefinedUnder Δ) (hd : d.DefinedUnder Δ)
    {m n} (hm : Submode Δ m (.compose n .top))
    (hca : ∀ j, value nodes c j ≤ value nodes a j)
    (hbd : ∀ j, value nodes b j ≤ value nodes d j) (i : State) :
    (nodes i).action m (branchValue nodes i .fn a b) ≤
      (nodes i).action n (branchValue nodes i .fn c d) := by
  have hab : branchValue nodes i .fn a b ≤ branchValue nodes i .fn c d := by
    have ha := hca ((nodes i).branch .fn).next
    have hb := hbd ((nodes i).branch .fn).next
    cases hleft : ((nodes i).branch .fn).left
    · simpa only [branchValue, hleft, Bool.false_eq_true, if_false] using hb
    · simp only [branchValue, hleft, if_true, sign, Constructor.dual, Bool.true_and]
      cases he : value nodes a ((nodes i).branch .fn).next <;>
        cases hf : value nodes c ((nodes i).branch .fn).next <;> simp_all [Bool.le_iff_imp]
  apply (hmv.monotone i m hm.defined.1 hab).trans
  have h₁ := hc.fn i m n hm _ (hr.value_mem hc' ((nodes i).branch .fn).next)
  have h₂ := hc.fn i m n hm _ (hr.value_mem hd ((nodes i).branch .fn).next)
  cases hleft : ((nodes i).branch .fn).left <;>
    simp_all [branchValue, sign, Constructor.dual]

theorem Coherent.pair_action {Δ} {nodes : State → Node State}
    (hc : Coherent Δ nodes) (hr : RangeClosed Δ nodes)
    {k : Constructor} (hk : k = .prod ∨ k = .sum)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    {m} (hm : Entails Δ (.defined m)) (i : State) :
    (nodes i).action m (branchValue nodes i k a b) =
      (nodes i).action m (branchValue nodes i k (.modal a m) (.modal b m)) := by
  have h₁ := hc.pair i k hk m hm _ (hr.value_mem ha ((nodes i).branch k).next)
  have h₂ := hc.pair i k hk m hm _ (hr.value_mem hb ((nodes i).branch k).next)
  cases he : ((nodes i).branch k).left <;> rcases hk with rfl | rfl <;>
    simp_all [branchValue, sign, Constructor.dual, value]

theorem Coherent.pair_step {Δ} {nodes : State → Node State}
    (hc : Coherent Δ nodes) (hr : RangeClosed Δ nodes) (hmv : ModalValid Δ nodes)
    {k : Constructor} (hk : k = .prod ∨ k = .sum)
    {a b c d : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hc' : c.DefinedUnder Δ) (hd : d.DefinedUnder Δ)
    {m} (hm : Entails Δ (.defined m))
    (h₁ : ∀ j, value nodes (.modal a m) j ≤ value nodes (.modal c m) j)
    (h₂ : ∀ j, value nodes (.modal b m) j ≤ value nodes (.modal d m) j) (i : State) :
    (nodes i).action m (branchValue nodes i k a b) ≤
      (nodes i).action m (branchValue nodes i k c d) := by
  rw [hc.pair_action hr hk ha hb hm, hc.pair_action hr hk hc' hd hm]
  apply hmv.monotone i m hm
  have h₁ := h₁ ((nodes i).branch k).next
  have h₂ := h₂ ((nodes i).branch k).next
  cases he : ((nodes i).branch k).left <;> rcases hk with rfl | rfl <;>
    simpa only [branchValue, he, sign, Constructor.dual, Bool.true_and,
      Bool.false_and, Bool.false_eq_true, if_false, if_true] using (by first | exact h₂ | exact h₁)

theorem branch_diagonal (nodes : State → Node State) (i : State) (k : Constructor)
    (p : Bool) (a b c d : CompareTy) :
    branchValue nodes i k (typeOp (if k.dual then !p else p) a c) (typeOp p b d) =
      if p then branchValue nodes i k a b || branchValue nodes i k c d
      else branchValue nodes i k a b && branchValue nodes i k c d := by
  cases he : ((nodes i).branch k).left <;> cases k <;> cases p <;>
    simp [branchValue, he, sign, Constructor.dual, typeOp, value]

theorem equation_value {Δ} {nodes : State → Node State} (hv : ModalValid Δ nodes)
    {a b} (h : ComparisonAlgebra.Equation Δ a b) (i : State) :
    value nodes a i = value nodes b i := by
  cases h with
  | distrib p hab hac =>
    rename_i a b c
    cases p <;> simp only [typeOp, Bool.false_eq_true, Bool.not_false, Bool.not_true,
      if_false, if_true, value]
    all_goals cases value nodes a i <;> cases value nodes b i <;> cases value nodes c i <;> rfl
  | modal p _ hm =>
    cases p
    · exact (hv.transition i).modal_meet hm _ _
    · exact (hv.transition i).modal_join hm _ _
  | scalar p _ _ hm hn =>
    cases p
    · exact (hv.transition i).meet _ _ hm hn _
    · exact (hv.transition i).join _ _ hm hn _
  | prod p hac hbe =>
    rename_i a b c e
    have hh := branch_diagonal nodes i .prod p a b c e
    cases p <;> simpa [value, branchValue, sign, Constructor.dual, typeOp] using hh.symm
  | sum p hac hbe =>
    rename_i a b c e
    have hh := branch_diagonal nodes i .sum p a b c e
    cases p <;> simpa [value, branchValue, sign, Constructor.dual, typeOp] using hh.symm
  | fn p hac hbe =>
    rename_i a b c e
    have hh := branch_diagonal nodes i .fn p a b c e
    cases p <;> simpa [value, branchValue, sign, Constructor.dual, typeOp] using hh.symm

theorem trace_mono {Δ} {nodes : State → Node State}
    (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes) (hc : Coherent Δ nodes)
    (hb : BoundsHold Δ nodes) {a b} (h : ComparisonTotalDerivation.Derivation Δ a b) :
    ∀ i, value nodes a i ≤ value nodes b i := by
  induction h with
  | refl _ _ => exact fun _ => le_rfl
  | bound h _ _ => exact fun i => hb i _ _ h
  | identity _ _ => exact fun i => le_of_eq (hv.epsilon i _)
  | identityRev _ _ => exact fun i => le_of_eq (hv.epsilon i _).symm
  | compose _ _ hm hn => exact fun i => le_of_eq (hv.compose i _ _ hm hn _).symm
  | composeRev _ _ hm hn => exact fun i => le_of_eq (hv.compose i _ _ hm hn _)
  | trans _ _ ih₁ ih₂ => exact fun i => (ih₁ i).trans (ih₂ i)
  | congr _ hm ih =>
    exact fun i => (hv.monotone i _ hm.defined.1 (ih i)).trans (hv.submode i _ _ hm _)
  | prod h₁ h₂ hs ht ih₁ ih₂ =>
    obtain ⟨⟨ha,hb⟩,hm⟩ := (CompareTy.definedUnder_modal_iff.mp hs).imp_left
      CompareTy.definedUnder_prod_iff.mp
    obtain ⟨hc',hd⟩ := CompareTy.definedUnder_prod_iff.mp
      (CompareTy.definedUnder_modal_iff.mp ht).1
    exact hc.pair_step hr hv (Or.inl rfl) ha hb hc' hd hm ih₁ ih₂
  | sum h₁ h₂ hs ht ih₁ ih₂ =>
    obtain ⟨⟨ha,hb⟩,hm⟩ := (CompareTy.definedUnder_modal_iff.mp hs).imp_left
      CompareTy.definedUnder_sum_iff.mp
    obtain ⟨hc',hd⟩ := CompareTy.definedUnder_sum_iff.mp
      (CompareTy.definedUnder_modal_iff.mp ht).1
    exact hc.pair_step hr hv (Or.inr rfl) ha hb hc' hd hm ih₁ ih₂
  | fn h₁ h₂ hm hs ht ih₁ ih₂ =>
    obtain ⟨hc',hd⟩ := CompareTy.definedUnder_fn_iff.mp
      (CompareTy.definedUnder_modal_iff.mp ht).1
    exact hc.fn_step hr hv hc' hd hm ih₁ ih₂
  | joinLeft _ =>
    exact fun _ => Bool.le_iff_imp.mpr (fun h => by simp only [value, h, Bool.true_or])
  | joinRight _ =>
    exact fun _ => Bool.le_iff_imp.mpr (fun h => by simp only [value, h, Bool.or_true])
  | joinLeast _ _ ih₁ ih₂ => exact fun i => sup_le (ih₁ i) (ih₂ i)
  | meetLeft _ => exact fun _ => Bool.le_iff_imp.mpr (fun h => (Bool.and_eq_true_iff.mp h).1)
  | meetRight _ => exact fun _ => Bool.le_iff_imp.mpr (fun h => (Bool.and_eq_true_iff.mp h).2)
  | meetGreatest _ _ ih₁ ih₂ => exact fun i => le_inf (ih₁ i) (ih₂ i)
  | equation h => exact fun i => le_of_eq (equation_value hv h i)
  | equationRev h => exact fun i => le_of_eq (equation_value hv h i).symm
  | clamp _ _ hm _ _ ih₁ ih₂ =>
    exact fun i => le_of_eq ((hv.transition i).clamp hm (ih₁ i) (ih₂ i))
  | clampRev _ _ hm _ _ ih₁ ih₂ =>
    exact fun i => le_of_eq ((hv.transition i).clamp hm (ih₁ i) (ih₂ i)).symm

/-- A cyclic state graph is a sound observer family whenever its local
certificates hold. The proof recurses on derivations, never on graph edges. -/
theorem subtype_mono {Δ} {nodes : State → Node State}
    (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes) (hc : Coherent Δ nodes)
    (hb : BoundsHold Δ nodes) (hΔ : Bounds.TypeBoundsDefined Δ) {a b}
    (ha : CompareTy.DefinedUnder a Δ) (hb' : CompareTy.DefinedUnder b Δ)
    (h : AlgebraSubtype Δ a b) (i : State) : value nodes a i ≤ value nodes b i :=
  trace_mono hv hr hc hb (ComparisonTotalDerivation.derivation hΔ ha hb' h) i

noncomputable def observer {Δ shape} {nodes : State → Node State}
    (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes) (hc : Coherent Δ nodes)
    (hb : BoundsHold Δ nodes) (hΔ : Bounds.TypeBoundsDefined Δ) (i : State) :
    LatticeHom (Order Δ shape) Bool where
  toFun := Quotient.lift (fun a : Carrier Δ shape => value nodes a.type i) (by
    intro a b hab
    exact le_antisymm (subtype_mono hv hr hc hb hΔ a.defined b.defined hab.1 i)
      (subtype_mono hv hr hc hb hΔ b.defined a.defined hab.2 i))
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

theorem observer_value {Δ shape} {nodes : State → Node State}
    (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes) (hc : Coherent Δ nodes)
    (hb : BoundsHold Δ nodes) (hΔ : Bounds.TypeBoundsDefined Δ) (i : State)
    (a : Carrier Δ shape) :
    ComparisonAlgebra.observer (observer hv hr hc hb hΔ i) a = value nodes a.type i := rfl

/-- The local semantic certificate contains no recursive observer premise. -/
structure Certified (Δ : Bounds) (nodes : State → Node State) : Prop where
  modal : ModalValid Δ nodes
  range : RangeClosed Δ nodes
  coherent : Coherent Δ nodes
  bounds : BoundsHold Δ nodes

noncomputable def Certified.observer {Δ shape} {nodes : State → Node State}
    (h : Certified Δ nodes) (hΔ : Bounds.TypeBoundsDefined Δ) (i : State) :
    LatticeHom (Order Δ shape) Bool := ComparisonObserverMachine.observer h.modal h.range h.coherent h.bounds hΔ i

theorem Certified.observer_value {Δ shape} {nodes : State → Node State}
    (h : Certified Δ nodes) (hΔ : Bounds.TypeBoundsDefined Δ) (i : State)
    (a : Carrier Δ shape) :
    ComparisonAlgebra.observer (h.observer hΔ i) a = value nodes a.type i := rfl

end ModalityInference.ComparisonObserverMachine
