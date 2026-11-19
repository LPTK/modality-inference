import ModalityInference.Proofs.ComparisonRelativeSyntax
import ModalityInference.Proofs.ComparisonRelativeControlProjection
import ModalityInference.Proofs.ComparisonFiniteControlRange

/-! Agreement with the finite defined range algebra supplies every guarded
equation and clamp rule. The hypotheses compare primitive finite operations;
they contain no assumption about the original subtyping relation. -/
namespace ModalityInference.ComparisonRelativeSyntax

open ComparisonRelativeCoordinates ComparisonFiniteControls ComparisonFiniteControlProjection
  ComparisonFiniteControlRange ComparisonObserverMachine ComparisonObserverFiniteRange
  ComparisonStructuralLayout

noncomputable section

variable {Δ : Bounds} {names : List ModVar} {State : Type} {nodes : State → Node State}
  {A O : Type*} {embed : A → O → Bool}
  (S : Model Δ (Control Δ names) A O embed)
  (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes)
  (hnames : Δ.modVars ⊆ names.toFinset)
  (j : LatticeHom (ComparisonObserverFiniteRange.Value nodes)
    (Coordinates (Control Δ names) (O → Bool)))

structure DefinedAgreement : Prop where
  controls : ∀ m hm, S.controls.toFun m hm = project hnames m hm
  reflect : ∀ {x y}, j x ≤ j y → x ≤ y
  atom : ∀ v, S.atom v = j (atom hr v)
  unit : S.unit = j (unit hr)
  credit : S.credit = j (credit hr)
  action : ∀ m x, shift S.mul_mono m (j x) = j (action hv hr m x)
  prod : ∀ x y, pair (S.prodTable none) (S.prod_order none) (j x) (j y) = j (op hr .prod x y)
  sum : ∀ x y, pair (S.sumTable none) (S.sum_order none) (j x) (j y) = j (op hr .sum x y)
  fn : ∀ x y, fn S.fnTable S.fn_order (j x) (j y) = j (op hr .fn x y)

namespace DefinedAgreement

variable {S hv hr hnames j} (h : DefinedAgreement S hv hr hnames j)

include h

theorem denote_defined {a : CompareTy} (ha : a.DefinedUnder Δ) :
    S.denote a none = j (evaluate hr hnames a ha) := by
  induction a with
  | var v => exact h.atom v
  | unit => exact h.unit
  | credit => exact h.credit
  | prod a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_prod_iff.mp ha
    change pair (S.prodTable none) (S.prod_order none) (S.denote a none) (S.denote b none) = _
    rw [iha ha,ihb hb,h.prod]
    exact congrArg j (evaluate_op hr hnames .prod a b ha hb).symm
  | sum a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_sum_iff.mp ha
    change pair (S.sumTable none) (S.sum_order none) (S.denote a none) (S.denote b none) = _
    rw [iha ha,ihb hb,h.sum]
    exact congrArg j (evaluate_op hr hnames .sum a b ha hb).symm
  | fn a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_fn_iff.mp ha
    change ComparisonRelativeCoordinates.fn S.fnTable S.fn_order (S.denote a none) (S.denote b none) = _
    rw [iha ha,ihb hb,h.fn]
    exact congrArg j (evaluate_op hr hnames .fn a b ha hb).symm
  | modal a m ih =>
    obtain ⟨ha,hm⟩ := CompareTy.definedUnder_modal_iff.mp ha
    rw [S.denote_modal_total hm, ih ha, h.controls, h.action,
      evaluate_modal hv hr hnames a ha m hm]
  | join a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_join_iff.mp ha
    change S.denote a none ⊔ S.denote b none = _
    rw [iha ha,ihb hb,← map_sup,evaluate_sup hr hnames a b ha hb]
  | meet a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_meet_iff.mp ha
    change S.denote a none ⊓ S.denote b none = _
    rw [iha ha,ihb hb,← map_inf,evaluate_inf hr hnames a b ha hb]

theorem reflect_defined {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hab : S.Related a b) : evaluate hr hnames a ha ≤ evaluate hr hnames b hb := by
  apply h.reflect
  rw [← h.denote_defined ha, ← h.denote_defined hb]
  exact hab

theorem equation {a b : CompareTy} (hab : ComparisonAlgebra.Equation Δ a b) :
    S.denote a none = S.denote b none := by
  rw [h.denote_defined (ComparisonDefinedCovers.equation_defined hab).1,
    h.denote_defined (ComparisonDefinedCovers.equation_defined hab).2,
    evaluate_equation hv hr hnames hab]

theorem clamp {b a t : CompareTy} {m : ModExpr}
    (hb : b.DefinedUnder Δ) (ha : a.DefinedUnder Δ) (ht : t.DefinedUnder Δ)
    (hm : Entails Δ (.defined m)) (hba : S.Related b a) (hat : S.Related a t) :
    S.denote (.modal a m) none =
      S.denote (.meet (.join a (.modal b m)) (.modal t m)) none := by
  have he (x : CompareTy) (hx : x.DefinedUnder Δ) :
      S.denote (.modal x m) none =
        j (ComparisonFiniteControlRange.action hv hr (project hnames m hm) (evaluate hr hnames x hx)) := by
    rw [S.denote_modal_total hm,h.denote_defined hx,h.controls,h.action]
  change S.denote (.modal a m) none =
    (S.denote a none ⊔ S.denote (.modal b m) none) ⊓ S.denote (.modal t m) none
  rw [he a ha,he b hb,he t ht,h.denote_defined ha,← map_sup,← map_inf]
  exact congrArg j (action_clamp hv hr (project hnames m hm)
    (h.reflect_defined hb ha hba) (h.reflect_defined ha ht hat))

/-- The complete original algebra is sound once the finite raw-bound checks
and the primitive defined-operation agreement are supplied. -/
theorem algebra_sound
    (hb : ∀ a b, Constraint.sub a b ∈ Δ → S.Related (.ofTy a) (.ofTy b))
    {a b : CompareTy} (hab : AlgebraSubtype Δ a b) : S.Related a b := by
  induction hab with
  | shaped hs => exact S.shaped_sound hb hs
  | trans _ _ ih ih' => exact .trans S ih ih'
  | equation he => exact le_of_eq (h.equation he)
  | equationRev he => exact le_of_eq (h.equation he).symm
  | congr _ hm ih => exact .congr S ih hm
  | prod _ _ ih ih' => exact .prod S ih ih'
  | sum _ _ ih ih' => exact .sum S ih ih'
  | fn _ _ hm ih ih' => exact .fn S ih ih' hm
  | joinLeast _ _ ih ih' => exact .joinLeast S ih ih'
  | meetGreatest _ _ ih ih' => exact .meetGreatest S ih ih'
  | clamp hba hat hm _ _ ih ih' =>
    exact le_of_eq (h.clamp hba.2.1 hba.2.2 hat.2.2 hm ih ih')
  | clampRev hba hat hm _ _ ih ih' =>
    exact le_of_eq (h.clamp hba.2.1 hba.2.2 hat.2.2 hm ih ih').symm

end DefinedAgreement
end
end ModalityInference.ComparisonRelativeSyntax
