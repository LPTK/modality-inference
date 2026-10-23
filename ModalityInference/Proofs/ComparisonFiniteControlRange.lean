import ModalityInference.Proofs.ComparisonFiniteControlProjection
import ModalityInference.Proofs.ComparisonObserverFiniteRange

/-! Finite controls act on every value of a certified range algebra. The
projected evaluator retains the original guarded equations and clamp law. -/
namespace ModalityInference.ComparisonFiniteControlRange

open ComparisonFiniteControls ComparisonFiniteControlProjection ComparisonModeRestriction
  ComparisonObserverMachine ComparisonObserverFiniteRange ComparisonStructuralLayout

noncomputable section

variable {Δ : Bounds} {names : List ModVar} {State : Type} {nodes : State → Node State}
  (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes)

include hv

theorem modal_equivalent {m n : ModExpr} (hm : Entails Δ (.defined m))
    (hn : Entails Δ (.defined n)) (h : Submode Δ m n ∧ Submode Δ n m) (x : ComparisonObserverFiniteRange.Value nodes) :
    modal hr m hm x = modal hr n hn x :=
  le_antisymm (modal_submode hr hv m n hm hn h.1 x) (modal_submode hr hv n m hn hm h.2 x)

def action (m : Control Δ names) : LatticeHom (ComparisonObserverFiniteRange.Value nodes) (ComparisonObserverFiniteRange.Value nodes) where
  toFun := modal hr (expression m) (expression_defined m)
  map_sup' := modal_sup hr hv _ _
  map_inf' := modal_inf hr hv _ _

theorem action_index (x : ComparisonObserverFiniteRange.Value nodes) : Monotone (fun m : Control Δ names => action hv hr m x) :=
  fun m n h => modal_submode hr hv _ _ (expression_defined m) (expression_defined n) ((le_iff_submode _ _).mp h) x

theorem action_one (x : ComparisonObserverFiniteRange.Value nodes) : action hv hr (1 : Control Δ names) x = x :=
  (modal_equivalent (n := .epsilon) hv hr (expression_defined (1 : Control Δ names)) (fun _ _ => rfl) expression_one x).trans (modal_epsilon hr hv (fun _ _ => rfl) x)

theorem action_mul (m n : Control Δ names) (x : ComparisonObserverFiniteRange.Value nodes) :
    action hv hr (m * n) x = action hv hr n (action hv hr m x) :=
  (modal_equivalent hv hr (expression_defined (m * n))
    (expression_mul m n).1.defined.2 (expression_mul m n) x).trans
    (modal_compose hr hv _ _ (expression_defined m) (expression_defined n)
      (expression_mul m n).1.defined.2 x)

theorem action_encode (m : ModExpr) (hm : Entails Δ (.defined m))
    (hs : m.vars ⊆ names.toFinset) (x : ComparisonObserverFiniteRange.Value nodes) :
    action hv hr (encode m hm hs) x = modal hr m hm x :=
  modal_equivalent hv hr (expression_defined (encode m hm hs)) hm (expression_encode m hm hs) x

theorem action_pair_absorb (hc : Coherent Δ nodes) (k : Constructor)
    (hk : k = .prod ∨ k = .sum) (m : Control Δ names) (x y : ComparisonObserverFiniteRange.Value nodes) :
    action hv hr m (op hr k (action hv hr m x) (action hv hr m y)) =
      action hv hr m (op hr k x y) := pair_absorb hr hc k hk _ (expression_defined m) x y

theorem action_fn_index (hc : Coherent Δ nodes) {m n : Control Δ names}
    (h : FutureLe m n) (x y : ComparisonObserverFiniteRange.Value nodes) :
    action hv hr m (op hr .fn x y) ≤ action hv hr n (op hr .fn x y) :=
  fn_future hr hc _ _ (expression_defined m) (expression_defined n) ((futureLe_iff_submode m n).mp h) x y

theorem action_clamp (m : Control Δ names) {b a u : ComparisonObserverFiniteRange.Value nodes} (hba : b ≤ a) (hau : a ≤ u) :
    action hv hr m a = (a ⊔ action hv hr m b) ⊓ action hv hr m u :=
  modal_clamp hr hv _ (expression_defined m) hba hau

variable (hnames : Δ.modVars ⊆ names.toFinset)

def evaluate (a : CompareTy) (ha : a.DefinedUnder Δ) : ComparisonObserverFiniteRange.Value nodes :=
  eval hr (a.subst CompareTy.var (restrict names.toFinset))
    ((restrict_fixed Δ names.toFinset hnames).type_defined ha)

theorem action_project (m : ModExpr) (hm : Entails Δ (.defined m))
    (x : ComparisonObserverFiniteRange.Value nodes) :
    action hv hr (project hnames m hm) x = modal hr (m.subst (restrict names.toFinset))
      ((restrict_fixed Δ names.toFinset hnames).defined hm) x :=
  action_encode hv hr _ _ _ x

omit hv in
theorem evaluate_var (v : TypeVar) (ha : (CompareTy.var v).DefinedUnder Δ) :
    evaluate hr hnames (.var v) ha = atom hr v := rfl

omit hv in
theorem evaluate_unit (ha : CompareTy.unit.DefinedUnder Δ) :
    evaluate hr hnames .unit ha = unit hr := rfl

omit hv in
theorem evaluate_credit (ha : CompareTy.credit.DefinedUnder Δ) :
    evaluate hr hnames .credit ha = credit hr := rfl

theorem evaluate_modal (a : CompareTy) (ha : a.DefinedUnder Δ) (m : ModExpr)
    (hm : Entails Δ (.defined m)) :
    evaluate hr hnames (.modal a m) (CompareTy.definedUnder_modal_iff.mpr ⟨ha,hm⟩) =
      action hv hr (project hnames m hm) (evaluate hr hnames a ha) :=
  (action_project hv hr hnames m hm (evaluate hr hnames a ha)).symm

omit hv in
theorem evaluate_sup (a b : CompareTy) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    evaluate hr hnames (.join a b) (CompareTy.definedUnder_join_iff.mpr ⟨ha,hb⟩) =
      evaluate hr hnames a ha ⊔ evaluate hr hnames b hb :=
  eval_sup hr _ _ ((restrict_fixed Δ names.toFinset hnames).type_defined ha)
    ((restrict_fixed Δ names.toFinset hnames).type_defined hb)

omit hv in
theorem evaluate_inf (a b : CompareTy) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    evaluate hr hnames (.meet a b) (CompareTy.definedUnder_meet_iff.mpr ⟨ha,hb⟩) =
      evaluate hr hnames a ha ⊓ evaluate hr hnames b hb :=
  eval_inf hr _ _ ((restrict_fixed Δ names.toFinset hnames).type_defined ha)
    ((restrict_fixed Δ names.toFinset hnames).type_defined hb)

omit hv in
theorem evaluate_op (k : Constructor) (a b : CompareTy) (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    evaluate hr hnames (k.op a b) (op_defined k ha hb) =
      op hr k (evaluate hr hnames a ha) (evaluate hr hnames b hb) := by
  have h := eval_op hr k _ _
    ((restrict_fixed Δ names.toFinset hnames).type_defined ha)
    ((restrict_fixed Δ names.toFinset hnames).type_defined hb)
  cases k <;> exact h

theorem evaluate_equation {a b : CompareTy} (h : ComparisonAlgebra.Equation Δ a b) :
    evaluate hr hnames a (ComparisonDefinedCovers.equation_defined h).1 =
      evaluate hr hnames b (ComparisonDefinedCovers.equation_defined h).2 :=
  value_ext (fun i => equation_value hv ((restrict_fixed Δ names.toFinset hnames).equation h) i)

omit hv in
theorem evaluate_raw (a : Ty) (ha : (CompareTy.ofTy a).DefinedUnder Δ)
    (hs : a.modVars ⊆ names.toFinset) :
    evaluate hr hnames (.ofTy a) ha = eval hr (.ofTy a) ha :=
  value_ext (fun i => congrArg (fun t => ComparisonObserverMachine.value nodes t i)
    (ofTy_fixed a (fun v hv => by simp only [restrict,if_pos (hs hv)])))

theorem evaluate_clamp (b a u : CompareTy) (hb : b.DefinedUnder Δ)
    (ha : a.DefinedUnder Δ) (hu : u.DefinedUnder Δ) (m : ModExpr)
    (hm : Entails Δ (.defined m))
    (hba : evaluate hr hnames b hb ≤ evaluate hr hnames a ha)
    (hau : evaluate hr hnames a ha ≤ evaluate hr hnames u hu) :
    evaluate hr hnames (.modal a m) (CompareTy.definedUnder_modal_iff.mpr ⟨ha,hm⟩) =
      (evaluate hr hnames a ha ⊔
        evaluate hr hnames (.modal b m) (CompareTy.definedUnder_modal_iff.mpr ⟨hb,hm⟩)) ⊓
        evaluate hr hnames (.modal u m) (CompareTy.definedUnder_modal_iff.mpr ⟨hu,hm⟩) := by
  exact (evaluate_modal hv hr hnames a ha m hm).trans
    ((action_clamp hv hr (project hnames m hm) hba hau).trans
      (congrArg₂ (· ⊓ ·)
        (congrArg (fun x => evaluate hr hnames a ha ⊔ x)
          (evaluate_modal hv hr hnames b hb m hm).symm)
        (evaluate_modal hv hr hnames u hu m hm).symm))

end
end ModalityInference.ComparisonFiniteControlRange
