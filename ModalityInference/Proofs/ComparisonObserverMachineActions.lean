import ModalityInference.Proofs.ComparisonObserverMachine

/-! Replacing modal actions only on uninhabited fibers preserves every defined
observation and the complete finite-machine certificate. -/
namespace ModalityInference.ComparisonObserverMachine

variable {State : Type}

def withActions (nodes : State → Node State) (actions : State → ModExpr → Bool → Bool)
    (i : State) : Node State := { nodes i with action := actions i }

def ActionsAgree (Δ : Bounds) (nodes : State → Node State)
    (actions : State → ModExpr → Bool → Bool) : Prop :=
  ∀ i m, Entails Δ (.defined m) → ∀ x, (nodes i).range x = true →
    actions i m x = (nodes i).action m x

theorem withActions_value {Δ} {nodes : State → Node State} {actions}
    (hr : RangeClosed Δ nodes) (he : ActionsAgree Δ nodes actions)
    {a : CompareTy} (ha : a.DefinedUnder Δ) (i : State) :
    value (withActions nodes actions) a i = value nodes a i := by
  induction a generalizing i with
  | var | unit | credit => rfl
  | prod a b iha ihb =>
    obtain ⟨ha, hb⟩ := CompareTy.definedUnder_prod_iff.mp ha
    simp only [value, withActions, iha ha, ihb hb]
  | sum a b iha ihb =>
    obtain ⟨ha, hb⟩ := CompareTy.definedUnder_sum_iff.mp ha
    simp only [value, withActions, iha ha, ihb hb]
  | fn a b iha ihb =>
    obtain ⟨ha, hb⟩ := CompareTy.definedUnder_fn_iff.mp ha
    simp only [value, withActions, iha ha, ihb hb]
  | modal a m ih =>
    obtain ⟨ha, hm⟩ := CompareTy.definedUnder_modal_iff.mp ha
    simp only [value, withActions, ih ha]
    exact he i m hm _ (hr.value_mem ha i)
  | join a b iha ihb =>
    obtain ⟨ha, hb⟩ := CompareTy.definedUnder_join_iff.mp ha
    exact congrArg₂ (· || ·) (iha ha i) (ihb hb i)
  | meet a b iha ihb =>
    obtain ⟨ha, hb⟩ := CompareTy.definedUnder_meet_iff.mp ha
    exact congrArg₂ (· && ·) (iha ha i) (ihb hb i)

theorem RangeClosed.withActions {Δ} {nodes : State → Node State} {actions}
    (hr : RangeClosed Δ nodes) (he : ActionsAgree Δ nodes actions) :
    RangeClosed Δ (ComparisonObserverMachine.withActions nodes actions) := by
  refine ⟨hr.atom, hr.unit, hr.credit, hr.branch, ?_⟩
  intro i m hm x hx
  change (nodes i).range (actions i m x) = true
  rw [he i m hm x hx]
  exact hr.modal i m hm x hx

theorem RangeClosed.pair_fiber {Δ} {nodes : State → Node State} (hr : RangeClosed Δ nodes)
    (i : State) {k : ComparisonStructuralLayout.Constructor} (hk : k = .prod ∨ k = .sum)
    {x : Bool} (hx : (nodes ((nodes i).branch k).next).range x = true) :
    (nodes i).range x = true := by
  have hh := hr.branch i k x hx
  rcases hk with rfl | rfl <;> simpa [sign, ComparisonStructuralLayout.Constructor.dual] using hh

theorem Coherent.withActions {Δ} {nodes : State → Node State} {actions}
    (hc : Coherent Δ nodes) (hr : RangeClosed Δ nodes) (he : ActionsAgree Δ nodes actions) :
    Coherent Δ (ComparisonObserverMachine.withActions nodes actions) := by
  constructor
  · intro i k hk m hm x hx
    change (nodes ((nodes i).branch k).next).range x = true at hx
    change actions i m (actions ((nodes i).branch k).next m x) = actions i m x
    have hp := hr.pair_fiber i hk hx
    have hq := hr.pair_fiber i hk (hr.modal ((nodes i).branch k).next m hm x hx)
    rw [he _ m hm x hx, he i m hm _ hq, he i m hm x hp]
    exact hc.pair i k hk m hm x hx
  · intro i m n hm x hx
    change (nodes ((nodes i).branch .fn).next).range x = true at hx
    change actions i m (sign .fn ((nodes i).branch .fn).left x) ≤
      actions i n (sign .fn ((nodes i).branch .fn).left x)
    have hrx := hr.branch i .fn x hx
    rw [he i m hm.defined.1 _ hrx,
      he i n (Entails.defined_compose_iff.mp hm.defined.2).1 _ hrx]
    exact hc.fn i m n hm x hx

theorem Certified.withActions {Δ} {nodes : State → Node State} {actions}
    (hc : Certified Δ nodes) (hΔ : Δ.TypeBoundsDefined)
    (he : ActionsAgree Δ nodes actions)
    (hm : ModalValid Δ (ComparisonObserverMachine.withActions nodes actions)) :
    Certified Δ (ComparisonObserverMachine.withActions nodes actions) := by
  refine ⟨hm, hc.range.withActions he, hc.coherent.withActions hc.range he, ?_⟩
  intro i a b hab
  rw [withActions_value hc.range he ((CompareTy.definedUnder_ofTy a Δ).mpr (hΔ a b hab).1),
    withActions_value hc.range he ((CompareTy.definedUnder_ofTy b Δ).mpr (hΔ a b hab).2)]
  exact hc.bounds i a b hab

end ModalityInference.ComparisonObserverMachine
