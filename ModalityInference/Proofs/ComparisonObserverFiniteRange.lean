import ModalityInference.Proofs.ComparisonObserverMachine

/-! A certified observer machine acts on the complete product of its allowed
Boolean ranges. Its algebraic laws hold on all product values, whether or not
those values are represented by a finite term. Finite state sets give finite
defined algebras. -/
namespace ModalityInference.ComparisonObserverFiniteRange

open ComparisonAlgebra ComparisonStructuralLayout ComparisonObserverMachine

variable {State : Type} {Δ : Bounds} {nodes : State → Node State}

abbrev Fiber (nodes : State → Node State) (i : State) :=
  {b : Bool // (nodes i).range b = true}

noncomputable instance fiberFintype (nodes : State → Node State) (i : State) :
    Fintype (Fiber nodes i) := Fintype.ofFinite _

abbrev Value (nodes : State → Node State) := ∀ i, Fiber nodes i

noncomputable instance valueFintype [Fintype State] (nodes : State → Node State) :
    Fintype (Value nodes) := by
  classical
  exact Pi.instFintype

def unit (hr : RangeClosed Δ nodes) : Value nodes :=
  fun i => ⟨(nodes i).unitValue,hr.unit i⟩

def credit (hr : RangeClosed Δ nodes) : Value nodes :=
  fun i => ⟨(nodes i).creditValue,hr.credit i⟩

def atom (hr : RangeClosed Δ nodes) (v : TypeVar) : Value nodes :=
  fun i => ⟨(nodes i).atom v,hr.atom i v⟩

@[simp] theorem atom_val (hr : RangeClosed Δ nodes) (v : TypeVar) (i : State) :
    (atom hr v i).val = (nodes i).atom v := rfl

def modal (hr : RangeClosed Δ nodes) (m : ModExpr) (hm : Entails Δ (.defined m))
    (x : Value nodes) : Value nodes :=
  fun i => ⟨(nodes i).action m (x i).val,hr.modal i m hm _ (x i).property⟩

def op (hr : RangeClosed Δ nodes) (k : Constructor) (x y : Value nodes) : Value nodes :=
  fun i =>
    let b := (nodes i).branch k
    if b.left then ⟨sign k b.left (x b.next).val,hr.branch i k _ (x b.next).property⟩
    else ⟨sign k b.left (y b.next).val,hr.branch i k _ (y b.next).property⟩

@[ext] theorem value_ext {x y : Value nodes} (h : ∀ i, (x i).val = (y i).val) : x = y :=
  funext fun i => Subtype.ext (h i)

@[simp] theorem modal_val (hr : RangeClosed Δ nodes) (m : ModExpr)
    (hm : Entails Δ (.defined m)) (x : Value nodes) (i : State) :
    (modal hr m hm x i).val = (nodes i).action m (x i).val := rfl

theorem op_val (hr : RangeClosed Δ nodes) (k : Constructor) (x y : Value nodes) (i : State) :
    (op hr k x y i).val =
      if ((nodes i).branch k).left then sign k true (x ((nodes i).branch k).next).val
      else (y ((nodes i).branch k).next).val := by
  simp only [op]
  split <;> simp_all [sign]

theorem pair_absorb (hr : RangeClosed Δ nodes) (hc : Coherent Δ nodes)
    (k : Constructor) (hk : k = .prod ∨ k = .sum)
    (m : ModExpr) (hm : Entails Δ (.defined m)) (x y : Value nodes) :
    modal hr m hm (op hr k (modal hr m hm x) (modal hr m hm y)) =
      modal hr m hm (op hr k x y) := by
  apply value_ext
  intro i
  have hs (b : Bool) : sign k true b = b := by rcases hk with rfl | rfl <;> rfl
  simp only [modal_val,op_val,hs]
  split
  · exact hc.pair i k hk m hm _ (x ((nodes i).branch k).next).property
  · exact hc.pair i k hk m hm _ (y ((nodes i).branch k).next).property

theorem fn_future (hr : RangeClosed Δ nodes) (hc : Coherent Δ nodes)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (h : Submode Δ m (.compose n .top)) (x y : Value nodes) :
    modal hr m hm (op hr .fn x y) ≤ modal hr n hn (op hr .fn x y) := by
  intro i
  change (nodes i).action m (op hr .fn x y i).val ≤
    (nodes i).action n (op hr .fn x y i).val
  simp only [op]
  split
  · exact hc.fn i m n h _ (x ((nodes i).branch .fn).next).property
  · exact hc.fn i m n h _ (y ((nodes i).branch .fn).next).property

theorem card_value [Fintype State] : Fintype.card (Value nodes) ≤ 2 ^ Fintype.card State := by
  classical
  calc
    Fintype.card (Value nodes) ≤ Fintype.card (State → Bool) :=
      Fintype.card_le_of_injective (fun x i => (x i).val)
        (fun _ _ h => value_ext (fun i => congrFun h i))
    _ = _ := by simp

theorem value_nonempty (hr : RangeClosed Δ nodes) : Nonempty (Value nodes) := ⟨unit hr⟩

@[simp] theorem sup_val (x y : Value nodes) (i : State) :
    ((x ⊔ y) i).val = ((x i).val || (y i).val) := by
  change (max (x i) (y i)).val = _
  simp only [max_def]
  split
  · rename_i h
    change (x i).val ≤ (y i).val at h
    cases hx : (x i).val <;> cases hy : (y i).val <;> simp_all [Bool.le_iff_imp]
  · rename_i h
    change ¬ (x i).val ≤ (y i).val at h
    cases hx : (x i).val <;> cases hy : (y i).val <;> simp_all [Bool.le_iff_imp]

@[simp] theorem inf_val (x y : Value nodes) (i : State) :
    ((x ⊓ y) i).val = ((x i).val && (y i).val) := by
  change (min (x i) (y i)).val = _
  simp only [min_def]
  split
  · rename_i h
    change (x i).val ≤ (y i).val at h
    cases hx : (x i).val <;> cases hy : (y i).val <;> simp_all [Bool.le_iff_imp]
  · rename_i h
    change ¬ (x i).val ≤ (y i).val at h
    cases hx : (x i).val <;> cases hy : (y i).val <;> simp_all [Bool.le_iff_imp]

theorem modal_mono (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (m : ModExpr) (hm : Entails Δ (.defined m)) : Monotone (modal hr m hm) :=
  fun _ _ h i => hv.monotone i m hm (h i)

theorem modal_submode (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (h : Submode Δ m n) (x : Value nodes) : modal hr m hm x ≤ modal hr n hn x :=
  fun i => hv.submode i m n h (x i).val

theorem modal_epsilon (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (hε : Entails Δ (.defined .epsilon)) (x : Value nodes) : modal hr .epsilon hε x = x := by
  apply value_ext
  exact fun i => hv.epsilon i _

theorem modal_compose (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hmn : Entails Δ (.defined (.compose m n))) (x : Value nodes) :
    modal hr (.compose m n) hmn x = modal hr n hn (modal hr m hm x) := by
  apply value_ext
  exact fun i => hv.compose i m n hm hn _

theorem modal_sup (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (m : ModExpr) (hm : Entails Δ (.defined m)) (x y : Value nodes) :
    modal hr m hm (x ⊔ y) = modal hr m hm x ⊔ modal hr m hm y := by
  apply value_ext
  intro i
  simp only [modal_val,sup_val]
  exact (hv.transition i).modal_join hm _ _

theorem modal_inf (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (m : ModExpr) (hm : Entails Δ (.defined m)) (x y : Value nodes) :
    modal hr m hm (x ⊓ y) = modal hr m hm x ⊓ modal hr m hm y := by
  apply value_ext
  intro i
  simp only [modal_val,inf_val]
  exact (hv.transition i).modal_meet hm _ _

theorem pair_mono (hr : RangeClosed Δ nodes) (k : Constructor)
    (hk : k = .prod ∨ k = .sum) {x y u v : Value nodes} (hxu : x ≤ u) (hyv : y ≤ v) :
    op hr k x y ≤ op hr k u v := by
  intro i
  change (op hr k x y i).val ≤ (op hr k u v i).val
  have hs (b : Bool) : sign k true b = b := by rcases hk with rfl | rfl <;> rfl
  simp only [op_val,hs]
  split
  · exact hxu _
  · exact hyv _

theorem fn_mono (hr : RangeClosed Δ nodes) {x y u v : Value nodes}
    (hux : u ≤ x) (hyv : y ≤ v) : op hr .fn x y ≤ op hr .fn u v := by
  intro i
  change (op hr .fn x y i).val ≤ (op hr .fn u v i).val
  simp only [op_val,sign,Constructor.dual,Bool.true_and,if_true]
  split
  · have h := hux ((nodes i).branch .fn).next
    change (u _).val ≤ (x _).val at h
    cases hx : (x ((nodes i).branch .fn).next).val <;>
      cases hu : (u ((nodes i).branch .fn).next).val <;> simp_all [Bool.le_iff_imp]
  · exact hyv _

theorem pair_sup (hr : RangeClosed Δ nodes) (k : Constructor)
    (hk : k = .prod ∨ k = .sum) (x y u v : Value nodes) :
    op hr k (x ⊔ u) (y ⊔ v) = op hr k x y ⊔ op hr k u v := by
  apply value_ext
  intro i
  have hs (b : Bool) : sign k true b = b := by rcases hk with rfl | rfl <;> rfl
  simp only [sup_val,op_val,hs]
  split <;> simp_all

theorem pair_inf (hr : RangeClosed Δ nodes) (k : Constructor)
    (hk : k = .prod ∨ k = .sum) (x y u v : Value nodes) :
    op hr k (x ⊓ u) (y ⊓ v) = op hr k x y ⊓ op hr k u v := by
  apply value_ext
  intro i
  have hs (b : Bool) : sign k true b = b := by rcases hk with rfl | rfl <;> rfl
  simp only [inf_val,op_val,hs]
  split <;> simp_all

theorem fn_sup (hr : RangeClosed Δ nodes) (x y u v : Value nodes) :
    op hr .fn (x ⊓ u) (y ⊔ v) = op hr .fn x y ⊔ op hr .fn u v := by
  apply value_ext
  intro i
  simp only [sup_val,inf_val,op_val,sign,Constructor.dual,Bool.true_and,if_true]
  split <;> simp_all

theorem fn_inf (hr : RangeClosed Δ nodes) (x y u v : Value nodes) :
    op hr .fn (x ⊔ u) (y ⊓ v) = op hr .fn x y ⊓ op hr .fn u v := by
  apply value_ext
  intro i
  simp only [sup_val,inf_val,op_val,sign,Constructor.dual,Bool.true_and,if_true]
  split <;> simp_all

theorem modal_join_mode (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hmn : Entails Δ (.defined (.join m n))) (x : Value nodes) :
    modal hr (.join m n) hmn x = modal hr m hm x ⊔ modal hr n hn x := by
  apply value_ext
  intro i
  simp only [modal_val,sup_val]
  exact hv.join i m n hm hn _

theorem modal_meet_mode (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (m n : ModExpr) (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hmn : Entails Δ (.defined (.meet m n))) (x : Value nodes) :
    modal hr (.meet m n) hmn x = modal hr m hm x ⊓ modal hr n hn x := by
  apply value_ext
  intro i
  simp only [modal_val,inf_val]
  exact hv.meet i m n hm hn _

theorem modal_clamp (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {b a u : Value nodes}
    (hba : b ≤ a) (hau : a ≤ u) :
    modal hr m hm a = (a ⊔ modal hr m hm b) ⊓ modal hr m hm u := by
  apply value_ext
  intro i
  simp only [modal_val,inf_val,sup_val]
  exact (hv.transition i).clamp hm (hba i) (hau i)

theorem pair_step (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (hc : Coherent Δ nodes) (k : Constructor) (hk : k = .prod ∨ k = .sum)
    (m : ModExpr) (hm : Entails Δ (.defined m)) {x y u v : Value nodes}
    (hxu : modal hr m hm x ≤ modal hr m hm u)
    (hyv : modal hr m hm y ≤ modal hr m hm v) :
    modal hr m hm (op hr k x y) ≤ modal hr m hm (op hr k u v) := by
  rw [← pair_absorb hr hc k hk m hm x y,← pair_absorb hr hc k hk m hm u v]
  exact modal_mono hr hv m hm (pair_mono hr k hk hxu hyv)

theorem fn_step (hr : RangeClosed Δ nodes) (hv : ModalValid Δ nodes)
    (hc : Coherent Δ nodes) (m n : ModExpr)
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (h : Submode Δ m (.compose n .top)) {x y u v : Value nodes}
    (hux : u ≤ x) (hyv : y ≤ v) :
    modal hr m hm (op hr .fn x y) ≤ modal hr n hn (op hr .fn u v) :=
  (modal_mono hr hv m hm (fn_mono hr hux hyv)).trans (fn_future hr hc m n hm hn h u v)

def eval (hr : RangeClosed Δ nodes) (a : CompareTy) (ha : a.DefinedUnder Δ) : Value nodes :=
  fun i => ⟨ComparisonObserverMachine.value nodes a i,hr.value_mem ha i⟩

@[simp] theorem eval_val (hr : RangeClosed Δ nodes) (a : CompareTy)
    (ha : a.DefinedUnder Δ) (i : State) :
    (eval hr a ha i).val = ComparisonObserverMachine.value nodes a i := rfl

theorem eval_var (hr : RangeClosed Δ nodes) (v : TypeVar) (ha : (CompareTy.var v).DefinedUnder Δ) :
    eval hr (.var v) ha = atom hr v := rfl

theorem eval_unit (hr : RangeClosed Δ nodes) (ha : CompareTy.unit.DefinedUnder Δ) :
    eval hr .unit ha = unit hr := rfl

theorem eval_credit (hr : RangeClosed Δ nodes) (ha : CompareTy.credit.DefinedUnder Δ) :
    eval hr .credit ha = credit hr := rfl

theorem eval_modal (hr : RangeClosed Δ nodes) (m : ModExpr) (hm : Entails Δ (.defined m))
    (a : CompareTy) (ha : a.DefinedUnder Δ) :
    eval hr (.modal a m) (CompareTy.definedUnder_modal_iff.mpr ⟨ha,hm⟩) =
      modal hr m hm (eval hr a ha) := rfl

theorem eval_sup (hr : RangeClosed Δ nodes) (a b : CompareTy)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    eval hr (.join a b) (CompareTy.definedUnder_join_iff.mpr ⟨ha,hb⟩) =
      eval hr a ha ⊔ eval hr b hb := by
  apply value_ext
  intro i
  rw [sup_val]
  rfl

theorem eval_inf (hr : RangeClosed Δ nodes) (a b : CompareTy)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    eval hr (.meet a b) (CompareTy.definedUnder_meet_iff.mpr ⟨ha,hb⟩) =
      eval hr a ha ⊓ eval hr b hb := by
  apply value_ext
  intro i
  rw [inf_val]
  rfl

theorem op_defined (k : Constructor) {a b : CompareTy}
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) : (k.op a b).DefinedUnder Δ := by
  cases k <;> exact CompareTy.definedUnder_prod_iff.mpr ⟨ha,hb⟩

theorem eval_op (hr : RangeClosed Δ nodes) (k : Constructor) (a b : CompareTy)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    eval hr (k.op a b) (op_defined k ha hb) = op hr k (eval hr a ha) (eval hr b hb) := by
  apply value_ext
  intro i
  rw [op_val]
  cases k <;> simp only [eval_val,Constructor.op,ComparisonObserverMachine.value,
    sign,Constructor.dual,Bool.and_false,Bool.and_true,Bool.false_eq_true,if_false,if_true]

theorem eval_mono (hc : Certified Δ nodes) (hΔ : Δ.TypeBoundsDefined)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (h : AlgebraSubtype Δ a b) : eval hc.range a ha ≤ eval hc.range b hb :=
  ComparisonObserverMachine.subtype_mono hc.modal hc.range hc.coherent hc.bounds hΔ ha hb h

theorem eval_bound (hc : Certified Δ nodes) (hΔ : Δ.TypeBoundsDefined)
    {a b : Ty} (hab : Constraint.sub a b ∈ Δ) :
    eval hc.range (.ofTy a) ((CompareTy.definedUnder_ofTy a Δ).mpr (hΔ a b hab).1) ≤
      eval hc.range (.ofTy b) ((CompareTy.definedUnder_ofTy b Δ).mpr (hΔ a b hab).2) :=
  fun i => hc.bounds i a b hab

end ModalityInference.ComparisonObserverFiniteRange
