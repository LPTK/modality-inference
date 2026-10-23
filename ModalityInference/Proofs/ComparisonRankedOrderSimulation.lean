import ModalityInference.Proofs.ComparisonRankedBasis
import ModalityInference.Proofs.ComparisonObserverMachine

/-! Exact one-level tests for positive observer links. Different constructor
selectors expose independent operands, so their comparison reduces to a
constant boundary on one child. These tests preserve function-domain variance.
They do not exchange finite-rank approximation with graph reachability. -/
namespace ModalityInference.ComparisonRankedOrderSimulation

open ComparisonObserverMachine ComparisonStructuralLayout ComparisonRankedBasis
  ComparisonControls ComparisonStructuralBasis

def On {α : Type*} (P : α → Prop) (f g : α → Bool) : Prop :=
  ∀a, P a → f a ≤ g a

def Constant {α : Type*} (P : α → Prop) (f : α → Bool) (b : Bool) : Prop :=
  ∀a, P a → f a = b

theorem independent_le_iff {α : Type*} (P : α → Prop) (f g : α → Bool) :
    (∀a, P a → ∀b, P b → f a ≤ g b) ↔
      Constant P f false ∨ Constant P g true := by
  classical
  constructor
  · intro h
    by_cases hf : Constant P f false
    · exact .inl hf
    · simp only [Constant, not_forall, Bool.not_eq_false] at hf
      obtain ⟨a, ha, hfa⟩ := hf
      exact .inr (fun b hb => Bool.eq_true_of_true_le (hfa ▸ h a ha b hb))
  · rintro (hf | hg) a ha b hb
    · exact hf a ha ▸ Bool.false_le _
    · exact hg b hb ▸ Bool.le_true _

def select {α : Type*} (left : Bool) (f : α → Bool) (a b : α) : Bool :=
  if left then f a else f b

def SelectorTest {α : Type*} (P : α → Prop) (left right : Bool)
    (f g : α → Bool) : Prop :=
  if left = right then On P f g
  else Constant P f false ∨ Constant P g true

theorem selector_le_iff {α : Type*} (P : α → Prop) (left right : Bool)
    (f g : α → Bool) :
    (∀a, P a → ∀b, P b → select left f a b ≤ select right g a b) ↔
      SelectorTest P left right f g := by
  cases left <;> cases right <;> simp only [select, SelectorTest, Bool.false_eq_true,
    Bool.true_eq_false, if_false, if_true]
  · exact ⟨fun h a ha => h a ha a ha, fun h _ _ b hb => h b hb⟩
  · exact ⟨fun h => (independent_le_iff P f g).mp (fun a ha b hb => h b hb a ha),
      fun h a ha b hb => (independent_le_iff P f g).mpr h b hb a ha⟩
  · exact independent_le_iff P f g
  · exact ⟨fun h a ha => h a ha a ha, fun h a ha _ _ => h a ha⟩

theorem negate_le (a b : Bool) : ((!a) ≤ (!b)) ↔ b ≤ a := by
  cases a <;> cases b <;> decide

def BranchTest {α : Type*} (P : α → Prop) (kind : Constructor)
    (left right : Bool) (f g : α → Bool) : Prop :=
  match left, right with
  | false, false => On P f g
  | true, true => if kind.dual then On P g f else On P f g
  | true, false => Constant P f kind.dual ∨ Constant P g true
  | false, true => Constant P f false ∨ Constant P g (!kind.dual)

theorem branch_test_iff {α : Type*} (P : α → Prop) (kind : Constructor)
    (left right : Bool) (f g : α → Bool) :
    SelectorTest P left right (fun a => sign kind left (f a))
      (fun a => sign kind right (g a)) ↔ BranchTest P kind left right f g := by
  cases kind <;> cases left <;> cases right <;>
    simp [SelectorTest, BranchTest, sign, Constructor.dual, On, Constant, negate_le]

theorem constructor_select {State : Type} (nodes : State → Node State)
    (i : State) (kind : Constructor) (a b : CompareTy) :
    value nodes (kind.op a b) i = select ((nodes i).branch kind).left
      (fun t => sign kind ((nodes i).branch kind).left
        (value nodes t ((nodes i).branch kind).next)) a b := by
  cases h : ((nodes i).branch kind).left <;>
    simp [value_constructor, branchValue, select, h, sign]

theorem constructor_order_iff {State : Type} (nodes : State → Node State)
    (i j : State) (kind : Constructor) (P : CompareTy → Prop) :
    (∀a, P a → ∀b, P b → value nodes (kind.op a b) i ≤
      value nodes (kind.op a b) j) ↔
      BranchTest P kind ((nodes i).branch kind).left ((nodes j).branch kind).left
        (fun t => value nodes t ((nodes i).branch kind).next)
        (fun t => value nodes t ((nodes j).branch kind).next) := by
  simpa only [constructor_select] using
    (selector_le_iff P ((nodes i).branch kind).left ((nodes j).branch kind).left
      (fun t => sign kind ((nodes i).branch kind).left
        (value nodes t ((nodes i).branch kind).next))
      (fun t => sign kind ((nodes j).branch kind).left
        (value nodes t ((nodes j).branch kind).next))).trans
      (branch_test_iff P kind ((nodes i).branch kind).left ((nodes j).branch kind).left
        (fun t => value nodes t ((nodes i).branch kind).next)
        (fun t => value nodes t ((nodes j).branch kind).next))

theorem pairs_order_iff {State : Type} (nodes : State → Node State)
    (i j : State) (kind : Constructor) (terms : List CompareTy) :
    On (· ∈ pairs kind.op terms terms) (fun t => value nodes t i)
      (fun t => value nodes t j) ↔
      BranchTest (· ∈ terms) kind ((nodes i).branch kind).left
        ((nodes j).branch kind).left
        (fun t => value nodes t ((nodes i).branch kind).next)
        (fun t => value nodes t ((nodes j).branch kind).next) := by
  simpa only [On, pairs, List.forall_mem_flatMap, List.forall_mem_map] using
    constructor_order_iff nodes i j kind (· ∈ terms)

def ChildTest {State : Type} (nodes : State → Node State) (terms : List CompareTy)
    (i j : State) (kind : Constructor) : Prop :=
  BranchTest (· ∈ terms) kind ((nodes i).branch kind).left ((nodes j).branch kind).left
    (fun t => value nodes t ((nodes i).branch kind).next)
    (fun t => value nodes t ((nodes j).branch kind).next)

theorem heads_order_step {State : Type} (nodes : State → Node State)
    (names : List TypeVar) (modes : List ModVar) (n : Nat) (i j : State) :
    On (· ∈ (ComparisonRankedBasis.basis names modes (n+1)).heads)
      (fun t => value nodes t i) (fun t => value nodes t j) ↔
      (nodes i).unitValue ≤ (nodes j).unitValue ∧
      On (· ∈ (ComparisonRankedBasis.basis names modes n).types)
        (fun t => value nodes t i) (fun t => value nodes t j) ∧
      ChildTest nodes (ComparisonRankedBasis.basis names modes n).types i j .prod ∧
      ChildTest nodes (ComparisonRankedBasis.basis names modes n).types i j .sum ∧
      ChildTest nodes (ComparisonRankedBasis.basis names modes n).types i j .fn := by
  simp only [ChildTest, ←pairs_order_iff, On, ComparisonRankedBasis.basis, Basis.heads,
    List.forall_mem_cons, List.forall_mem_append, Constructor.op, value, and_assoc]

theorem selector_constant_iff {α : Type*} (P : α → Prop) (left : Bool)
    (f : α → Bool) (c : Bool) :
    (∀a, P a → ∀b, P b → select left f a b = c) ↔ Constant P f c := by
  cases left <;> simp only [select, Bool.false_eq_true, if_false, if_true, Constant]
  · exact ⟨fun h a ha => h a ha a ha, fun h _ _ b hb => h b hb⟩
  · exact ⟨fun h a ha => h a ha a ha, fun h a ha _ _ => h a ha⟩

theorem sign_constant_iff {α : Type*} (P : α → Prop) (kind : Constructor)
    (left : Bool) (f : α → Bool) (c : Bool) :
    Constant P (fun a => sign kind left (f a)) c ↔
      Constant P f (sign kind left c) := by
  cases kind <;> cases left <;> cases c <;> simp [Constant, sign, Constructor.dual]

theorem pairs_constant_iff {State : Type} (nodes : State → Node State)
    (i : State) (kind : Constructor) (terms : List CompareTy) (c : Bool) :
    Constant (· ∈ pairs kind.op terms terms) (fun t => value nodes t i) c ↔
      Constant (· ∈ terms) (fun t => value nodes t ((nodes i).branch kind).next)
        (sign kind ((nodes i).branch kind).left c) := by
  simpa only [Constant, pairs, List.forall_mem_flatMap, List.forall_mem_map,
    constructor_select] using
      (selector_constant_iff (· ∈ terms) ((nodes i).branch kind).left
        (fun t => sign kind ((nodes i).branch kind).left
          (value nodes t ((nodes i).branch kind).next)) c).trans
        (sign_constant_iff (· ∈ terms) kind ((nodes i).branch kind).left
          (fun t => value nodes t ((nodes i).branch kind).next) c)

def ChildConstant {State : Type} (nodes : State → Node State) (terms : List CompareTy)
    (i : State) (kind : Constructor) (c : Bool) : Prop :=
  Constant (· ∈ terms) (fun t => value nodes t ((nodes i).branch kind).next)
    (sign kind ((nodes i).branch kind).left c)

theorem heads_constant_step {State : Type} (nodes : State → Node State)
    (names : List TypeVar) (modes : List ModVar) (n : Nat) (i : State) (c : Bool) :
    Constant (· ∈ (ComparisonRankedBasis.basis names modes (n+1)).heads)
      (fun t => value nodes t i) c ↔
      (nodes i).unitValue = c ∧
      Constant (· ∈ (ComparisonRankedBasis.basis names modes n).types)
        (fun t => value nodes t i) c ∧
      ChildConstant nodes (ComparisonRankedBasis.basis names modes n).types i .prod c ∧
      ChildConstant nodes (ComparisonRankedBasis.basis names modes n).types i .sum c ∧
      ChildConstant nodes (ComparisonRankedBasis.basis names modes n).types i .fn c := by
  simp only [ChildConstant]
  rw [←pairs_constant_iff nodes i .prod, ←pairs_constant_iff nodes i .sum,
    ←pairs_constant_iff nodes i .fn]
  simp only [Constant, ComparisonRankedBasis.basis, Basis.heads, List.forall_mem_cons,
    List.forall_mem_append, Constructor.op, value, and_assoc]

def extraKeys (modes : List ModVar) : List Key :=
  [.bottom, .raised, .localFloor, .affineFloor, .top] ++
    (modes.flatMap controls).map Key.control

theorem types_order_iff {State : Type} (nodes : State → Node State)
    (b : Basis) (i j : State) :
    On (· ∈ b.types) (fun t => value nodes t i) (fun t => value nodes t j) ↔
      On (· ∈ b.heads) (fun t => value nodes t i) (fun t => value nodes t j) ∧
      On (· ∈ extraKeys b.modes) (fun k => value nodes (b.term k) i)
        (fun k => value nodes (b.term k) j) := by
  simp only [On, Basis.types, Basis.keys, extraKeys, List.forall_mem_map,
    List.forall_mem_append, Basis.term, and_assoc]

theorem types_constant_iff {State : Type} (nodes : State → Node State)
    (b : Basis) (i : State) (c : Bool) :
    Constant (· ∈ b.types) (fun t => value nodes t i) c ↔
      Constant (· ∈ b.heads) (fun t => value nodes t i) c ∧
      Constant (· ∈ extraKeys b.modes) (fun k => value nodes (b.term k) i) c := by
  simp only [Constant, Basis.types, Basis.keys, extraKeys, List.forall_mem_map,
    List.forall_mem_append, Basis.term, and_assoc]

theorem meet_value {State : Type} (nodes : State → Node State) (i : State)
    (head : CompareTy) (rest : List CompareTy) :
    value nodes (ComparisonInterpolation.meet head rest) i =
      ((head :: rest).map (fun t => value nodes t i)).all id := by
  induction rest generalizing head <;> simp_all [ComparisonInterpolation.meet, value]

theorem join_value {State : Type} (nodes : State → Node State) (i : State)
    (head : CompareTy) (rest : List CompareTy) :
    value nodes (ComparisonInterpolation.join head rest) i =
      ((head :: rest).map (fun t => value nodes t i)).any id := by
  induction rest generalizing head <;> simp_all [ComparisonInterpolation.join, value]

def headBits {State : Type} (nodes : State → Node State) (b : Basis) (i : State) : Bool × Bool :=
  let values := b.heads.map (fun t => value nodes t i)
  (values.all id, values.any id)

def controlValue (action : ModExpr → Bool → Bool) (bits : Bool × Bool) : Key → Bool :=
  let bottom := action (.const Mode.bottom) bits.1
  let top := action (.const Mode.top) bits.2
  fun k => match k with
  | .head _ => false
  | .bottom => bottom
  | .raised => action (.const Mode.top) bottom
  | .localFloor => action (.const Mode.global) top
  | .affineFloor => action (.const Mode.many) top
  | .top => top
  | .control c => action c.expression (if c.channel == .lower then bottom else top)

theorem extra_value {State : Type} (nodes : State → Node State)
    (b : Basis) (i : State) (k : Key) (hk : k ∈ extraKeys b.modes) :
    value nodes (b.term k) i = controlValue (nodes i).action (headBits nodes b i) k := by
  cases k <;> simp_all [extraKeys, controlValue, Basis.term, Basis.bottom, Basis.top,
    value, meet_value, join_value, headBits, Basis.heads, apply_ite]

theorem headBits_all {State : Type} (nodes : State → Node State) (b : Basis) (i : State) :
    (headBits nodes b i).1 = true ↔ Constant (· ∈ b.heads) (fun t => value nodes t i) true := by
  simp [headBits, Constant]

theorem headBits_any {State : Type} (nodes : State → Node State) (b : Basis) (i : State) :
    (headBits nodes b i).2 = false ↔ Constant (· ∈ b.heads) (fun t => value nodes t i) false := by
  simp [headBits, Constant]

theorem types_order_simulation {State : Type} (nodes : State → Node State)
    (b : Basis) (i j : State) :
    On (· ∈ b.types) (fun t => value nodes t i) (fun t => value nodes t j) ↔
      On (· ∈ b.heads) (fun t => value nodes t i) (fun t => value nodes t j) ∧
      On (· ∈ extraKeys b.modes)
        (controlValue (nodes i).action (headBits nodes b i))
        (controlValue (nodes j).action (headBits nodes b j)) := by
  refine (types_order_iff nodes b i j).trans (and_congr Iff.rfl ?_)
  exact forall_congr' fun k => imp_congr_right fun hk =>
    by simp only [extra_value nodes b i k hk, extra_value nodes b j k hk]

end ModalityInference.ComparisonRankedOrderSimulation
