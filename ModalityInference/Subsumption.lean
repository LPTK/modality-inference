import Mathlib.Order.Notation
import Mathlib.Order.Heyting.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

/-! ## Variable Mappings -/

/-- A mapping from variables to values in a Heyting algebra.
    This is simply a Vector but we give it a separate name to distinguish
    its use as a variable assignment from other uses of vectors. -/
abbrev Mapping (α : Type u) (n : Nat) := Vector α n

namespace Mapping

/-- Pointwise ordering on mappings: M₁ ≤ M₂ iff M₁(x) ≤ M₂(x) for all x -/
instance {n : Nat} [LE α] : LE (Mapping α n) where
  le M₁ M₂ := ∀ x, M₁.get x ≤ M₂.get x

/-- Pointwise meet of two mappings -/
instance {n : Nat} [Min α] : Min (Mapping α n) where
  min M₁ M₂ := Vector.ofFn fun x => M₁.get x ⊓ M₂.get x

/-- Constant mapping that sends all variables to the same value -/
def const (α : Type u) (n : Nat) (c : α) : Mapping α n :=
  Vector.ofFn fun _ => c

@[simp]
theorem get_inf {n : Nat} [Min α] (M₁ M₂ : Mapping α n) (x : Fin n) :
    (M₁ ⊓ M₂).get x = M₁.get x ⊓ M₂.get x := by
  simp [Min.min, Vector.get]

@[simp]
theorem get_const (α : Type u) (n : Nat) (c : α) (x : Fin n) :
    (const α n c).get x = c := by
  simp [const, Vector.get]

/-- Maximum element in a list (supremum of all values) -/
def max_list [SemilatticeSup α] [OrderBot α] (l : List α) : α :=
  l.foldl (· ⊔ ·) ⊥

/-- Maximum element in a mapping (supremum of all values) -/
def max [SemilatticeSup α] [OrderBot α] (M : Mapping α n) : α :=
  max_list M.toList

/-- Helper: accumulator is bounded by foldl result -/
theorem List.foldl_sup_ge_acc [SemilatticeSup α] (l : List α) (acc : α) :
    acc ≤ l.foldl (· ⊔ ·) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp [List.foldl]
    calc acc ≤ acc ⊔ x := le_sup_left
         _ ≤ xs.foldl (· ⊔ ·) (acc ⊔ x) := ih (acc ⊔ x)

/-- Helper: foldl is monotone in accumulator -/
theorem List.foldl_sup_mono [SemilatticeSup α] (l : List α) {acc1 acc2 : α} (h : acc1 ≤ acc2) :
    l.foldl (· ⊔ ·) acc1 ≤ l.foldl (· ⊔ ·) acc2 := by
  induction l generalizing acc1 acc2 with
  | nil => exact h
  | cons x xs ih =>
    simp [List.foldl]
    apply ih
    exact sup_le_sup h le_rfl

/-- Helper: any member of a list is bounded by max_list -/
theorem List.mem_le_max_list [SemilatticeSup α] [OrderBot α] {a : α} {l : List α} (h : a ∈ l) :
    a ≤ max_list l := by
  induction l with
  | nil => contradiction
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h'
    · -- a = x, need: a ≤ max_list (a :: xs)
      unfold max_list
      simp only [List.foldl, bot_sup_eq]
      exact List.foldl_sup_ge_acc xs a
    · -- a ∈ xs, by IH: a ≤ max_list xs
      unfold max_list
      simp only [List.foldl, bot_sup_eq]
      calc a ≤ xs.foldl (· ⊔ ·) ⊥ := ih h'
           _ ≤ xs.foldl (· ⊔ ·) x := List.foldl_sup_mono xs bot_le

/-- Each element in a mapping is bounded by max -/
theorem get_le_max [SemilatticeSup α] [OrderBot α] (M : Mapping α n) (i : Fin n) :
    M.get i ≤ max M := by
  unfold max
  have h_mem : M.get i ∈ M.toList := by
    simp [Vector.get]
  exact List.mem_le_max_list h_mem

/-- Meeting with a constant mapping decreases the mapping pointwise. -/
theorem inf_const_le [Lattice α] (M : Mapping α n) (c : α) :
    M ⊓ const α n c ≤ M := by
  intro x
  simp only [get_inf, get_const]
  exact inf_le_left

/-- Max of a constant mapping equals the constant (when n > 0). -/
theorem max_const [SemilatticeSup α] [OrderBot α] (d : α) (hn : 0 < n) :
    max (const α n d) = d := by
  apply le_antisymm
  · -- max (const d) ≤ d: every element is d, so max is ≤ d
    unfold max max_list const
    -- All elements in toList are d, so the fold gives at most d
    have h_all : ∀ x ∈ (Vector.ofFn fun _ : Fin n => d).toList, x ≤ d := by
      intro x hx
      simp only [Vector.toList_ofFn, List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      exact le_rfl
    -- foldl sup ⊥ over elements all ≤ d gives ≤ d
    have h_fold : ∀ (l : List α), (∀ x ∈ l, x ≤ d) → ∀ acc ≤ d, l.foldl (· ⊔ ·) acc ≤ d := by
      intro l h_mem acc hacc
      induction l generalizing acc with
      | nil => simp [List.foldl]; exact hacc
      | cons x xs ih =>
        simp only [List.foldl]
        apply ih (fun y hy => h_mem y (List.mem_cons_of_mem x hy))
        have hx_mem : x ∈ x :: xs := by simp
        exact sup_le hacc (h_mem x hx_mem)
    exact h_fold _ h_all ⊥ bot_le
  · -- d ≤ max (const d): since d is in the mapping
    calc d = (const α n d).get ⟨0, hn⟩ := by simp [const, Vector.get]
      _ ≤ max (const α n d) := get_le_max (const α n d) ⟨0, hn⟩

/-- Pointwise join of two mappings -/
instance {n : Nat} [Max α] : Max (Mapping α n) where
  max M₁ M₂ := Vector.ofFn fun x => M₁.get x ⊔ M₂.get x

@[simp]
theorem get_sup {n : Nat} [Max α] (M₁ M₂ : Mapping α n) (x : Fin n) :
    (M₁ ⊔ M₂).get x = M₁.get x ⊔ M₂.get x := by
  simp [Max.max, Vector.get]

/-- Transitivity of Mapping ordering -/
theorem le_trans {n : Nat} [Preorder α] {M₁ M₂ M₃ : Mapping α n} (h₁ : M₁ ≤ M₂) (h₂ : M₂ ≤ M₃) : M₁ ≤ M₃ :=
  fun x => _root_.le_trans (h₁ x) (h₂ x)

/-- Left element is ≤ sup -/
theorem le_sup_left {n : Nat} [SemilatticeSup α] (M₁ M₂ : Mapping α n) : M₁ ≤ M₁ ⊔ M₂ :=
  fun x => by simp [Max.max, Vector.get]; exact _root_.le_sup_left

/-- Right element is ≤ sup -/
theorem le_sup_right {n : Nat} [SemilatticeSup α] (M₁ M₂ : Mapping α n) : M₂ ≤ M₁ ⊔ M₂ :=
  fun x => by simp [Max.max, Vector.get]; exact _root_.le_sup_right

/-- Sup is least upper bound -/
theorem sup_le {n : Nat} [SemilatticeSup α] {M₁ M₂ M₃ : Mapping α n} (h₁ : M₁ ≤ M₃) (h₂ : M₂ ≤ M₃) : M₁ ⊔ M₂ ≤ M₃ :=
  fun x => by simp [Max.max, Vector.get]; exact _root_.sup_le (h₁ x) (h₂ x)

/-- sup_le_sup for Mappings -/
theorem sup_le_sup {n : Nat} [SemilatticeSup α] {M₁ M₂ M₃ M₄ : Mapping α n} (h₁ : M₁ ≤ M₃) (h₂ : M₂ ≤ M₄) : M₁ ⊔ M₂ ≤ M₃ ⊔ M₄ :=
  fun x => by simp [Max.max, Vector.get]; exact _root_.sup_le_sup (h₁ x) (h₂ x)

/-- const ⊥ is the bottom element -/
theorem const_bot_le {n : Nat} [Preorder α] [OrderBot α] (M : Mapping α n) : const α n ⊥ ≤ M :=
  fun x => by simp [const, Vector.get]

/-- Preorder instance for Mapping (pointwise) -/
instance mappingPreorder {n : Nat} [Preorder α] : Preorder (Mapping α n) where
  le := (· ≤ ·)
  lt := fun M₁ M₂ => M₁ ≤ M₂ ∧ ¬M₂ ≤ M₁
  le_refl := fun M x => _root_.le_refl (M.get x)
  le_trans := fun {_ _ _} hab hbc x => _root_.le_trans (hab x) (hbc x)

/-- PartialOrder instance for Mapping (pointwise) -/
instance mappingPartialOrder {n : Nat} [PartialOrder α] : PartialOrder (Mapping α n) where
  le_antisymm := fun {a b} h₁ h₂ => by
    apply Vector.ext
    intro i hi
    exact _root_.le_antisymm (h₁ ⟨i, hi⟩) (h₂ ⟨i, hi⟩)

/-- SemilatticeSup instance for Mapping (pointwise) -/
instance mappingSemilatticeSup {n : Nat} [SemilatticeSup α] : SemilatticeSup (Mapping α n) where
  sup := (· ⊔ ·)
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le := fun {_ _ _} h₁ h₂ => sup_le h₁ h₂

/-- OrderBot instance for Mapping -/
instance mappingOrderBot {n : Nat} [PartialOrder α] [OrderBot α] : OrderBot (Mapping α n) where
  bot := const α n ⊥
  bot_le := const_bot_le

/-- Finset.sup of const mappings equals const of the sup -/
theorem sup_const_eq_const_sup {n : Nat} [SemilatticeSup α] [OrderBot α] [DecidableEq β]
    (s : Finset β) (f : β → α) :
    s.sup (fun x => const α n (f x)) = const α n (s.sup f) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sup_empty]
    rfl
  | insert x s' hx ih =>
    simp only [Finset.sup_insert]
    rw [ih]
    apply Vector.ext; intro i hi
    calc (const α n (f x) ⊔ const α n (s'.sup f)).get ⟨i, hi⟩
        = (const α n (f x)).get ⟨i, hi⟩ ⊔ (const α n (s'.sup f)).get ⟨i, hi⟩ := get_sup _ _ _
      _ = f x ⊔ s'.sup f := by rw [get_const, get_const]
      _ = (const α n (f x ⊔ s'.sup f)).get ⟨i, hi⟩ := by rw [get_const]

/-- Max of a finset sup of const mappings is bounded by the finset sup of the values. -/
theorem max_finset_sup_const_le [SemilatticeSup α] [OrderBot α] [DecidableEq β]
    (hn : 0 < n) (s : Finset β) (f : β → α) :
    max (s.sup (fun x => const α n (f x))) ≤ s.sup f := by
  rw [sup_const_eq_const_sup]
  by_cases hs : s.Nonempty
  · rw [max_const (s.sup f) hn]
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs
    simp only [hs, Finset.sup_empty]
    rw [max_const ⊥ hn]

/-- Update a single variable in a mapping -/
def update [Lattice α] (M : Mapping α n) (i : Fin n) (v : α) : Mapping α n :=
  Vector.ofFn fun j => if j = i then M.get i ⊔ v else M.get j

@[simp]
theorem get_update_same [Lattice α] (M : Mapping α n) (i : Fin n) (v : α) :
    (update M i v).get i = M.get i ⊔ v := by
  simp [update, Vector.get]

@[simp]
theorem get_update_diff [Lattice α] (M : Mapping α n) (i j : Fin n) (v : α) (h : j ≠ i) :
    (update M i v).get j = M.get j := by
  simp [update, Vector.get, h]

end Mapping

/-- Left-hand side expressions in Heyting algebra equations.
    Parameterized by carrier type `α` and indexed by number of free variables `n`.
    Variables are represented as `Fin n`. -/
inductive LeftExpr (α : Type u) : Nat → Type u where
  | var : Fin n → LeftExpr α n
  | const : α → LeftExpr α n
  | join : LeftExpr α n → LeftExpr α n → LeftExpr α n
  | meet : LeftExpr α n → LeftExpr α n → LeftExpr α n

namespace LeftExpr

/-- Max instance for join in left expressions -/
instance {n : Nat} : Max (LeftExpr α n) where
  max := join

/-- Min instance for meet in left expressions -/
instance {n : Nat} : Min (LeftExpr α n) where
  min := meet

/-- Evaluate a left expression in a Heyting algebra given an environment for variables.
    The environment is a vector of n values in the algebra. -/
def eval [HeytingAlgebra α] (env : Vector α n) : LeftExpr α n → α
  | var i => env.get i
  | const c => c
  | join e₁ e₂ => eval env e₁ ⊔ eval env e₂
  | meet e₁ e₂ => eval env e₁ ⊓ eval env e₂

/-- Left expressions are monotone: if M₁ ≤ M₂ pointwise, then eval M₁ l ≤ eval M₂ l. -/
theorem eval_mono [HeytingAlgebra α] {M₁ M₂ : Mapping α n} (l : LeftExpr α n)
    (h : M₁ ≤ M₂) : eval M₁ l ≤ eval M₂ l := by
  induction l with
  | var i =>
    simp only [eval]
    exact h i
  | const c =>
    simp only [eval]
    exact le_refl _
  | join l₁ l₂ ih₁ ih₂ =>
    simp only [eval]
    exact sup_le_sup (ih₁) (ih₂)
  | meet l₁ l₂ ih₁ ih₂ =>
    simp only [eval]
    exact inf_le_inf (ih₁) (ih₂)

/-- Key property: eval (M ⊔ N) l is bounded by eval M l ⊔ max N.
    This shows how left expression evaluation under joined mappings relates to max. -/
theorem eval_sup_le_max [HeytingAlgebra α] (M N : Mapping α n) (l : LeftExpr α n) :
    eval (M ⊔ N) l ≤ eval M l ⊔ Mapping.max N := by
  induction l with
  | var i =>
    simp only [eval, Mapping.get_sup]
    exact sup_le_sup_left (Mapping.get_le_max N i) _
  | const c =>
    simp only [eval]
    exact le_sup_left
  | join l₁ l₂ ih₁ ih₂ =>
    simp only [eval]
    calc eval (M ⊔ N) l₁ ⊔ eval (M ⊔ N) l₂
        ≤ (eval M l₁ ⊔ Mapping.max N) ⊔ (eval M l₂ ⊔ Mapping.max N) := sup_le_sup ih₁ ih₂
      _ = (eval M l₁ ⊔ eval M l₂) ⊔ Mapping.max N := by ac_rfl
  | meet l₁ l₂ ih₁ ih₂ =>
    simp only [eval]
    calc eval (M ⊔ N) l₁ ⊓ eval (M ⊔ N) l₂
        ≤ (eval M l₁ ⊔ Mapping.max N) ⊓ (eval M l₂ ⊔ Mapping.max N) := inf_le_inf ih₁ ih₂
      _ = (eval M l₁ ⊓ eval M l₂) ⊔ Mapping.max N := by
        -- Derive (a ⊔ c) ⊓ (b ⊔ c) = (a ⊓ b) ⊔ c using distributivity
        rw [inf_sup_left]
        -- (eval M l₁ ⊔ N.max) ⊓ eval M l₂ ⊔ (eval M l₁ ⊔ N.max) ⊓ N.max
        rw [inf_sup_right]
        -- (eval M l₁ ⊓ eval M l₂ ⊔ N.max ⊓ eval M l₂) ⊔ (eval M l₁ ⊔ N.max) ⊓ N.max
        rw [show (eval M l₁ ⊔ Mapping.max N) ⊓ Mapping.max N = Mapping.max N from
              inf_of_le_right le_sup_right]
        -- Goal: (eval M l₁ ⊓ eval M l₂ ⊔ N.max ⊓ eval M l₂) ⊔ N.max = eval M l₁ ⊓ eval M l₂ ⊔ N.max
        -- Use absorption: (a ⊓ b) ⊔ a = a, so (N.max ⊓ eval M l₂) ⊔ N.max = N.max
        rw [sup_assoc]
        rw [show Mapping.max N ⊓ eval M l₂ ⊔ Mapping.max N = Mapping.max N by
              rw [sup_comm]; exact sup_inf_self]

/-- When capping with d, evaluating at M ⊓ const d gives the same result as evaluating at M and then capping. -/
theorem eval_meet_const_eq [HeytingAlgebra α] (M : Mapping α n) (l : LeftExpr α n) (d : α) :
    eval (M ⊓ Mapping.const α n d) l ⊓ d = eval M l ⊓ d := by
  induction l with
  | var i =>
    simp only [eval, Mapping.get_inf, Mapping.get_const, inf_assoc, inf_idem]
  | const c =>
    simp only [eval]
  | join l₁ l₂ ih₁ ih₂ =>
    simp only [eval]
    calc (eval (M ⊓ Mapping.const α n d) l₁ ⊔ eval (M ⊓ Mapping.const α n d) l₂) ⊓ d
        = (eval (M ⊓ Mapping.const α n d) l₁ ⊓ d) ⊔ (eval (M ⊓ Mapping.const α n d) l₂ ⊓ d) := @inf_sup_right _ _ _ _ d
      _ = (eval M l₁ ⊓ d) ⊔ (eval M l₂ ⊓ d) := by rw [ih₁, ih₂]
      _ = (eval M l₁ ⊔ eval M l₂) ⊓ d := (@inf_sup_right _ _ _ _ d).symm
  | meet l₁ l₂ ih₁ ih₂ =>
    simp only [eval]
    calc (eval (M ⊓ Mapping.const α n d) l₁ ⊓ eval (M ⊓ Mapping.const α n d) l₂) ⊓ d
        = (eval (M ⊓ Mapping.const α n d) l₁ ⊓ d) ⊓ (eval (M ⊓ Mapping.const α n d) l₂ ⊓ d) := by ac_rfl
      _ = (eval M l₁ ⊓ d) ⊓ (eval M l₂ ⊓ d) := by rw [ih₁, ih₂]
      _ = (eval M l₁ ⊓ eval M l₂) ⊓ d := by ac_rfl

end LeftExpr

/-- Right-hand side expressions in Heyting algebra equations.
    Parameterized by carrier type `α` and indexed by number of free variables `n`.
    Variables are represented as `Fin n`.
    Implication can only take a left-hand side expression as its first argument. -/
inductive RightExpr (α : Type u) : Nat → Type u where
  | var : Fin n → RightExpr α n
  | const : α → RightExpr α n
  | meet : RightExpr α n → RightExpr α n → RightExpr α n
  | imply : LeftExpr α n → RightExpr α n → RightExpr α n

namespace RightExpr

/-- Min instance for meet in right expressions -/
instance {n : Nat} : Min (RightExpr α n) where
  min := meet

/-- Infix notation for implication (⇨) in right expressions -/
infixr:60 " ⇨ " => imply

/-- Evaluate a right expression in a Heyting algebra given an environment for variables.
    The environment is a vector of n values in the algebra. -/
def eval [HeytingAlgebra α] (env : Vector α n) : RightExpr α n → α
  | var i => env.get i
  | const c => c
  | meet e₁ e₂ => eval env e₁ ⊓ eval env e₂
  | imply l r => LeftExpr.eval env l ⇨ eval env r

/-- Evaluate a right expression focusing only on const parts.
    Treats all vars in the right expression as ⊤, but evaluates left expressions normally.
    This captures the "const sufficiency" condition independent of var values. -/
def eval_for_consts [HeytingAlgebra α] (env : Vector α n) : RightExpr α n → α
  | var _ => ⊤
  | const c => c
  | meet e₁ e₂ => eval_for_consts env e₁ ⊓ eval_for_consts env e₂
  | imply l r => LeftExpr.eval env l ⇨ eval_for_consts env r

theorem eval_le_eval_for_consts [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) :
    eval M r ≤ eval_for_consts M r := by
  induction r with
  | var i =>
    simp only [eval, eval_for_consts]
    exact le_top
  | const c =>
    simp only [eval, eval_for_consts]
    exact le_refl _
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [eval, eval_for_consts]
    exact inf_le_inf ih₁ ih₂
  | imply l r' ih =>
    simp only [eval, eval_for_consts]
    -- Need: eval M l ⇨ eval M r' ≤ eval M l ⇨ eval_for_consts M r'
    -- This follows from monotonicity of ⇨ in the second argument
    apply le_himp_iff.mpr
    calc (LeftExpr.eval M l ⇨ eval M r') ⊓ LeftExpr.eval M l
        ≤ eval M r' := le_himp_iff.mp (le_refl _)
      _ ≤ eval_for_consts M r' := ih

/-- eval_for_consts is antitone in M (because left expressions appear in antitonic positions). -/
theorem eval_for_consts_antitone [HeytingAlgebra α] (r : RightExpr α n) (M₁ M₂ : Mapping α n)
    (h : M₁ ≤ M₂) :
    eval_for_consts M₂ r ≤ eval_for_consts M₁ r := by
  induction r with
  | var _ =>
    simp only [eval_for_consts]
    exact le_refl _
  | const _ =>
    simp only [eval_for_consts]
    exact le_refl _
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [eval_for_consts]
    exact inf_le_inf ih₁ ih₂
  | imply l r' ih =>
    simp only [eval_for_consts]
    -- eval M₁ l ⇨ eval_for_consts M₁ r' ≥ eval M₂ l ⇨ eval_for_consts M₂ r'
    -- Since M₁ ≤ M₂, we have eval M₁ l ≤ eval M₂ l (left expr monotone)
    -- And eval_for_consts M₂ r' ≤ eval_for_consts M₁ r' (by IH)
    -- So (eval M₂ l ⇨ eval_for_consts M₂ r') ≤ (eval M₁ l ⇨ eval_for_consts M₁ r')
    -- This follows from himp being antitone in first arg and monotone in second arg
    apply le_himp_iff.mpr
    have h_left : LeftExpr.eval M₁ l ≤ LeftExpr.eval M₂ l := LeftExpr.eval_mono l h
    calc (LeftExpr.eval M₂ l ⇨ eval_for_consts M₂ r') ⊓ LeftExpr.eval M₁ l
        ≤ (LeftExpr.eval M₂ l ⇨ eval_for_consts M₂ r') ⊓ LeftExpr.eval M₂ l := by
          apply inf_le_inf_left
          exact h_left
      _ ≤ eval_for_consts M₂ r' := le_himp_iff.mp (le_refl _)
      _ ≤ eval_for_consts M₁ r' := ih

/-- Inverse of eval_meet_const_of_ge: If eval (M ⊓ const e) r ≥ c ⊓ e, then eval M r ≥ c ⊓ e.
    This works because variables go up when going from M ⊓ const e to M, and
    antitonic positions (within left expressions) can't drop below e. -/
theorem eval_of_eval_inf_const [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) (c e : α) :
    eval (M ⊓ Mapping.const α n e) r ≥ c ⊓ e → eval M r ≥ c ⊓ e := by
  induction r generalizing c with
  | var i =>
    simp only [eval, Mapping.get_inf, Mapping.get_const]
    intro h
    calc eval M (var i)
        = M.get i := rfl
      _ ≥ M.get i ⊓ e := inf_le_left
      _ ≥ c ⊓ e := h
  | const c' =>
    simp only [eval]
    intro h
    exact h
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [eval]
    intro h
    have h₁ : eval (M ⊓ Mapping.const α n e) r₁ ≥ c ⊓ e := le_trans h inf_le_left
    have h₂ : eval (M ⊓ Mapping.const α n e) r₂ ≥ c ⊓ e := le_trans h inf_le_right
    exact le_inf (ih₁ c h₁) (ih₂ c h₂)
  | imply l r ih =>
    simp only [eval]
    intro h
    -- We have: c ⊓ e ≤ LeftExpr.eval (M ⊓ const e) l ⇨ eval (M ⊓ const e) r
    -- Want to show: c ⊓ e ≤ LeftExpr.eval M l ⇨ eval M r
    -- By adjunction: (c ⊓ e) ⊓ LeftExpr.eval M l ≤ eval M r

    -- Use adjunction on hypothesis
    have h_adj : (c ⊓ e) ⊓ LeftExpr.eval (M ⊓ Mapping.const α n e) l ≤ eval (M ⊓ Mapping.const α n e) r :=
      le_himp_iff.mp h
    -- Key insight: Use eval_meet_const_eq to relate the left expressions
    have h_eq : LeftExpr.eval (M ⊓ Mapping.const α n e) l ⊓ e = LeftExpr.eval M l ⊓ e :=
      LeftExpr.eval_meet_const_eq M l e
    -- Rewrite: (c ⊓ e) ⊓ LeftExpr.eval (M ⊓ const e) l = (c ⊓ LeftExpr.eval M l) ⊓ e
    have h_inf_eq : (c ⊓ e) ⊓ LeftExpr.eval (M ⊓ Mapping.const α n e) l = (c ⊓ LeftExpr.eval M l) ⊓ e := by
      calc (c ⊓ e) ⊓ LeftExpr.eval (M ⊓ Mapping.const α n e) l
          = c ⊓ (e ⊓ LeftExpr.eval (M ⊓ Mapping.const α n e) l) := by ac_rfl
        _ = c ⊓ (e ⊓ (LeftExpr.eval (M ⊓ Mapping.const α n e) l ⊓ e)) := by ac_rfl
        _ = c ⊓ (e ⊓ (LeftExpr.eval M l ⊓ e)) := by rw [h_eq]
        _ = c ⊓ (e ⊓ LeftExpr.eval M l) := by ac_rfl
        _ = (c ⊓ LeftExpr.eval M l) ⊓ e := by ac_rfl
    -- So: (c ⊓ LeftExpr.eval M l) ⊓ e ≤ eval (M ⊓ const e) r
    have h_adj' : (c ⊓ LeftExpr.eval M l) ⊓ e ≤ eval (M ⊓ Mapping.const α n e) r := by
      rw [← h_inf_eq]; exact h_adj
    -- By IH with c' := c ⊓ LeftExpr.eval M l: eval M r ≥ (c ⊓ LeftExpr.eval M l) ⊓ e
    have h_r : eval M r ≥ (c ⊓ LeftExpr.eval M l) ⊓ e := ih (c ⊓ LeftExpr.eval M l) h_adj'
    -- Now show: c ⊓ e ≤ LeftExpr.eval M l ⇨ eval M r
    -- By adjunction: (c ⊓ e) ⊓ LeftExpr.eval M l ≤ eval M r
    apply le_himp_iff.mpr
    calc (c ⊓ e) ⊓ LeftExpr.eval M l
        = (c ⊓ LeftExpr.eval M l) ⊓ e := by ac_rfl
      _ ≤ eval M r := h_r

/-- Generalized threshold property: if eval M r ≥ c ⊓ e, then eval (M ⊓ const e) r ≥ c ⊓ e.
    The extra parameter c allows tracking additional constraints through recursion. -/
theorem eval_meet_const_of_ge [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) (c e : α)
    (h : eval M r ≥ c ⊓ e) : eval (M ⊓ Mapping.const α n e) r ≥ c ⊓ e := by
  induction r generalizing c with
  | var i =>
    -- eval (M ⊓ const e) (var i) = M.get i ⊓ e
    -- If eval M (var i) = M.get i ≥ c ⊓ e, then M.get i ⊓ e ≥ c ⊓ e
    simp only [eval, Mapping.get_inf, Mapping.get_const] at h ⊢
    calc M.get i ⊓ e
        ≥ (c ⊓ e) ⊓ e := inf_le_inf_right e h
      _ = c ⊓ e := by rw [inf_assoc, inf_idem]
  | const c' =>
    -- eval (M ⊓ const e) (const c') = c'
    -- If eval M (const c') = c' ≥ c ⊓ e, then c' ≥ c ⊓ e
    simp only [eval] at h ⊢
    exact h
  | meet r₁ r₂ ih₁ ih₂ =>
    -- If eval M (meet r₁ r₂) = eval M r₁ ⊓ eval M r₂ ≥ c ⊓ e
    simp only [eval] at h ⊢
    have h₁ : eval M r₁ ≥ c ⊓ e := le_trans h inf_le_left
    have h₂ : eval M r₂ ≥ c ⊓ e := le_trans h inf_le_right
    exact le_inf (ih₁ c h₁) (ih₂ c h₂)
  | imply l r ih =>
    -- If eval M (l ⇨ r) = LeftExpr.eval M l ⇨ eval M r ≥ c ⊓ e
    -- We need: LeftExpr.eval (M ⊓ const e) l ⇨ eval (M ⊓ const e) r ≥ c ⊓ e
    simp only [eval] at h ⊢
    -- Strategy: Use c' := LeftExpr.eval M l ⊓ c in the IH
    -- Step 1: Use adjunction on h: c ⊓ e ≤ l ⇨ r means l ⊓ (c ⊓ e) ≤ r
    -- The adjunction is: c ≤ a ⇨ b ↔ a ⊓ c ≤ b
    have h_adj : LeftExpr.eval M l ⊓ (c ⊓ e) ≤ eval M r := by
      -- h : LeftExpr.eval M l ⇨ eval M r ≥ c ⊓ e
      -- which is: c ⊓ e ≤ LeftExpr.eval M l ⇨ eval M r
      -- The adjunction is: a ≤ b ⇨ c ↔ a ⊓ b ≤ c (this is le_himp_iff)
      -- So with a = c ⊓ e, b = LeftExpr.eval M l, c = eval M r:
      -- (c ⊓ e) ⊓ LeftExpr.eval M l ≤ eval M r ↔ c ⊓ e ≤ LeftExpr.eval M l ⇨ eval M r
      have h_le : c ⊓ e ≤ LeftExpr.eval M l ⇨ eval M r := h
      have := le_himp_iff.mp h_le
      rw [inf_comm] at this
      exact this
    -- Rewrite to: (LeftExpr.eval M l ⊓ c) ⊓ e ≤ eval M r
    have h' : eval M r ≥ (LeftExpr.eval M l ⊓ c) ⊓ e := by
      calc eval M r
          ≥ LeftExpr.eval M l ⊓ (c ⊓ e) := h_adj
        _ = LeftExpr.eval M l ⊓ c ⊓ e := by ac_rfl
    -- Step 2: Apply IH with c' := LeftExpr.eval M l ⊓ c
    have ih_applied := ih (LeftExpr.eval M l ⊓ c) h'
    -- ih_applied : eval (M ⊓ const e) r ≥ (LeftExpr.eval M l ⊓ c) ⊓ e
    -- Step 3: Use monotonicity of left expressions
    have l_mono : LeftExpr.eval (M ⊓ Mapping.const α n e) l ≤ LeftExpr.eval M l :=
      LeftExpr.eval_mono l (Mapping.inf_const_le M e)
    -- Step 4: Show LeftExpr.eval (M ⊓ const e) l ⊓ (c ⊓ e) ≤ eval (M ⊓ const e) r
    have key : LeftExpr.eval (M ⊓ Mapping.const α n e) l ⊓ (c ⊓ e) ≤ eval (M ⊓ Mapping.const α n e) r := by
      calc LeftExpr.eval (M ⊓ Mapping.const α n e) l ⊓ (c ⊓ e)
          = LeftExpr.eval (M ⊓ Mapping.const α n e) l ⊓ c ⊓ e := by ac_rfl
        _ ≤ LeftExpr.eval M l ⊓ c ⊓ e := inf_le_inf_right e (inf_le_inf_right c l_mono)
        _ ≤ eval (M ⊓ Mapping.const α n e) r := ih_applied
    -- Step 5: Apply adjunction backwards to get the goal
    -- key : LeftExpr.eval (M ⊓ const e) l ⊓ (c ⊓ e) ≤ eval (M ⊓ const e) r
    -- Goal: c ⊓ e ≤ LeftExpr.eval (M ⊓ const e) l ⇨ eval (M ⊓ const e) r
    -- Use adjunction: a ≤ b ⇨ c ↔ a ⊓ b ≤ c
    -- First commute to get (c ⊓ e) ⊓ LeftExpr.eval (M ⊓ const e) l ≤ ...
    have key' : (c ⊓ e) ⊓ LeftExpr.eval (M ⊓ Mapping.const α n e) l ≤ eval (M ⊓ Mapping.const α n e) r := by
      rw [inf_comm]
      exact key
    exact le_himp_iff.mpr key'

end RightExpr


/-- An equation in the form `r ≤ l`.
    Parameterized by carrier type `α` and indexed by number of free variables `n`. -/
structure Equation (α : Type u) (n : Nat) where
  /-- The right-hand side of the inequality -/
  right : RightExpr α n
  /-- The left-hand side of the inequality -/
  left : LeftExpr α n

namespace Equation

/-- An equation is satisfied by an environment if `r ≤ l` holds. -/
def satisfied [HeytingAlgebra α] (env : Vector α n) (eq : Equation α n) : Prop :=
  RightExpr.eval env eq.right ≤ LeftExpr.eval env eq.left

/-- An equation is not satisfied by an environment if `r ≰ l`. -/
def not_satisfied [HeytingAlgebra α] (env : Vector α n) (eq : Equation α n) : Prop :=
  ¬(RightExpr.eval env eq.right ≤ LeftExpr.eval env eq.left)

/-- An equation is valid if all environments satisfy it. -/
def valid [HeytingAlgebra α] (eq : Equation α n) : Prop :=
  ∀ env, satisfied env eq

/-- An equation is not valid if there exists an environment that does not satisfy it. -/
def not_valid [HeytingAlgebra α] (eq : Equation α n) : Prop :=
  ∃ env, not_satisfied env eq

end Equation

/-! ## Horn-Clause Solver for Right Expressions

The Horn-clause solver computes a "minimal" environment S for a right expression.
-/

namespace RightExpr

/-- Size of a right expression, used for bounding iteration. -/
def size : RightExpr α n → Nat
  | var _ => 1
  | const _ => 1
  | meet r₁ r₂ => 1 + size r₁ + size r₂
  | imply _ r => 1 + size r

/-- Update a mapping by propagating a constraint through a right expression.
    This is the core operation of the horn-clause solver. -/
def update [HeytingAlgebra α] (M : Mapping α n) (c : α) : RightExpr α n → Mapping α n
  | var i => Mapping.update M i c
  | const _ => M
  | meet r₁ r₂ => update M c r₁ ⊔ update M c r₂
  | imply l r =>
      let v := LeftExpr.eval M l
      update M (c ⊓ v) r

/-- The update function increases the mapping. -/
theorem update_le [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) (c : α) :
    M ≤ update M c r := by
  induction r generalizing c with
  | var i =>
    intro j
    by_cases hj : j = i
    · rw [hj]
      simp only [update, Mapping.get_update_same]
      exact le_sup_left
    · simp only [update, Mapping.get_update_diff _ _ _ _ hj]
      exact le_refl _
  | const c' =>
    simp only [update]
    intro x
    exact le_refl _
  | meet r₁ r₂ ih₁ ih₂ =>
    intro x
    simp only [update, Mapping.get_sup]
    calc M.get x
        ≤ (update M c r₁).get x := ih₁ c x
      _ ≤ (update M c r₁).get x ⊔ (update M c r₂).get x := le_sup_left
  | imply l r ih =>
    simp only [update]
    exact ih (c ⊓ LeftExpr.eval M l)

/-- The update function is monotonic in its constant argument. -/
theorem update_const_mono [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) (c₁ c₂ : α) :
    c₁ ≤ c₂ → update M c₁ r ≤ update M c₂ r := by
  intro h
  induction r generalizing c₁ c₂ with
  | var i =>
    intro j
    by_cases hj : j = i
    · rw [hj]
      simp only [update, Mapping.get_update_same]
      exact sup_le_sup_left h (M.get i)
    · simp only [update, Mapping.get_update_diff _ _ _ _ hj]
      exact le_refl _
  | const c' =>
    simp only [update]
    intro x
    exact le_refl _
  | meet r₁ r₂ ih₁ ih₂ =>
    intro x
    simp only [update, Mapping.get_sup]
    exact sup_le_sup (ih₁ c₁ c₂ h x) (ih₂ c₁ c₂ h x)
  | imply l r ih =>
    simp only [update]
    have : c₁ ⊓ LeftExpr.eval M l ≤ c₂ ⊓ LeftExpr.eval M l := inf_le_inf_right (LeftExpr.eval M l) h
    exact ih (c₁ ⊓ LeftExpr.eval M l) (c₂ ⊓ LeftExpr.eval M l) this

/-- The update function is monotonic in its mapping argument. -/
theorem update_mono [HeytingAlgebra α] (r : RightExpr α n) (M₁ M₂ : Mapping α n) (c : α) :
    M₁ ≤ M₂ → update M₁ c r ≤ update M₂ c r := by
  intro h
  induction r generalizing c with
  | var i =>
    intro j
    by_cases hj : j = i
    · rw [hj]
      simp only [update, Mapping.get_update_same]
      exact sup_le_sup (h i) (le_refl c)
    · simp only [update, Mapping.get_update_diff _ _ _ _ hj]
      exact h j
  | const c' =>
    simp only [update]
    exact h
  | meet r₁ r₂ ih₁ ih₂ =>
    intro x
    simp only [update, Mapping.get_sup]
    exact sup_le_sup (ih₁ c x) (ih₂ c x)
  | imply l r ih =>
    intro x
    simp only [update]
    have h_le : LeftExpr.eval M₁ l ≤ LeftExpr.eval M₂ l := LeftExpr.eval_mono l h
    have hc : c ⊓ LeftExpr.eval M₁ l ≤ c ⊓ LeftExpr.eval M₂ l := inf_le_inf_left c h_le
    -- By IH: update is monotonic in the mapping for any constant
    have step1 : (update M₁ (c ⊓ LeftExpr.eval M₁ l) r).get x ≤ (update M₂ (c ⊓ LeftExpr.eval M₁ l) r).get x :=
      ih (c ⊓ LeftExpr.eval M₁ l) x
    -- By update_const_mono: update is monotonic in the constant
    have step2 : (update M₂ (c ⊓ LeftExpr.eval M₁ l) r).get x ≤ (update M₂ (c ⊓ LeftExpr.eval M₂ l) r).get x :=
      update_const_mono r M₂ (c ⊓ LeftExpr.eval M₁ l) (c ⊓ LeftExpr.eval M₂ l) hc x
    calc (update M₁ (c ⊓ LeftExpr.eval M₁ l) r).get x
        ≤ (update M₂ (c ⊓ LeftExpr.eval M₁ l) r).get x := step1
      _ ≤ (update M₂ (c ⊓ LeftExpr.eval M₂ l) r).get x := step2

theorem update_inf_const [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) (c d : α) :
    update M c r ⊓ Mapping.const α n d = update (M ⊓ Mapping.const α n d) (c ⊓ d) r := by
  induction r generalizing c with
  | var i =>
    -- Need to show equality of mappings using Vector.ext
    apply Vector.ext
    intro j hj
    show (update M c (var i) ⊓ Mapping.const α n d).get ⟨j, hj⟩ =
         (update (M ⊓ Mapping.const α n d) (c ⊓ d) (var i)).get ⟨j, hj⟩
    by_cases heq : (⟨j, hj⟩ : Fin n) = i
    · -- Position i: show (M.get i ⊔ c) ⊓ d = (M.get i ⊓ d) ⊔ (c ⊓ d)
      rw [heq]
      simp only [update, Mapping.get_inf, Mapping.get_const, Mapping.get_update_same]
      -- Goal: (M.get i ⊔ c) ⊓ d = (M.get i ⊓ d) ⊔ (c ⊓ d)
      -- Use distributivity: (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)
      rw [inf_sup_right]
    · -- Position j ≠ i
      simp only [update, Mapping.get_inf, Mapping.get_const, Mapping.get_update_diff _ _ _ _ heq]
  | const c' =>
    -- update M c (const c') = M for both sides
    simp only [update]
  | meet r₁ r₂ ih₁ ih₂ =>
    -- LHS: (update M c (meet r₁ r₂)) ⊓ const d
    --    = (update M c r₁ ⊔ update M c r₂) ⊓ const d
    -- RHS: update (M ⊓ const d) (c ⊓ d) (meet r₁ r₂)
    --    = update (M ⊓ const d) (c ⊓ d) r₁ ⊔ update (M ⊓ const d) (c ⊓ d) r₂
    apply Vector.ext
    intro x hx
    show (update M c (meet r₁ r₂) ⊓ Mapping.const α n d).get ⟨x, hx⟩ =
         (update (M ⊓ Mapping.const α n d) (c ⊓ d) (meet r₁ r₂)).get ⟨x, hx⟩
    simp only [update, Mapping.get_inf, Mapping.get_const, Mapping.get_sup]
    -- Goal: ((update M c r₁).get x ⊔ (update M c r₂).get x) ⊓ d =
    --       (update (M ⊓ const d) (c ⊓ d) r₁).get x ⊔ (update (M ⊓ const d) (c ⊓ d) r₂).get x
    -- Get the equalities from IH by unfolding vector equality
    have h1 : (update M c r₁).get ⟨x, hx⟩ ⊓ d =
              (update (M ⊓ Mapping.const α n d) (c ⊓ d) r₁).get ⟨x, hx⟩ := by
      have eq := ih₁ c
      have : (update M c r₁ ⊓ Mapping.const α n d).get ⟨x, hx⟩ =
             (update (M ⊓ Mapping.const α n d) (c ⊓ d) r₁).get ⟨x, hx⟩ := by
        rw [eq]
      simp [Mapping.get_inf, Mapping.get_const] at this
      exact this
    have h2 : (update M c r₂).get ⟨x, hx⟩ ⊓ d =
              (update (M ⊓ Mapping.const α n d) (c ⊓ d) r₂).get ⟨x, hx⟩ := by
      have eq := ih₂ c
      have : (update M c r₂ ⊓ Mapping.const α n d).get ⟨x, hx⟩ =
             (update (M ⊓ Mapping.const α n d) (c ⊓ d) r₂).get ⟨x, hx⟩ := by
        rw [eq]
      simp [Mapping.get_inf, Mapping.get_const] at this
      exact this
    -- Use distributivity: (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)
    calc ((update M c r₁).get ⟨x, hx⟩ ⊔ (update M c r₂).get ⟨x, hx⟩) ⊓ d
        = ((update M c r₁).get ⟨x, hx⟩ ⊓ d) ⊔ ((update M c r₂).get ⟨x, hx⟩ ⊓ d) := by
          rw [inf_sup_right]
      _ = (update (M ⊓ Mapping.const α n d) (c ⊓ d) r₁).get ⟨x, hx⟩ ⊔
          (update (M ⊓ Mapping.const α n d) (c ⊓ d) r₂).get ⟨x, hx⟩ := by rw [h1, h2]
  | imply l r' ih =>
    simp only [update]
    -- By IH: update M c' r' ⊓ const d = update (M ⊓ const d) (c' ⊓ d) r'
    -- We apply this with c' = c ⊓ LeftExpr.eval M l
    have ih_applied : update M (c ⊓ LeftExpr.eval M l) r' ⊓ Mapping.const α n d =
                      update (M ⊓ Mapping.const α n d) ((c ⊓ LeftExpr.eval M l) ⊓ d) r' := ih (c ⊓ LeftExpr.eval M l)
    -- Need to show: (c ⊓ LeftExpr.eval M l) ⊓ d = (c ⊓ d) ⊓ LeftExpr.eval (M ⊓ const d) l
    have key : (c ⊓ LeftExpr.eval M l) ⊓ d = (c ⊓ d) ⊓ LeftExpr.eval (M ⊓ Mapping.const α n d) l := by
      -- Key: by eval_meet_const_eq, eval (M ⊓ const d) l ⊓ d = eval M l ⊓ d
      have eq := LeftExpr.eval_meet_const_eq M l d
      calc c ⊓ LeftExpr.eval M l ⊓ d
          = c ⊓ (LeftExpr.eval M l ⊓ d) := by ac_rfl
        _ = c ⊓ (LeftExpr.eval (M ⊓ Mapping.const α n d) l ⊓ d) := by rw [← eq]
        _ = c ⊓ (d ⊓ LeftExpr.eval (M ⊓ Mapping.const α n d) l) := by ac_rfl
        _ = c ⊓ d ⊓ LeftExpr.eval (M ⊓ Mapping.const α n d) l := by ac_rfl
    calc update M (c ⊓ LeftExpr.eval M l) r' ⊓ Mapping.const α n d
        = update (M ⊓ Mapping.const α n d) (c ⊓ LeftExpr.eval M l ⊓ d) r' := ih_applied
      _ = update (M ⊓ Mapping.const α n d) (c ⊓ d ⊓ LeftExpr.eval (M ⊓ Mapping.const α n d) l) r' := by rw [key]

/-- Converse of update_fixpoint: if M is a fixed point with constant c ≥ e and satisfies
    const sufficiency for e, then it satisfies the full evaluation condition for e. -/
theorem fixpoint_and_consts_sufficient_general [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) (c e : α)
    (hc : c ≥ e)
    (hfp : update M c r = M)
    (hconst : eval_for_consts M r ≥ e) :
    eval M r ≥ e := by
  induction r generalizing c e with
  | var i =>
    simp only [update] at hfp
    have heq := congr_fun (congr_arg Vector.get hfp) i
    rw [Mapping.get_update_same] at heq
    simp only [eval]
    rw [sup_comm] at heq
    have : M.get i ≥ c := le_of_sup_eq heq
    calc e ≤ c := hc
         _ ≤ M.get i := this
  | const c' =>
    simp only [eval_for_consts] at hconst
    exact hconst
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [eval, eval_for_consts, update] at hfp hconst ⊢
    have h₁ : eval_for_consts M r₁ ≥ e := le_trans hconst inf_le_left
    have h₂ : eval_for_consts M r₂ ≥ e := le_trans hconst inf_le_right
    have hfp₁ : update M c r₁ = M := by
      have hle : M ≤ update M c r₁ := update_le r₁ M c
      have : ∀ (j : ℕ) (hj : j < n), (update M c r₁)[j] = M[j] := by
        intro j hj
        show (update M c r₁).get ⟨j, hj⟩ = M.get ⟨j, hj⟩
        have h1 : (update M c r₁).get ⟨j, hj⟩ ≤ (update M c r₁ ⊔ update M c r₂).get ⟨j, hj⟩ := by
          rw [Mapping.get_sup]
          exact le_sup_left
        have h2 : (update M c r₁ ⊔ update M c r₂).get ⟨j, hj⟩ = M.get ⟨j, hj⟩ := by
          rw [hfp]
        have h3 : M.get ⟨j, hj⟩ ≤ (update M c r₁).get ⟨j, hj⟩ := hle ⟨j, hj⟩
        have hle' : (update M c r₁).get ⟨j, hj⟩ ≤ M.get ⟨j, hj⟩ :=
          calc (update M c r₁).get ⟨j, hj⟩
              ≤ (update M c r₁ ⊔ update M c r₂).get ⟨j, hj⟩ := h1
            _ = M.get ⟨j, hj⟩ := h2
        exact le_antisymm hle' h3
      exact Vector.ext this
    have hfp₂ : update M c r₂ = M := by
      have hle : M ≤ update M c r₂ := update_le r₂ M c
      have : ∀ (j : ℕ) (hj : j < n), (update M c r₂)[j] = M[j] := by
        intro j hj
        show (update M c r₂).get ⟨j, hj⟩ = M.get ⟨j, hj⟩
        have h1 : (update M c r₂).get ⟨j, hj⟩ ≤ (update M c r₁ ⊔ update M c r₂).get ⟨j, hj⟩ := by
          rw [Mapping.get_sup]
          exact le_sup_right
        have h2 : (update M c r₁ ⊔ update M c r₂).get ⟨j, hj⟩ = M.get ⟨j, hj⟩ := by
          rw [hfp]
        have h3 : M.get ⟨j, hj⟩ ≤ (update M c r₂).get ⟨j, hj⟩ := hle ⟨j, hj⟩
        have hle' : (update M c r₂).get ⟨j, hj⟩ ≤ M.get ⟨j, hj⟩ :=
          calc (update M c r₂).get ⟨j, hj⟩
              ≤ (update M c r₁ ⊔ update M c r₂).get ⟨j, hj⟩ := h1
            _ = M.get ⟨j, hj⟩ := h2
        exact le_antisymm hle' h3
      exact Vector.ext this
    exact le_inf (ih₁ c e hc hfp₁ h₁) (ih₂ c e hc hfp₂ h₂)
  | imply l r' ih =>
    simp only [eval, eval_for_consts, update] at hfp hconst ⊢
    have h_adj : e ⊓ LeftExpr.eval M l ≤ eval_for_consts M r' :=
      le_himp_iff.mp hconst
    have hc' : c ⊓ LeftExpr.eval M l ≥ e ⊓ LeftExpr.eval M l := inf_le_inf hc (le_refl _)
    have ih' := ih (c ⊓ LeftExpr.eval M l) (e ⊓ LeftExpr.eval M l) hc' hfp h_adj
    exact le_himp_iff.mpr ih'

/-- Converse of update_fixpoint: if M is a fixed point and satisfies const sufficiency,
    then it satisfies the full evaluation condition. -/
theorem fixpoint_and_consts_sufficient [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) (e : α)
    (hfp : update M e r = M)
    (hconst : eval_for_consts M r ≥ e) :
    eval M r ≥ e := by
  exact fixpoint_and_consts_sufficient_general r M e e (le_refl _) hfp hconst

/-- If eval M r ≥ c, then M is a fixed point of update M c r. -/
theorem update_fixpoint [HeytingAlgebra α] (r : RightExpr α n) (M : Mapping α n) (c : α)
    (h : eval M r ≥ c) : update M c r = M := by
  induction r generalizing c with
  | var i =>
    -- eval M (var i) = M.get i, so if M.get i ≥ c, then update M c (var i) = M
    simp only [eval] at h
    -- update M c (var i) = Mapping.update M i c
    -- Need to show Mapping.update M i c = M
    simp only [update]
    have : ∀ (j : ℕ) (hj : j < n), (Mapping.update M i c)[j] = M[j] := fun j hj => by
      show (Mapping.update M i c).get ⟨j, hj⟩ = M.get ⟨j, hj⟩
      by_cases heq : (⟨j, hj⟩ : Fin n) = i
      · rw [heq, Mapping.get_update_same]
        exact sup_of_le_left h
      · rw [Mapping.get_update_diff M i ⟨j, hj⟩ c heq]
    exact Vector.ext this
  | const c' =>
    -- update M c (const c') = M
    rfl
  | meet r₁ r₂ ih₁ ih₂ =>
    -- eval M (r₁ ⊓ r₂) = eval M r₁ ⊓ eval M r₂ ≥ c
    -- So eval M r₁ ≥ c and eval M r₂ ≥ c
    simp only [eval] at h
    have h₁ : eval M r₁ ≥ c := le_trans h inf_le_left
    have h₂ : eval M r₂ ≥ c := le_trans h inf_le_right
    -- By IH: update M c r₁ = M and update M c r₂ = M
    have ih₁' := ih₁ c h₁
    have ih₂' := ih₂ c h₂
    -- update M c (meet r₁ r₂) = update M c r₁ ⊔ update M c r₂ = M ⊔ M = M
    simp only [update]
    rw [ih₁', ih₂']
    -- Now prove M ⊔ M = M
    have : ∀ (j : ℕ) (hj : j < n), (M ⊔ M)[j] = M[j] := fun j hj => by
      show (M ⊔ M).get ⟨j, hj⟩ = M.get ⟨j, hj⟩
      rw [Mapping.get_sup]
      exact sup_idem (M.get ⟨j, hj⟩)
    exact Vector.ext this
  | imply l r ih =>
    -- eval M (l ⇨ r) = LeftExpr.eval M l ⇨ eval M r ≥ c
    -- Use adjunction: c ⊓ LeftExpr.eval M l ≤ eval M r
    simp only [eval] at h
    have h_adj : c ⊓ LeftExpr.eval M l ≤ eval M r := by
      have : c ≤ LeftExpr.eval M l ⇨ eval M r := h
      exact le_himp_iff.mp this
    -- By IH with c' := c ⊓ LeftExpr.eval M l
    have ih' := ih (c ⊓ LeftExpr.eval M l) h_adj
    -- update M c (imply l r) = update M (c ⊓ LeftExpr.eval M l) r = M
    simp only [update]
    exact ih'

/-! ## Iteration

Iterate the update function a fixed number of times.
-/

/-- Iterate update function k times starting from mapping M. -/
def iterate [HeytingAlgebra α] (k : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n) : Mapping α n :=
  match k with
  | 0 => M
  | k' + 1 => update (iterate k' M c r) c r

/-- If M is a fixed point, then iterate k M ≤ M for all k -/
theorem iterate_least [HeytingAlgebra α] (k : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n)
    (M₀ : Mapping α n) (h_init : M₀ ≤ M) (hfp : update M c r = M) :
    iterate k M₀ c r ≤ M := by
  induction k generalizing M₀ with
  | zero =>
    simp [iterate]
    exact h_init
  | succ k' ih =>
    simp [iterate]
    -- iterate (k'+1) M₀ = update (iterate k' M₀)
    -- By IH: iterate k' M₀ ≤ M
    have h_iter : iterate k' M₀ c r ≤ M := ih M₀ h_init
    -- By update_mono: update (iterate k' M₀) ≤ update M
    have h_update : update (iterate k' M₀ c r) c r ≤ update M c r :=
      update_mono r (iterate k' M₀ c r) M c h_iter
    -- By hfp: update M = M
    calc update (iterate k' M₀ c r) c r
        ≤ update M c r := h_update
      _ = M := hfp

/-- Iterate is monotone in the iteration count: iterate k M ≤ iterate (k+1) M. -/
theorem iterate_step_le [HeytingAlgebra α] (k : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n) :
    iterate k M c r ≤ iterate (k + 1) M c r := by
  induction k generalizing M with
  | zero =>
    -- iterate 0 M = M, iterate 1 M = update M c r, and M ≤ update M c r by update_le
    simp only [iterate]
    exact update_le r M c
  | succ k' ih =>
    -- iterate (k'+1) M = update (iterate k' M) c r
    -- iterate (k'+2) M = update (iterate (k'+1) M) c r
    -- By IH: iterate k' M ≤ iterate (k'+1) M
    -- By update_mono: update (iterate k' M) c r ≤ update (iterate (k'+1) M) c r
    simp only [iterate]
    have h_ih := ih (iterate 0 M c r)
    simp only [iterate] at h_ih
    exact update_mono r (iterate k' M c r) (iterate (k' + 1) M c r) c h_ih

/-- Iterate is monotone in the iteration count for arbitrary gaps. -/
theorem iterate_le_of_le [HeytingAlgebra α] {k₁ k₂ : Nat} (M : Mapping α n) (c : α) (r : RightExpr α n) :
    k₁ ≤ k₂ → iterate k₁ M c r ≤ iterate k₂ M c r := by
  intro h_le
  -- Get the difference and prove by induction on it
  have ⟨d, hd⟩ := Nat.le.dest h_le
  subst hd
  -- Now prove iterate k₁ M ≤ iterate (k₁ + d) M by induction on d
  induction d with
  | zero =>
    -- k₁ + 0 = k₁
    intro x
    simp only [Nat.add_zero]
    rfl
  | succ d' ih =>
    -- iterate k₁ M ≤ iterate (k₁ + d') M ≤ iterate (k₁ + d' + 1) M
    intro x
    have h1 : (iterate k₁ M c r).get x ≤ (iterate (k₁ + d') M c r).get x :=
      ih (Nat.le_add_right k₁ d') x
    have h2 : (iterate (k₁ + d') M c r).get x ≤ (iterate (k₁ + d' + 1) M c r).get x :=
      iterate_step_le (k₁ + d') M c r x
    exact le_trans h1 h2

/-- Helper: if M is a fixed point, then iterating from M returns M -/
theorem iterate_fixpoint [HeytingAlgebra α] (k : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n)
    (h_fp : update M c r = M) : iterate k M c r = M := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    simp only [iterate]
    rw [ih, h_fp]

/-- Helper: iterating from update M is the same as updating after iterating from M -/
theorem iterate_update_comm [HeytingAlgebra α] (k : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n) :
    iterate k (update M c r) c r = update (iterate k M c r) c r := by
  induction k generalizing M with
  | zero =>
    -- iterate 0 (update M c r) = update M c r = update (iterate 0 M) c r
    rfl
  | succ k' ih =>
    -- iterate (k'+1) (update M c r) = update (iterate k' (update M c r)) c r
    -- update (iterate (k'+1) M) c r = update (update (iterate k' M) c r) c r
    simp [iterate]
    rw [ih M]

/-- Helper: iterating with c then capping at d equals iterating with c ⊓ d. -/
theorem iterate_inf_const [HeytingAlgebra α] (k : Nat) (c d : α) (r : RightExpr α n) (M₀ : Mapping α n) :
    iterate k (M₀ ⊓ Mapping.const α n d) (c ⊓ d) r = iterate k M₀ c r ⊓ Mapping.const α n d := by
  induction k generalizing M₀ with
  | zero => rfl
  | succ k' ih =>
    simp only [iterate]
    rw [ih, update_inf_const]

/-! ## Update Trees

Update trees provide a way to reason about sequences of partial updates.
They make explicit the DAG structure of iterating the update function,
and allow us to prove termination by showing that pruned trees have bounded depth.
-/

/-- Reversed length-indexed vector type for use in nested inductives.
    Unlike `Vector`, this is a pure inductive type without equality proofs.
    Uses `snoc` instead of `cons` to make the reversed nature explicit:
    - `snoc xs x` appends `x` at the end, so `x` has the highest index.
    - When matching `snoc xs x` with size `n+1`, `x` is at index `n`. -/
inductive Rvec (α : Type*) : Nat → Type _ where
  | nil : Rvec α 0
  | snoc : Rvec α n → α → Rvec α (n + 1)

namespace Rvec

/-- Get element at index. For `snoc xs x` of size `n+1`, `x` is at index `n`. -/
def get : {n : Nat} → Rvec α n → Fin n → α
  | n + 1, snoc xs x, ⟨i, hi⟩ =>
    if h : i = n then x
    else get xs ⟨i, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hi) h⟩

/-- Getting from snoc at an index other than the last returns from the rest. -/
@[simp]
theorem get_snoc_ne {xs : Rvec α n} {x : α} {i : Fin (n + 1)} (hi : i.val ≠ n) :
    (xs.snoc x).get i = xs.get ⟨i.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi⟩ :=
  dif_neg hi

/-- Create Rvec from function. -/
def ofFn (f : Fin n → α) : Rvec α n :=
  match n with
  | 0 => nil
  | n + 1 => snoc (ofFn fun i => f ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩) (f ⟨n, Nat.lt_succ_self n⟩)

/-- Convert Rvec to a list (in natural index order, so index 0 first). -/
def toList : Rvec α n → List α
  | nil => []
  | snoc xs x => xs.toList ++ [x]

theorem toList_length : (v : Rvec α n) → v.toList.length = n
  | nil => rfl
  | snoc xs _ => by simp [toList, toList_length xs]

/-- Convert Rvec to Vector. -/
def toVector (v : Rvec α n) : Vector α n :=
  ⟨v.toList.toArray, by simp [v.toList_length]⟩

/-- The i-th element of toList equals get i. -/
theorem toList_get (v : Rvec α n) (i : Fin n) : v.toList[i.val]'(by rw [toList_length]; exact i.isLt) = v.get i := by
  match n, v with
  | m + 1, snoc xs x =>
    simp only [toList]
    unfold get
    by_cases h : i.val = m
    · simp only [h, ↓reduceDIte]
      rw [List.getElem_append_right]
      · simp [toList_length xs]
      · simp [toList_length xs]
    · simp only [h, ↓reduceDIte]
      rw [List.getElem_append_left]
      exact toList_get xs ⟨i.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) h⟩

/-- toVector.get equals Rvec.get. -/
theorem toVector_get (v : Rvec α n) (i : Fin n) : v.toVector.get i = v.get i := by
  simp only [toVector, Vector.get, List.getElem_toArray]
  exact toList_get v i

end Rvec

/-- Tree structure representing complete (but possibly pruned) update sequences.
    - `leaf`: base case, evaluates to a provided mapping
    - `branch children`: for each variable v, children[v] = (active, subtree) where:
      * active = true: value at v is M'.get v ⊔ partial_update v M' c r (where M' = eval subtree)
      * active = false: value at v is just M'.get v (projection only, no new contribution)
    This representation ensures evaluation always produces full mappings at each level. -/
inductive UpdateTree (n : Nat) where
  | leaf : UpdateTree n
  | branch : Rvec (Bool × UpdateTree n) n → UpdateTree n

namespace UpdateTree

/-- Compute the value that would be written to variable v by propagating
    constraint c through right expression r.
    Returns the value that should be joined with M(v). -/
def partial_update [HeytingAlgebra α] (v : Fin n) (M : Mapping α n) (c : α) : RightExpr α n → α
  | var i => if v = i then c else ⊥
  | const _ => ⊥
  | meet r₁ r₂ => partial_update v M c r₁ ⊔ partial_update v M c r₂
  | imply l r =>
      let c' := c ⊓ LeftExpr.eval M l
      partial_update v M c' r

mutual
/-- Evaluate an update tree given a base mapping (for leaves), constraint, and expression. -/
def eval [HeytingAlgebra α] (t : UpdateTree n) (M : Mapping α n) (c : α) (r : RightExpr α n) : Mapping α n :=
  match t with
  | leaf => M
  | branch children => (evalRvec n (le_refl n) children M c r).toVector

/-- Recurse on k, processing children. With snoc, child at position k' controls variable k'. -/
def evalRvec [HeytingAlgebra α] (k : Nat) (hk : k ≤ n) (children : Rvec (Bool × UpdateTree n) k)
    (M : Mapping α n) (c : α) (r : RightExpr α n) : Rvec α k :=
  match k with
  | 0 => .nil
  | k' + 1 =>
      -- .snoc is outside the match, so knowing k = k' + 1 suffices to know result is .snoc
      .snoc
        (match children with | .snoc rest _ => evalRvec k' (by omega) rest M c r)
        (match children with
         | .snoc _ (active, subtree) =>
           let M' := eval subtree M c r
           if active then M'.get ⟨k', by omega⟩ ⊔ partial_update ⟨k', by omega⟩ M' c r
           else M'.get ⟨k', by omega⟩)
end

mutual
/-- Depth of a tree: counts the maximum number of "active" nodes along any path. -/
def depth (t : UpdateTree n) : Nat :=
  match t with
  | leaf => 0
  | branch children => depthRvec children

/-- Compute max depth over an Rvec of children. -/
def depthRvec (children : Rvec (Bool × UpdateTree n) m) : Nat :=
  match children with
  | .nil => 0
  | .snoc rest (active, subtree) =>
      max (if active then 1 + depth subtree else depth subtree) (depthRvec rest)
end

mutual
/-- Complete tree of depth k: represents all possible sequences of k partial updates.
    At depth k, all variables are active and share the same subtree (complete k-1). -/
def complete (d : Nat) (n : Nat) : UpdateTree n :=
  match d with
  | 0 => leaf
  | d' + 1 => branch (completeRvec d' n n (le_refl n))

/-- Helper for complete: produces the children Rvec for a complete tree.
    Each child is (true, complete d n) - all variables are active. -/
def completeRvec (d : Nat) (n : Nat) (k : Nat) (hk : k ≤ n) : Rvec (Bool × UpdateTree n) k :=
  match k with
  | 0 => .nil
  | k' + 1 => .snoc (completeRvec d n k' (by omega)) (true, complete d n)
end

mutual
/-- Specialized pruning for complete trees. Produces a tree equivalent to pruning complete d n,
    deactivating any variable that appears in `seen`. -/
def pruned_aux (d : Nat) (n : Nat) (seen : Finset (Fin n)) : UpdateTree n :=
  match d with
  | 0 => leaf
  | d' + 1 => branch (prunedRvec d' n n (le_refl n) seen)

/-- Helper for pruned_aux: produces the pruned children for a complete tree. -/
def prunedRvec (d : Nat) (n : Nat) (k : Nat) (hk : k ≤ n) (seen : Finset (Fin n)) : Rvec (Bool × UpdateTree n) k :=
  match k with
  | 0 => .nil
  | k' + 1 =>
    let v : Fin n := ⟨k', by omega⟩
    let child := if v ∈ seen then
      (false, pruned_aux d n seen)
    else
      (true, pruned_aux d n (seen ∪ {v}))
    .snoc (prunedRvec d n k' (by omega) seen) child
end

/-- Pruned complete tree of depth d. Deactivates duplicate variable updates along any path. -/
def pruned (d : Nat) (n : Nat) : UpdateTree n := pruned_aux d n ∅

/-! ### Update Tree Theorems -/

/-- Helper: the value at position i after update equals M.get i ⊔ partial_update i. -/
theorem update_get_eq_partial [HeytingAlgebra α] (M : Mapping α n) (c : α) (r : RightExpr α n) (i : Fin n) :
    (update M c r).get i = M.get i ⊔ partial_update i M c r := by
  induction r generalizing c with
  | var j =>
    simp only [update, partial_update]
    by_cases h : i = j
    · -- i = j: both sides are M.get i ⊔ c
      subst h
      simp only [Mapping.get_update_same, ↓reduceIte]
    · -- i ≠ j: LHS is M.get i, RHS is M.get i ⊔ ⊥ = M.get i
      simp only [Mapping.get_update_diff M j i c h, if_neg h, sup_bot_eq]
  | const _ =>
    simp only [update, partial_update, sup_bot_eq]
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [update, partial_update, Mapping.get_sup]
    rw [ih₁, ih₂]
    -- Goal: (M.get i ⊔ partial_update i M c r₁) ⊔ (M.get i ⊔ partial_update i M c r₂) =
    --       M.get i ⊔ (partial_update i M c r₁ ⊔ partial_update i M c r₂)
    ac_rfl
  | imply l r ih =>
    simp only [update, partial_update]
    exact ih (c ⊓ LeftExpr.eval M l)

/-- partial_update is monotone in the constraint c. -/
theorem partial_update_mono_c [HeytingAlgebra α] (v : Fin n) (M : Mapping α n) (c₁ c₂ : α) (r : RightExpr α n)
    (h : c₁ ≤ c₂) : partial_update v M c₁ r ≤ partial_update v M c₂ r := by
  induction r generalizing c₁ c₂ with
  | var j =>
    simp only [partial_update]
    by_cases hj : v = j
    · simp only [hj, ↓reduceIte]; exact h
    · simp only [hj, ↓reduceIte]; exact le_refl ⊥
  | const _ => simp only [partial_update]; exact le_refl ⊥
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [partial_update]
    exact sup_le_sup (ih₁ c₁ c₂ h) (ih₂ c₁ c₂ h)
  | imply l r ih =>
    simp only [partial_update]
    have h' : c₁ ⊓ LeftExpr.eval M l ≤ c₂ ⊓ LeftExpr.eval M l := inf_le_inf_right _ h
    exact ih (c₁ ⊓ LeftExpr.eval M l) (c₂ ⊓ LeftExpr.eval M l) h'

/-- partial_update is monotone in the mapping. -/
theorem partial_update_mono [HeytingAlgebra α] (v : Fin n) (M₁ M₂ : Mapping α n) (c : α) (r : RightExpr α n)
    (h : M₁ ≤ M₂) : partial_update v M₁ c r ≤ partial_update v M₂ c r := by
  induction r generalizing c with
  | var j =>
    simp only [partial_update]
    by_cases hj : v = j
    · simp only [hj, ↓reduceIte]; exact le_refl c
    · simp only [hj, ↓reduceIte]; exact le_refl ⊥
  | const _ => simp only [partial_update]; exact le_refl ⊥
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [partial_update]
    exact sup_le_sup (ih₁ c) (ih₂ c)
  | imply l r ih =>
    simp only [partial_update]
    -- LeftExpr.eval is monotone, so LeftExpr.eval M₁ l ≤ LeftExpr.eval M₂ l
    have h_left : LeftExpr.eval M₁ l ≤ LeftExpr.eval M₂ l := LeftExpr.eval_mono l h
    have h_inf : c ⊓ LeftExpr.eval M₁ l ≤ c ⊓ LeftExpr.eval M₂ l := inf_le_inf_left c h_left
    calc partial_update v M₁ (c ⊓ LeftExpr.eval M₁ l) r
        ≤ partial_update v M₂ (c ⊓ LeftExpr.eval M₁ l) r := ih (c ⊓ LeftExpr.eval M₁ l)
      _ ≤ partial_update v M₂ (c ⊓ LeftExpr.eval M₂ l) r :=
          partial_update_mono_c v M₂ _ _ r h_inf

/-- partial_update distributes over join in the constraint (up to inequality). -/
theorem partial_update_sup_c [HeytingAlgebra α] (v : Fin n) (M : Mapping α n) (c₁ c₂ : α) (r : RightExpr α n) :
    partial_update v M (c₁ ⊔ c₂) r ≤ partial_update v M c₁ r ⊔ c₂ := by
  induction r generalizing c₁ c₂ with
  | var i =>
    simp only [partial_update]
    by_cases h : v = i
    · simp only [h, ↓reduceIte]
      -- Goal: c₁ ⊔ c₂ ≤ c₁ ⊔ c₂
      exact le_refl _
    · simp only [h, ↓reduceIte]; exact bot_le
  | const _ =>
    simp only [partial_update]; exact bot_le
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [partial_update]
    calc partial_update v M (c₁ ⊔ c₂) r₁ ⊔ partial_update v M (c₁ ⊔ c₂) r₂
        ≤ (partial_update v M c₁ r₁ ⊔ c₂) ⊔ (partial_update v M c₁ r₂ ⊔ c₂) :=
            sup_le_sup (ih₁ c₁ c₂) (ih₂ c₁ c₂)
      _ = (partial_update v M c₁ r₁ ⊔ partial_update v M c₁ r₂) ⊔ c₂ := by ac_rfl
  | imply l r' ih =>
    simp only [partial_update]
    -- constraint is (c₁ ⊔ c₂) ⊓ eval M l = (c₁ ⊓ eval M l) ⊔ (c₂ ⊓ eval M l)
    have h_eq : (c₁ ⊔ c₂) ⊓ LeftExpr.eval M l = (c₁ ⊓ LeftExpr.eval M l) ⊔ (c₂ ⊓ LeftExpr.eval M l) := by
      let e := LeftExpr.eval M l
      calc (c₁ ⊔ c₂) ⊓ e = e ⊓ (c₁ ⊔ c₂) := inf_comm _ _
        _ = (e ⊓ c₁) ⊔ (e ⊓ c₂) := inf_sup_left e c₁ c₂
        _ = (c₁ ⊓ e) ⊔ (c₂ ⊓ e) := by rw [inf_comm e c₁, inf_comm e c₂]
    rw [h_eq]
    calc partial_update v M ((c₁ ⊓ LeftExpr.eval M l) ⊔ (c₂ ⊓ LeftExpr.eval M l)) r'
        ≤ partial_update v M (c₁ ⊓ LeftExpr.eval M l) r' ⊔ (c₂ ⊓ LeftExpr.eval M l) :=
            ih (c₁ ⊓ LeftExpr.eval M l) (c₂ ⊓ LeftExpr.eval M l)
      _ ≤ partial_update v M (c₁ ⊓ LeftExpr.eval M l) r' ⊔ c₂ := by
            apply sup_le_sup_left; exact inf_le_left

mutual
/-- eval is monotone in the base mapping. -/
theorem eval_mono [HeytingAlgebra α] (t : UpdateTree n) (M₁ M₂ : Mapping α n) (c : α) (r : RightExpr α n)
    (h : M₁ ≤ M₂) : eval t M₁ c r ≤ eval t M₂ c r := by
  match t with
  | leaf =>
    simp only [eval]
    exact h
  | branch children =>
    simp only [eval]
    intro i
    rw [Rvec.toVector_get, Rvec.toVector_get]
    exact evalRvec_mono n (le_refl n) children M₁ M₂ c r h i

theorem evalRvec_mono [HeytingAlgebra α] (k : Nat) (hk : k ≤ n) (children : Rvec (Bool × UpdateTree n) k)
    (M₁ M₂ : Mapping α n) (c : α) (r : RightExpr α n) (h : M₁ ≤ M₂) (i : Fin k) :
    (evalRvec k hk children M₁ c r).get i ≤ (evalRvec k hk children M₂ c r).get i := by
  match k, children with
  | 0, .nil => exact i.elim0
  | k' + 1, .snoc restChildren (active, subtree) =>
    simp only [evalRvec]
    unfold Rvec.get
    by_cases hi : i.val = k'
    · -- i is the last element, controlled by (active, subtree)
      simp only [hi, ↓reduceDIte]
      have h_sub : eval subtree M₁ c r ≤ eval subtree M₂ c r := eval_mono subtree M₁ M₂ c r h
      by_cases hactive : active
      · simp only [hactive, ↓reduceIte]
        have h1 : (eval subtree M₁ c r).get ⟨k', by omega⟩ ≤ (eval subtree M₂ c r).get ⟨k', by omega⟩ :=
          h_sub ⟨k', by omega⟩
        have h2 : partial_update ⟨k', by omega⟩ (eval subtree M₁ c r) c r ≤
                  partial_update ⟨k', by omega⟩ (eval subtree M₂ c r) c r :=
          partial_update_mono ⟨k', by omega⟩ (eval subtree M₁ c r) (eval subtree M₂ c r) c r h_sub
        exact sup_le_sup h1 h2
      · simp only [hactive]
        exact h_sub ⟨k', by omega⟩
    · -- i is in restChildren
      simp only [hi, ↓reduceDIte]
      exact evalRvec_mono k' (by omega) restChildren M₁ M₂ c r h ⟨i.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi⟩
end

mutual
/-- The base mapping is always bounded by the evaluation of any tree. -/
theorem M_le_eval [HeytingAlgebra α] (t : UpdateTree n) (M : Mapping α n) (c : α) (r : RightExpr α n) :
    M ≤ eval t M c r := by
  match t with
  | leaf =>
    simp only [eval]
    exact le_refl M
  | branch children =>
    simp only [eval]
    intro i
    rw [Rvec.toVector_get]
    exact M_le_evalRvec n (le_refl n) children M c r i

theorem M_le_evalRvec [HeytingAlgebra α] (k : Nat) (hk : k ≤ n) (children : Rvec (Bool × UpdateTree n) k)
    (M : Mapping α n) (c : α) (r : RightExpr α n) (i : Fin k) :
    M.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ ≤ (evalRvec k hk children M c r).get i := by
  match k, children with
  | 0, .nil => exact i.elim0
  | k' + 1, .snoc restChildren (active, subtree) =>
    simp only [evalRvec]
    unfold Rvec.get
    by_cases hi : i.val = k'
    · -- i is the last element, controlled by (active, subtree)
      simp only [hi, ↓reduceDIte]
      have h_sub : M ≤ eval subtree M c r := M_le_eval subtree M c r
      by_cases hactive : active
      · simp only [hactive, ↓reduceIte]
        calc M.get ⟨k', by omega⟩
            ≤ (eval subtree M c r).get ⟨k', by omega⟩ := h_sub ⟨k', by omega⟩
          _ ≤ (eval subtree M c r).get ⟨k', by omega⟩ ⊔ partial_update ⟨k', by omega⟩ (eval subtree M c r) c r := le_sup_left
      · simp only [hactive]
        exact h_sub ⟨k', by omega⟩
    · -- i is in restChildren
      simp only [hi, ↓reduceDIte]
      exact M_le_evalRvec k' (by omega) restChildren M c r ⟨i.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi⟩
end

/-- Helper: evalRvec on completeRvec gives the expected value at each position.
    With snoc, result position j corresponds to variable j. -/
theorem evalRvec_completeRvec [HeytingAlgebra α] (d : Nat) (k : Nat) (hk : k ≤ n)
    (M : Mapping α n) (c : α) (r : RightExpr α n) (j : Fin k) :
    (evalRvec k hk (completeRvec d n k hk) M c r).get j =
    (eval (complete d n) M c r).get ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ ⊔
      partial_update ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ (eval (complete d n) M c r) c r := by
  induction k with
  | zero => exact j.elim0
  | succ k' ih =>
    simp only [completeRvec, evalRvec]
    unfold Rvec.get
    by_cases hj : j.val = k'
    · simp only [hj, ↓reduceDIte, ↓reduceIte]
    · simp only [hj, ↓reduceDIte]
      exact ih (by omega) ⟨j.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) hj⟩

/-- The complete tree of depth k corresponds to iterating update k times. -/
theorem complete_eq_iterate [HeytingAlgebra α] (k : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n) :
    eval (complete k n) M c r = iterate k M c r := by
  induction k generalizing M with
  | zero =>
    -- Base case: complete 0 n = leaf, iterate 0 M = M
    simp [complete, eval, iterate]
  | succ k' ih =>
    -- Show equality by extensionality
    apply Vector.ext
    intro i hi
    -- LHS: eval (complete (k'+1) n) M c r = eval (branch (completeRvec ...)) M c r
    simp only [complete, iterate, eval]
    show (evalRvec n (le_refl n) (completeRvec k' n n (le_refl n)) M c r).toVector.get ⟨i, hi⟩ =
         (update (iterate k' M c r) c r).get ⟨i, hi⟩
    rw [Rvec.toVector_get]
    -- At position i, evalRvec gives: M'.get i ⊔ partial_update i M' c r
    -- where M' = eval (complete k' n) M c r = iterate k' M c r (by IH)
    rw [evalRvec_completeRvec k' n (le_refl n) M c r ⟨i, hi⟩]
    -- Now we have: (eval (complete k' n) M c r).get ⟨i, hi⟩ ⊔ partial_update ⟨i, hi⟩ (eval (complete k' n) M c r) c r
    rw [ih]
    -- Now we have: (iterate k' M c r).get ⟨i, hi⟩ ⊔ partial_update ⟨i, hi⟩ (iterate k' M c r) c r
    -- RHS: (update (iterate k' M c r) c r).get ⟨i, hi⟩
    rw [update_get_eq_partial]

/-- Evaluation of complete tree is monotone in depth. -/
theorem complete_eval_depth_mono [HeytingAlgebra α] (k₁ k₂ : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n)
    (h : k₁ ≤ k₂) : eval (complete k₁ n) M c r ≤ eval (complete k₂ n) M c r := by
  rw [complete_eq_iterate, complete_eq_iterate]
  exact iterate_le_of_le M c r h

/-- Key lemma: partial_update with mapping P ⊔ const d is bounded by
    partial_update with mapping P, plus d.
    This captures how constant corrections propagate through partial_update. -/
theorem partial_update_sup_const [HeytingAlgebra α] (v : Fin n) (P : Mapping α n) (c d : α) (r : RightExpr α n) :
    partial_update v (P ⊔ Mapping.const α n d) c r ≤ partial_update v P c r ⊔ d := by
  induction r generalizing c with
  | var i =>
    simp only [partial_update]
    by_cases h : v = i
    · simp only [h, ↓reduceIte]; exact le_sup_left
    · simp only [h, ↓reduceIte]; exact bot_le
  | const _ =>
    simp only [partial_update]; exact bot_le
  | meet r₁ r₂ ih₁ ih₂ =>
    simp only [partial_update]
    calc partial_update v (P ⊔ Mapping.const α n d) c r₁ ⊔
         partial_update v (P ⊔ Mapping.const α n d) c r₂
        ≤ (partial_update v P c r₁ ⊔ d) ⊔ (partial_update v P c r₂ ⊔ d) :=
            sup_le_sup (ih₁ c) (ih₂ c)
      _ = (partial_update v P c r₁ ⊔ partial_update v P c r₂) ⊔ d := by ac_rfl
  | imply l r' ih =>
    simp only [partial_update]
    -- c' := c ⊓ LeftExpr.eval (P ⊔ const d) l
    -- c'' := c ⊓ LeftExpr.eval P l
    -- Need: partial_update v (P ⊔ const d) c' r' ≤ partial_update v P c'' r' ⊔ d
    let c' := c ⊓ LeftExpr.eval (P ⊔ Mapping.const α n d) l
    let c'' := c ⊓ LeftExpr.eval P l
    -- By IH: partial_update v (P ⊔ const d) c' r' ≤ partial_update v P c' r' ⊔ d
    have h_ih := ih c'
    -- By eval_sup_le_max: LeftExpr.eval (P ⊔ const d) l ≤ LeftExpr.eval P l ⊔ d
    have h_eval : LeftExpr.eval (P ⊔ Mapping.const α n d) l ≤ LeftExpr.eval P l ⊔ d := by
      by_cases hn : n = 0
      · -- n = 0: no variables, left expression is just constants
        subst hn
        have h_eq : ∀ (l' : LeftExpr α 0), LeftExpr.eval (P ⊔ Mapping.const α 0 d) l' = LeftExpr.eval P l' := by
          intro l'
          induction l' with
          | var i => exact Fin.elim0 i
          | const c => rfl
          | join l₁ l₂ ih₁ ih₂ => simp only [LeftExpr.eval, ih₁, ih₂]
          | meet l₁ l₂ ih₁ ih₂ => simp only [LeftExpr.eval, ih₁, ih₂]
        rw [h_eq l]
        exact le_sup_left
      · -- n > 0: can use max_const
        have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
        have h_max : Mapping.max (Mapping.const α n d) = d := Mapping.max_const d hn_pos
        calc LeftExpr.eval (P ⊔ Mapping.const α n d) l
            ≤ LeftExpr.eval P l ⊔ Mapping.max (Mapping.const α n d) := LeftExpr.eval_sup_le_max P _ l
          _ = LeftExpr.eval P l ⊔ d := by rw [h_max]
    -- So c' ≤ c ⊓ (LeftExpr.eval P l ⊔ d) = (c ⊓ LeftExpr.eval P l) ⊔ (c ⊓ d) = c'' ⊔ (c ⊓ d)
    have h_c' : c' ≤ c'' ⊔ (c ⊓ d) := by
      calc c' = c ⊓ LeftExpr.eval (P ⊔ Mapping.const α n d) l := rfl
        _ ≤ c ⊓ (LeftExpr.eval P l ⊔ d) := inf_le_inf_left c h_eval
        _ = (c ⊓ LeftExpr.eval P l) ⊔ (c ⊓ d) := inf_sup_left c (LeftExpr.eval P l) d
        _ = c'' ⊔ (c ⊓ d) := rfl
    -- By monotonicity in constraint: partial_update v P c' r' ≤ partial_update v P (c'' ⊔ (c ⊓ d)) r'
    have h_mono : partial_update v P c' r' ≤ partial_update v P (c'' ⊔ (c ⊓ d)) r' :=
      partial_update_mono_c v P c' (c'' ⊔ (c ⊓ d)) r' h_c'
    -- partial_update v P (c'' ⊔ (c ⊓ d)) r' ≤ partial_update v P c'' r' ⊔ (c ⊓ d)
    -- This follows from partial_update_sup_c
    have h_dist : partial_update v P (c'' ⊔ (c ⊓ d)) r' ≤ partial_update v P c'' r' ⊔ (c ⊓ d) :=
      partial_update_sup_c v P c'' (c ⊓ d) r'
    calc partial_update v (P ⊔ Mapping.const α n d) c' r'
        ≤ partial_update v P c' r' ⊔ d := h_ih
      _ ≤ partial_update v P (c'' ⊔ (c ⊓ d)) r' ⊔ d := sup_le_sup_right h_mono d
      _ ≤ (partial_update v P c'' r' ⊔ (c ⊓ d)) ⊔ d := sup_le_sup_right h_dist d
      _ = partial_update v P c'' r' ⊔ d := by
          calc (partial_update v P c'' r' ⊔ (c ⊓ d)) ⊔ d
              = partial_update v P c'' r' ⊔ ((c ⊓ d) ⊔ d) := by ac_rfl
            _ = partial_update v P c'' r' ⊔ d := by
                have h : (c ⊓ d) ⊔ d = d := sup_of_le_right (inf_le_right (a := c) (b := d))
                rw [h]

/-- General version: partial_update with M ⊔ N is bounded by pu M ⊔ max N.
    This captures how arbitrary corrections propagate through partial_update. -/
theorem partial_update_sup_max [HeytingAlgebra α] (v : Fin n) (M N : Mapping α n) (c : α) (r : RightExpr α n) :
    partial_update v (M ⊔ N) c r ≤ partial_update v M c r ⊔ Mapping.max N := by
  -- This follows from partial_update_sup_const with k = Mapping.max N
  -- since M ⊔ N ≤ M ⊔ const (max N)
  have h_le : M ⊔ N ≤ M ⊔ Mapping.const α n (Mapping.max N) := by
    intro j
    simp only [Mapping.get_sup, Mapping.get_const]
    exact sup_le_sup_left (Mapping.get_le_max N j) _
  calc partial_update v (M ⊔ N) c r
      ≤ partial_update v (M ⊔ Mapping.const α n (Mapping.max N)) c r :=
        partial_update_mono v (M ⊔ N) (M ⊔ Mapping.const α n (Mapping.max N)) c r h_le
    _ ≤ partial_update v M c r ⊔ Mapping.max N :=
        partial_update_sup_const v M c (Mapping.max N) r

/-! ### Auxiliary Lemmas for pruned_eval_ge

The key insight is that pruning can only deactivate nodes (changing active→inactive),
which can only decrease the result at each position. However, the correction term
accounts for this: the variables in `seen` have already contributed their maximum
effect, which is bounded by `partial_update`.

Key lemma used: `eval_sup_le_max` bounds how much an increase in a child's mapping
can affect the parent's mapping. This bound can be absorbed by the correction term
from seen nodes.
-/

mutual
/-- Evaluation of pruned_aux is monotone in depth: deeper trees give larger results. -/
theorem pruned_aux_eval_depth_mono [HeytingAlgebra α] (d : Nat) (seen : Finset (Fin n))
    (M : Mapping α n) (c : α) (r : RightExpr α n) :
    eval (pruned_aux d n seen) M c r ≤ eval (pruned_aux (d + 1) n seen) M c r := by
  match d with
  | 0 =>
    -- LHS: eval (pruned_aux 0 n seen) = eval leaf = M
    -- RHS: eval (pruned_aux 1 n seen) = eval (branch (prunedRvec 0 n n _ seen))
    simp only [pruned_aux, eval]
    intro i
    rw [Rvec.toVector_get]
    exact M_le_evalRvec n (le_refl n) (prunedRvec 0 n n (le_refl n) seen) M c r i
  | d' + 1 =>
    -- LHS: eval (pruned_aux (d'+1) n seen) = eval (branch (prunedRvec d' n n _ seen))
    -- RHS: eval (pruned_aux (d'+2) n seen) = eval (branch (prunedRvec (d'+1) n n _ seen))
    simp only [pruned_aux, eval]
    intro i
    simp only [Rvec.toVector_get]
    exact prunedRvec_eval_depth_mono d' n n (le_refl n) seen M c r i

theorem prunedRvec_eval_depth_mono [HeytingAlgebra α] (d : Nat) (n : Nat) (k : Nat) (hk : k ≤ n)
    (seen : Finset (Fin n)) (M : Mapping α n) (c : α) (r : RightExpr α n) (i : Fin k) :
    (evalRvec k hk (prunedRvec d n k hk seen) M c r).get i ≤
    (evalRvec k hk (prunedRvec (d + 1) n k hk seen) M c r).get i := by
  match k with
  | 0 => exact i.elim0
  | k' + 1 =>
    simp only [prunedRvec, evalRvec]
    unfold Rvec.get
    by_cases hi : i.val = k'
    · -- i is the last element
      simp only [hi, ↓reduceDIte]
      by_cases hv : (⟨k', by omega⟩ : Fin n) ∈ seen
      · -- v ∈ seen: child is (false, pruned_aux d n seen), active = false
        simp only [hv, ↓reduceIte]
        -- LHS: (eval (pruned_aux d n seen) M c r).get v
        -- RHS: (eval (pruned_aux (d+1) n seen) M c r).get v
        exact pruned_aux_eval_depth_mono d seen M c r ⟨k', by omega⟩
      · -- v ∉ seen: child is (true, pruned_aux d n (seen ∪ {v})), active = true
        simp only [hv, ↓reduceIte]
        -- LHS: (eval (pruned_aux d n (seen ∪ {v})) M c r).get v ⊔ pu_v(...)
        -- RHS: (eval (pruned_aux (d+1) n (seen ∪ {v})) M c r).get v ⊔ pu_v(...)
        have h := pruned_aux_eval_depth_mono d (seen ∪ {⟨k', by omega⟩}) M c r
        exact sup_le_sup (h ⟨k', by omega⟩) (partial_update_mono ⟨k', by omega⟩ _ _ c r h)
    · -- i is in rest
      simp only [hi, ↓reduceDIte]
      exact prunedRvec_eval_depth_mono d n k' (by omega) seen M c r ⟨i.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi⟩
end

mutual
/-- Evaluation of pruned_aux is antimonotone in the seen set: larger seen → smaller eval.
    This is because a larger seen set deactivates more nodes. -/
theorem pruned_aux_eval_seen_mono [HeytingAlgebra α] (d : Nat) (S₁ S₂ : Finset (Fin n))
    (h_sub : S₂ ⊆ S₁) (M : Mapping α n) (c : α) (r : RightExpr α n) :
    eval (pruned_aux d n S₁) M c r ≤ eval (pruned_aux d n S₂) M c r := by
  match d with
  | 0 =>
    simp only [pruned_aux, eval]
    exact le_refl M
  | d' + 1 =>
    simp only [pruned_aux, eval]
    intro i
    simp only [Rvec.toVector_get]
    exact prunedRvec_eval_seen_mono d' n n (le_refl n) S₁ S₂ h_sub M c r i

theorem prunedRvec_eval_seen_mono [HeytingAlgebra α] (d : Nat) (n : Nat) (k : Nat) (hk : k ≤ n)
    (S₁ S₂ : Finset (Fin n)) (h_sub : S₂ ⊆ S₁) (M : Mapping α n) (c : α) (r : RightExpr α n) (i : Fin k) :
    (evalRvec k hk (prunedRvec d n k hk S₁) M c r).get i ≤
    (evalRvec k hk (prunedRvec d n k hk S₂) M c r).get i := by
  match k with
  | 0 => exact i.elim0
  | k' + 1 =>
    simp only [prunedRvec, evalRvec]
    unfold Rvec.get
    by_cases hi : i.val = k'
    · -- i is the last element
      simp only [hi, ↓reduceDIte]
      let v : Fin n := ⟨k', by omega⟩
      by_cases hv₁ : (⟨k', by omega⟩ : Fin n) ∈ S₁
      · -- v ∈ S₁
        simp only [hv₁, ↓reduceIte]
        by_cases hv₂ : (⟨k', by omega⟩ : Fin n) ∈ S₂
        · -- v ∈ S₂: both inactive
          simp only [hv₂, ↓reduceIte]
          exact pruned_aux_eval_seen_mono d S₁ S₂ h_sub M c r ⟨k', by omega⟩
        · -- v ∉ S₂: S₁ inactive, S₂ active
          simp only [hv₂, ↓reduceIte]
          -- LHS: (eval (pruned_aux d n S₁)).get v
          -- RHS: (eval (pruned_aux d n (S₂ ∪ {v}))).get v ⊔ pu_v(...)
          have h_S₁_sub : S₂ ∪ {⟨k', by omega⟩} ⊆ S₁ := by
            intro x hx
            simp only [Finset.mem_union, Finset.mem_singleton] at hx
            cases hx with
            | inl hx => exact h_sub hx
            | inr hx => subst hx; exact hv₁
          calc (eval (pruned_aux d n S₁) M c r).get ⟨k', by omega⟩
              ≤ (eval (pruned_aux d n (S₂ ∪ {⟨k', by omega⟩})) M c r).get ⟨k', by omega⟩ :=
                pruned_aux_eval_seen_mono d S₁ (S₂ ∪ {⟨k', by omega⟩}) h_S₁_sub M c r ⟨k', by omega⟩
            _ ≤ (eval (pruned_aux d n (S₂ ∪ {⟨k', by omega⟩})) M c r).get ⟨k', by omega⟩ ⊔
                partial_update ⟨k', by omega⟩ (eval (pruned_aux d n (S₂ ∪ {⟨k', by omega⟩})) M c r) c r := le_sup_left
      · -- v ∉ S₁, so also v ∉ S₂ (since S₂ ⊆ S₁)
        have hv₂ : (⟨k', by omega⟩ : Fin n) ∉ S₂ := fun h => hv₁ (h_sub h)
        simp only [hv₁, hv₂, ↓reduceIte]
        -- Both active with sets S₁ ∪ {v} and S₂ ∪ {v}
        have h_sub' : S₂ ∪ {v} ⊆ S₁ ∪ {v} := Finset.union_subset_union h_sub (Finset.Subset.refl {v})
        have h := pruned_aux_eval_seen_mono d (S₁ ∪ {v}) (S₂ ∪ {v}) h_sub' M c r
        exact sup_le_sup (h v) (partial_update_mono v _ _ c r h)
    · -- i is in rest
      simp only [hi, ↓reduceDIte]
      exact prunedRvec_eval_seen_mono d n k' (by omega) S₁ S₂ h_sub M c r ⟨i.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi⟩
end

mutual
/-- Auxiliary lemma: eval (complete d n) ≤ eval (pruned_aux d n seen) ⊔ correction.
    The correction captures contributions from variables in `seen` that get deactivated.
    Importantly, the correction uses the PRUNED tree's eval, not the original. -/
theorem pruned_aux_eval_ge [HeytingAlgebra α] (d : Nat) (seen : Finset (Fin n))
    (M : Mapping α n) (c : α) (r : RightExpr α n) :
    eval (complete d n) M c r ≤ eval (pruned_aux d n seen) M c r ⊔
      seen.sup (fun v => Mapping.const α n
        (partial_update v (eval (pruned_aux d n seen) M c r) c r)) := by
  match d with
  | 0 =>
    simp only [complete, pruned_aux, eval]
    exact Mapping.le_sup_left M _
  | d' + 1 =>
    simp only [complete, eval]
    intro i
    simp only [Mapping.get_sup, Rvec.toVector_get]
    -- Convert: (seen.sup (fun v => Mapping.const α n (f v))).get i = seen.sup (fun v => f v)
    rw [Mapping.sup_const_eq_const_sup, Mapping.get_const]
    -- Note: pruned_aux (d'+1) n seen = branch (prunedRvec d' n n _ seen)
    -- so eval (pruned_aux (d'+1) n seen) = (evalRvec n _ (prunedRvec d' n n _ seen) ...).toVector
    have h := prunedRvec_eval_ge d' n n (le_refl n) seen M c r i
    simp only [pruned_aux, eval, Rvec.toVector_get] at h ⊢
    exact h

/-- Helper for pruned_aux_eval_ge: bounds each position of evalRvec.
    Compares evalRvec of complete's children to evalRvec of pruned children.
    The correction uses eval of the parent pruned_aux tree (depth d+1). -/
theorem prunedRvec_eval_ge [HeytingAlgebra α] (d : Nat) (n : Nat) (k : Nat) (hk : k ≤ n)
    (seen : Finset (Fin n)) (M : Mapping α n) (c : α) (r : RightExpr α n) (i : Fin k) :
    (evalRvec k hk (completeRvec d n k hk) M c r).get i ≤
      (evalRvec k hk (prunedRvec d n k hk seen) M c r).get i ⊔
      seen.sup (fun v => partial_update v (eval (pruned_aux (d + 1) n seen) M c r) c r) := by
  match k with
  | 0 => exact i.elim0
  | k' + 1 =>
    by_cases hi : i.val = k'
    · -- Position i = k', controlled by variable v = ⟨k', _⟩
      simp only [completeRvec, prunedRvec, evalRvec]
      unfold Rvec.get
      simp only [hi, ↓reduceDIte]
      let v : Fin n := ⟨k', by omega⟩
      let E := eval (complete d n) M c r  -- complete tree eval
      let P := eval (pruned_aux d n seen) M c r  -- pruned tree eval at depth d
      let P' := eval (pruned_aux (d + 1) n seen) M c r  -- pruned tree eval at depth d+1
      let correction := seen.sup (fun u => partial_update u P' c r)
      have hn : 0 < n := by omega
      -- LHS: E.get v ⊔ pu_v(E)
      -- RHS depends on whether v ∈ seen
      by_cases hv : v ∈ seen
      · -- v ∈ seen: child is (false, pruned_aux d n seen), active = false
        -- RHS: P.get v ⊔ correction
        simp only [↓reduceIte]
        -- From IH: E ≤ P ⊔ seen.sup (fun u => Mapping.const (pu_u(P)))
        have ih := pruned_aux_eval_ge d seen M c r
        -- For E.get v:
        have h_E_v : E.get v ≤ P.get v ⊔ seen.sup (fun u => partial_update u P c r) := by
          have := ih v
          simp only [Mapping.get_sup, Mapping.sup_const_eq_const_sup, Mapping.get_const] at this
          exact this
        -- For pu_v(E): Use partial_update_sup_max
        have h_pu_E : partial_update v E c r ≤
            partial_update v P c r ⊔ seen.sup (fun u => partial_update u P c r) := by
          have h_E_le : E ≤ P ⊔ seen.sup (fun u => Mapping.const α n (partial_update u P c r)) := ih
          calc partial_update v E c r
              ≤ partial_update v (P ⊔ seen.sup (fun u => Mapping.const α n (partial_update u P c r))) c r :=
                partial_update_mono v E _ c r h_E_le
            _ ≤ partial_update v P c r ⊔ Mapping.max (seen.sup (fun u => Mapping.const α n (partial_update u P c r))) :=
                partial_update_sup_max v P _ c r
            _ ≤ partial_update v P c r ⊔ seen.sup (fun u => partial_update u P c r) :=
                sup_le_sup_left (Mapping.max_finset_sup_const_le hn seen _) _
        -- Combine E.get v ⊔ pu_v(E)
        have h_combined : E.get v ⊔ partial_update v E c r ≤
            P.get v ⊔ seen.sup (fun u => partial_update u P c r) := by
          have h1 : partial_update v P c r ≤ seen.sup (fun u => partial_update u P c r) :=
            Finset.le_sup (f := fun u => partial_update u P c r) hv
          calc E.get v ⊔ partial_update v E c r
              ≤ (P.get v ⊔ seen.sup (fun u => partial_update u P c r)) ⊔
                (partial_update v P c r ⊔ seen.sup (fun u => partial_update u P c r)) :=
                  sup_le_sup h_E_v h_pu_E
            _ = P.get v ⊔ partial_update v P c r ⊔ seen.sup (fun u => partial_update u P c r) := by ac_rfl
            _ ≤ P.get v ⊔ seen.sup (fun u => partial_update u P c r) ⊔ seen.sup (fun u => partial_update u P c r) :=
                sup_le_sup_right (sup_le_sup_left h1 _) _
            _ = P.get v ⊔ seen.sup (fun u => partial_update u P c r) := by
                rw [sup_assoc, sup_idem]
        -- Now relate P to P' using depth monotonicity
        have h_depth : P ≤ P' := pruned_aux_eval_depth_mono d seen M c r
        have h_pu_mono : ∀ b ∈ seen, partial_update b P c r ≤ partial_update b P' c r :=
          fun u _ => partial_update_mono u P P' c r h_depth
        -- First show the RHS simplifies to P.get v ⊔ correction
        have h_rhs : (if (if v ∈ seen then (false, pruned_aux d n seen) else (true, pruned_aux d n (seen ∪ {v}))).1 = true
            then (eval (if v ∈ seen then (false, pruned_aux d n seen) else (true, pruned_aux d n (seen ∪ {v}))).2 M c r).get ⟨k', by omega⟩ ⊔
                 partial_update ⟨k', by omega⟩ (eval (if v ∈ seen then (false, pruned_aux d n seen) else (true, pruned_aux d n (seen ∪ {v}))).2 M c r) c r
            else (eval (if v ∈ seen then (false, pruned_aux d n seen) else (true, pruned_aux d n (seen ∪ {v}))).2 M c r).get ⟨k', by omega⟩) ⊔ correction
            = P.get v ⊔ correction := by simp only [hv, ↓reduceIte, Bool.false_eq_true]; rfl
        rw [h_rhs]
        calc E.get v ⊔ partial_update v E c r
            ≤ P.get v ⊔ seen.sup (fun u => partial_update u P c r) := h_combined
          _ ≤ P.get v ⊔ seen.sup (fun u => partial_update u P' c r) :=
              sup_le_sup_left (Finset.sup_mono_fun h_pu_mono) _
          _ ≤ P.get v ⊔ correction := le_refl _
      · -- v ∉ seen: child is (true, pruned_aux d n (seen ∪ {v})), active = true
        -- RHS: Q.get v ⊔ pu_v(Q) ⊔ correction where Q = eval (pruned_aux d n (seen ∪ {v}))
        simp only [↓reduceIte]
        let Q := eval (pruned_aux d n (seen ∪ {v})) M c r
        -- From IH: E ≤ Q ⊔ (seen ∪ {v}).sup (fun u => Mapping.const (pu_u(Q)))
        have ih := pruned_aux_eval_ge d (seen ∪ {v}) M c r
        -- Similar to above but for Q instead of P
        have h_E_v : E.get v ≤ Q.get v ⊔ (seen ∪ {v}).sup (fun u => partial_update u Q c r) := by
          have := ih v
          simp only [Mapping.get_sup, Mapping.sup_const_eq_const_sup, Mapping.get_const] at this
          exact this
        have h_pu_E : partial_update v E c r ≤
            partial_update v Q c r ⊔ (seen ∪ {v}).sup (fun u => partial_update u Q c r) := by
          have h_E_le : E ≤ Q ⊔ (seen ∪ {v}).sup (fun u => Mapping.const α n (partial_update u Q c r)) := ih
          calc partial_update v E c r
              ≤ partial_update v (Q ⊔ (seen ∪ {v}).sup (fun u => Mapping.const α n (partial_update u Q c r))) c r :=
                partial_update_mono v E _ c r h_E_le
            _ ≤ partial_update v Q c r ⊔ Mapping.max ((seen ∪ {v}).sup (fun u => Mapping.const α n (partial_update u Q c r))) :=
                partial_update_sup_max v Q _ c r
            _ ≤ partial_update v Q c r ⊔ (seen ∪ {v}).sup (fun u => partial_update u Q c r) :=
                sup_le_sup_left (Mapping.max_finset_sup_const_le hn (seen ∪ {v}) _) _
        -- Expand (seen ∪ {v}).sup = seen.sup ⊔ pu_v(Q)
        have h_expand : (seen ∪ {v}).sup (fun u => partial_update u Q c r) =
            seen.sup (fun u => partial_update u Q c r) ⊔ partial_update v Q c r := by
          rw [Finset.sup_union, Finset.sup_singleton]
        -- Combine and simplify
        have h_combined : E.get v ⊔ partial_update v E c r ≤
            Q.get v ⊔ partial_update v Q c r ⊔ seen.sup (fun u => partial_update u Q c r) := by
          calc E.get v ⊔ partial_update v E c r
              ≤ (Q.get v ⊔ (seen ∪ {v}).sup (fun u => partial_update u Q c r)) ⊔
                (partial_update v Q c r ⊔ (seen ∪ {v}).sup (fun u => partial_update u Q c r)) :=
                  sup_le_sup h_E_v h_pu_E
            _ = Q.get v ⊔ (seen ∪ {v}).sup (fun u => partial_update u Q c r) ⊔ partial_update v Q c r := by ac_rfl
            _ = Q.get v ⊔ (seen.sup (fun u => partial_update u Q c r) ⊔ partial_update v Q c r) ⊔
                partial_update v Q c r := by rw [h_expand]
            _ = Q.get v ⊔ partial_update v Q c r ⊔ seen.sup (fun u => partial_update u Q c r) := by ac_rfl
        -- Now need: seen.sup (fun u => pu_u(Q)) ≤ correction = seen.sup (fun u => pu_u(P'))
        -- This requires Q ≤ P', which needs seen monotonicity + depth monotonicity
        -- Q = eval (pruned_aux d n (seen ∪ {v})) ≤ eval (pruned_aux d n seen) ≤ eval (pruned_aux (d+1) n seen) = P'
        have h_seen_sub : seen ⊆ seen ∪ {v} := Finset.subset_union_left
        have h_Q_le_P : Q ≤ P := pruned_aux_eval_seen_mono d (seen ∪ {v}) seen h_seen_sub M c r
        have h_P_le_P' : P ≤ P' := pruned_aux_eval_depth_mono d seen M c r
        have h_Q_le_P' : Q ≤ P' := Mapping.le_trans h_Q_le_P h_P_le_P'
        have h_pu_mono : ∀ b ∈ seen, partial_update b Q c r ≤ partial_update b P' c r :=
          fun u _ => partial_update_mono u Q P' c r h_Q_le_P'
        -- First show RHS simplifies
        have h_rhs : (if (if v ∈ seen then (false, pruned_aux d n seen) else (true, pruned_aux d n (seen ∪ {v}))).1 = true
            then (eval (if v ∈ seen then (false, pruned_aux d n seen) else (true, pruned_aux d n (seen ∪ {v}))).2 M c r).get ⟨k', by omega⟩ ⊔
                 partial_update ⟨k', by omega⟩ (eval (if v ∈ seen then (false, pruned_aux d n seen) else (true, pruned_aux d n (seen ∪ {v}))).2 M c r) c r
            else (eval (if v ∈ seen then (false, pruned_aux d n seen) else (true, pruned_aux d n (seen ∪ {v}))).2 M c r).get ⟨k', by omega⟩) ⊔ correction
            = Q.get v ⊔ partial_update v Q c r ⊔ correction := by simp only [hv, ↓reduceIte]; rfl
        rw [h_rhs]
        calc E.get v ⊔ partial_update v E c r
            ≤ Q.get v ⊔ partial_update v Q c r ⊔ seen.sup (fun u => partial_update u Q c r) := h_combined
          _ ≤ Q.get v ⊔ partial_update v Q c r ⊔ seen.sup (fun u => partial_update u P' c r) :=
              sup_le_sup_left (Finset.sup_mono_fun h_pu_mono) _
          _ = Q.get v ⊔ partial_update v Q c r ⊔ correction := rfl
    · -- Position i ≠ k', in rest of Rvec
      -- evalRvec at k'+1 produces .snoc, and get at i≠k' returns from the init part
      simp only [prunedRvec, completeRvec, evalRvec, Rvec.get_snoc_ne hi]
      exact prunedRvec_eval_ge d n k' (by omega) seen M c r ⟨i.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi⟩
end

/-- Pruning a complete tree preserves or improves the evaluation.
    This is the key lemma: eval (pruned d n) M c r ≥ eval (complete d n) M c r -/
theorem pruned_eval_ge [HeytingAlgebra α] (d : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n) :
    eval (pruned d n) M c r ≥ eval (complete d n) M c r := by
  unfold pruned
  have h := pruned_aux_eval_ge d ∅ M c r
  simp only [Finset.sup_empty] at h
  calc eval (complete d n) M c r ≤ eval (pruned_aux d n ∅) M c r ⊔ ⊥ := h
    _ = eval (pruned_aux d n ∅) M c r := sup_bot_eq _

mutual
/-- Helper: pruned_aux with a seen set produces depth ≤ n - seen.card. -/
theorem pruned_aux_depth_le (d : Nat) (seen : Finset (Fin n)) (h : seen.card ≤ n) :
    depth (pruned_aux d n seen) ≤ n - seen.card := by
  match d with
  | 0 =>
    simp only [pruned_aux, depth]
    omega
  | d' + 1 =>
    simp only [pruned_aux, depth]
    exact prunedRvec_depthRvec_le d' n n (le_refl n) seen h

/-- Helper: depthRvec of pruned children is bounded by n - seen.card. -/
theorem prunedRvec_depthRvec_le (d : Nat) (n : Nat) (k : Nat) (hk : k ≤ n) (seen : Finset (Fin n))
    (h : seen.card ≤ n) :
    depthRvec (prunedRvec d n k hk seen) ≤ n - seen.card := by
  match k with
  | 0 =>
    simp only [prunedRvec, depthRvec]
    omega
  | k' + 1 =>
    simp only [prunedRvec, depthRvec]
    apply Nat.max_le.mpr
    constructor
    · -- Bound for the current child
      split
      · -- v ∈ seen: child is (false, pruned_aux d n seen)
        -- Not active, so just depth of pruned subtree
        exact pruned_aux_depth_le d seen h
      · -- v ∉ seen: child is (true, pruned_aux d n (seen ∪ {v}))
        rename_i hv
        simp only [↓reduceIte]
        -- Active, so 1 + depth of pruned subtree with expanded seen
        have h_card : (seen ∪ {⟨k', by omega⟩}).card = seen.card + 1 := by
          rw [Finset.card_union_of_disjoint]
          · simp only [Finset.card_singleton]
          · simp only [Finset.disjoint_singleton_right, hv, not_false_eq_true]
        have h_lt : seen.card < n := by
          have h_ssubset : seen ⊂ Finset.univ := by
            rw [Finset.ssubset_iff_subset_ne]
            constructor
            · exact Finset.subset_univ seen
            · intro h_eq
              have : (⟨k', by omega⟩ : Fin n) ∈ Finset.univ := Finset.mem_univ _
              rw [← h_eq] at this
              exact hv this
          calc seen.card < Finset.univ.card := Finset.card_lt_card h_ssubset
            _ = Fintype.card (Fin n) := Finset.card_univ
            _ = n := Fintype.card_fin n
        have h_new : (seen ∪ {⟨k', by omega⟩}).card ≤ n := by rw [h_card]; omega
        have ih := pruned_aux_depth_le d (seen ∪ {⟨k', by omega⟩}) h_new
        rw [h_card] at ih
        omega
    · -- Bound for the rest
      exact prunedRvec_depthRvec_le d n k' (by omega) seen h
end

/-- Pruned complete trees have depth bounded by the number of variables. -/
theorem pruned_depth_le (d : Nat) :
    depth (pruned d n) ≤ n := by
  unfold pruned
  have h : (∅ : Finset (Fin n)).card ≤ n := by simp
  have := pruned_aux_depth_le d ∅ h
  simp only [Finset.card_empty, Nat.sub_zero] at this
  exact this

mutual
/-- Complete trees are maximal: any tree evaluates to at most the complete tree of the same depth. -/
theorem complete_maximal [HeytingAlgebra α] (t : UpdateTree n) (M : Mapping α n) (c : α) (r : RightExpr α n) :
    eval t M c r ≤ eval (complete (depth t) n) M c r := by
  match t with
  | leaf =>
    simp only [depth, complete, eval]
    intro j; exact le_refl _
  | branch children =>
    simp only [eval, depth]
    intro i
    rw [Rvec.toVector_get]
    -- Need to show: evalRvec(...children...).get i ≤ (eval (complete (depthRvec children) n) M c r).get i
    -- The complete tree has depth k = depthRvec children, so it's branch (completeRvec (k-1) n n _)
    have h := complete_maximal_rvec n (le_refl n) children M c r i
    exact h

/-- Helper for complete_maximal: each position of evalRvec is bounded by the complete tree. -/
theorem complete_maximal_rvec [HeytingAlgebra α] (k : Nat) (hk : k ≤ n) (children : Rvec (Bool × UpdateTree n) k)
    (M : Mapping α n) (c : α) (r : RightExpr α n) (i : Fin k) :
    (evalRvec k hk children M c r).get i ≤ (eval (complete (depthRvec children) n) M c r).get ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  match k, children with
  | 0, .nil => exact i.elim0
  | k' + 1, .snoc restChildren (active, subtree) =>
    simp only [evalRvec, depthRvec]
    unfold Rvec.get
    by_cases hi : i.val = k'
    · -- i is the last position, controlled by (active, subtree)
      simp only [hi, ↓reduceDIte]
      -- By IH on subtree: eval subtree ≤ eval (complete (depth subtree) n)
      have ih := complete_maximal subtree M c r
      by_cases hactive : active
      · -- Active child: contributes M'.get k' ⊔ pu_k'(M') where M' = eval subtree
        simp only [hactive, ↓reduceIte]
        -- d = max (1 + depth subtree) (depthRvec restChildren)
        -- depth subtree ≤ d - 1 since d ≥ 1 + depth subtree
        have h_depth_bound : depth subtree ≤ max (1 + depth subtree) (depthRvec restChildren) - 1 := by
          have : 1 + depth subtree ≤ max (1 + depth subtree) (depthRvec restChildren) := le_max_left _ _
          omega
        -- eval subtree ≤ eval (complete (depth subtree) n) ≤ eval (complete (d-1) n)
        have h1 : eval subtree M c r ≤ eval (complete (max (1 + depth subtree) (depthRvec restChildren) - 1) n) M c r :=
          Mapping.le_trans ih (complete_eval_depth_mono (depth subtree) _ M c r h_depth_bound)
        -- Now show the value at position k' is bounded
        have h2 : (eval subtree M c r).get ⟨k', by omega⟩ ≤
                  (eval (complete (max (1 + depth subtree) (depthRvec restChildren) - 1) n) M c r).get ⟨k', by omega⟩ :=
          h1 ⟨k', by omega⟩
        have h3 : partial_update ⟨k', by omega⟩ (eval subtree M c r) c r ≤
                  partial_update ⟨k', by omega⟩ (eval (complete (max (1 + depth subtree) (depthRvec restChildren) - 1) n) M c r) c r :=
          partial_update_mono _ _ _ c r h1
        have h_bound : (eval subtree M c r).get ⟨k', by omega⟩ ⊔ partial_update ⟨k', by omega⟩ (eval subtree M c r) c r ≤
                       (eval (complete (max (1 + depth subtree) (depthRvec restChildren) - 1) n) M c r).get ⟨k', by omega⟩ ⊔
                       partial_update ⟨k', by omega⟩ (eval (complete (max (1 + depth subtree) (depthRvec restChildren) - 1) n) M c r) c r :=
          sup_le_sup h2 h3
        -- The complete tree at position k' gives M'.get k' ⊔ pu_k'(M') where M' = eval (complete (d-1) n) M c r
        -- And this equals (eval (complete d n) M c r).get k'
        have h_complete : (eval (complete (max (1 + depth subtree) (depthRvec restChildren)) n) M c r).get ⟨k', by omega⟩ =
            (eval (complete (max (1 + depth subtree) (depthRvec restChildren) - 1) n) M c r).get ⟨k', by omega⟩ ⊔
            partial_update ⟨k', by omega⟩ (eval (complete (max (1 + depth subtree) (depthRvec restChildren) - 1) n) M c r) c r := by
          -- max (1 + depth subtree) (depthRvec restChildren) ≥ 1
          have h_pos : max (1 + depth subtree) (depthRvec restChildren) ≥ 1 := by
            have : 1 + depth subtree ≥ 1 := by omega
            exact le_trans this (le_max_left _ _)
          obtain ⟨d', hd'⟩ : ∃ d', max (1 + depth subtree) (depthRvec restChildren) = d' + 1 := by
            exact Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp h_pos)
          simp only [hd', complete, eval, Nat.add_sub_cancel]
          rw [Rvec.toVector_get, evalRvec_completeRvec]
        rw [h_complete]
        exact h_bound
      · -- Inactive child: contributes M'.get k' where M' = eval subtree
        simp only [hactive]
        -- depth subtree ≤ max (depth subtree) (depthRvec restChildren)
        have h_depth_bound : depth subtree ≤ max (depth subtree) (depthRvec restChildren) := le_max_left _ _
        -- eval subtree ≤ eval (complete (depth subtree) n) ≤ eval (complete d n)
        have h1 : eval subtree M c r ≤ eval (complete (max (depth subtree) (depthRvec restChildren)) n) M c r :=
          Mapping.le_trans ih (complete_eval_depth_mono (depth subtree) _ M c r h_depth_bound)
        exact h1 ⟨k', by omega⟩
    · -- i is in restChildren
      simp only [hi, ↓reduceDIte]
      -- By IH on restChildren
      have h_rest := complete_maximal_rvec k' (by omega) restChildren M c r ⟨i.val, Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp i.isLt) hi⟩
      -- depthRvec restChildren ≤ max ... (depthRvec restChildren)
      have h_depth_le : depthRvec restChildren ≤ max (if active then 1 + depth subtree else depth subtree) (depthRvec restChildren) :=
        le_max_right _ _
      have h_mono := complete_eval_depth_mono (depthRvec restChildren)
        (max (if active then 1 + depth subtree else depth subtree) (depthRvec restChildren)) M c r h_depth_le
      exact le_trans h_rest (h_mono ⟨i.val, by omega⟩)
end

end UpdateTree

/-- After n iterations, update reaches a fixed point. -/
theorem iterate_stabilizes [HeytingAlgebra α] (M : Mapping α n) (c : α) (r : RightExpr α n) :
    iterate (n + 1) M c r = iterate n M c r := by
  -- Proof strategy:
  -- 1. iterate (n+1) M = eval (complete (n+1) n) M  [by complete_eq_iterate]
  -- 2. eval (pruned (n+1) n) M ≥ eval (complete (n+1) n) M  [by pruned_eval_ge]
  -- 3. depth (pruned (n+1) n) ≤ n  [by pruned_depth_le]
  -- 4. eval (pruned (n+1) n) M ≤ eval (complete n n) M  [by complete_maximal + monotonicity]
  -- 5. iterate n M = eval (complete n n) M  [by complete_eq_iterate]
  -- 6. Therefore iterate (n+1) M ≤ iterate n M
  -- 7. But iterate is monotone: iterate n M ≤ iterate (n+1) M
  -- 8. Therefore iterate (n+1) M = iterate n M

  -- Step 1: iterate (n+1) M = eval (complete (n+1) n) M
  have step1 : iterate (n + 1) M c r = UpdateTree.eval (UpdateTree.complete (n + 1) n) M c r :=
    (UpdateTree.complete_eq_iterate (n + 1) M c r).symm

  -- Step 2: eval (pruned (n+1) n) M ≥ eval (complete (n+1) n) M
  have step2 : UpdateTree.eval (UpdateTree.pruned (n + 1) n) M c r ≥
               UpdateTree.eval (UpdateTree.complete (n + 1) n) M c r :=
    UpdateTree.pruned_eval_ge (n + 1) M c r

  -- Step 3: depth (pruned (n+1) n) ≤ n
  have step3 : UpdateTree.depth (UpdateTree.pruned (n + 1) n) ≤ n :=
    UpdateTree.pruned_depth_le (n + 1)

  -- Step 4: By complete_maximal, eval (pruned (n+1) n) M ≤ eval (complete (depth (pruned ...)) n) M
  have step4a : UpdateTree.eval (UpdateTree.pruned (n + 1) n) M c r ≤
                UpdateTree.eval (UpdateTree.complete (UpdateTree.depth (UpdateTree.pruned (n + 1) n)) n) M c r :=
    UpdateTree.complete_maximal (UpdateTree.pruned (n + 1) n) M c r

  -- Step 4b: Since depth (pruned (n+1) n) ≤ n, we have eval (complete (depth ...) n) M ≤ eval (complete n n) M
  -- This follows from complete_eq_iterate and iterate_le_of_le
  have step4b : UpdateTree.eval (UpdateTree.complete (UpdateTree.depth (UpdateTree.pruned (n + 1) n)) n) M c r ≤
                UpdateTree.eval (UpdateTree.complete n n) M c r := by
    rw [UpdateTree.complete_eq_iterate, UpdateTree.complete_eq_iterate]
    exact iterate_le_of_le M c r step3

  -- Step 5: iterate n M = eval (complete n n) M
  have step5 : iterate n M c r = UpdateTree.eval (UpdateTree.complete n n) M c r :=
    (UpdateTree.complete_eq_iterate n M c r).symm

  -- Step 6: Combine to get iterate (n+1) M ≤ iterate n M
  have step6 : iterate (n + 1) M c r ≤ iterate n M c r := by
    intro x
    calc (iterate (n + 1) M c r).get x
        = (UpdateTree.eval (UpdateTree.complete (n + 1) n) M c r).get x := by rw [step1]
      _ ≤ (UpdateTree.eval (UpdateTree.pruned (n + 1) n) M c r).get x := step2 x
      _ ≤ (UpdateTree.eval (UpdateTree.complete (UpdateTree.depth (UpdateTree.pruned (n + 1) n)) n) M c r).get x := step4a x
      _ ≤ (UpdateTree.eval (UpdateTree.complete n n) M c r).get x := step4b x
      _ = (iterate n M c r).get x := by rw [step5]

  -- Step 7: But also iterate n M ≤ iterate (n+1) M
  have step7 : iterate n M c r ≤ iterate (n + 1) M c r :=
    iterate_step_le n M c r

  -- Step 8: Therefore iterate (n+1) M = iterate n M
  apply Vector.ext
  intro x hx
  have h1 : (iterate (n + 1) M c r).get ⟨x, hx⟩ ≤ (iterate n M c r).get ⟨x, hx⟩ := step6 ⟨x, hx⟩
  have h2 : (iterate n M c r).get ⟨x, hx⟩ ≤ (iterate (n + 1) M c r).get ⟨x, hx⟩ := step7 ⟨x, hx⟩
  exact le_antisymm h1 h2

/-- Optimized iteration that detects fixed points early.
    Like iterate, but stops early if a fixed point is detected. -/
def iterate_opt [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (k : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n) : Mapping α n :=
  match k with
  | 0 => M  -- Out of steps, return current mapping
  | k' + 1 =>
    let M' := update M c r
    if M' ≤ M then
      M  -- Fixpoint reached
    else
      iterate_opt k' M' c r

/-- iterate_opt gives the same result as iterate when both reach completion. -/
theorem iterate_opt_eq_iterate [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (k : Nat) (M : Mapping α n) (c : α) (r : RightExpr α n) :
    iterate_opt k M c r = iterate k M c r := by
  -- iterate_opt may terminate early if it detects a fixed point,
  -- but when it does, the result is the same as continuing to iterate
  -- because we've reached a fixed point
  induction k generalizing M with
  | zero =>
    -- Base case: both return M
    rfl
  | succ k' ih =>
    simp only [iterate_opt, iterate]
    by_cases h : update M c r ≤ M
    · -- Case: fixed point detected, iterate_opt returns M
      simp [h]
      -- We need to show: M = update (iterate k' M c r) c r
      -- Since update M c r ≤ M and M ≤ update M c r (by update_le), we have update M c r = M
      have h_eq : update M c r = M := by
        apply Vector.ext
        intro i hi
        have h1 : (update M c r).get ⟨i, hi⟩ ≤ M.get ⟨i, hi⟩ := h ⟨i, hi⟩
        have h2 : M.get ⟨i, hi⟩ ≤ (update M c r).get ⟨i, hi⟩ := update_le r M c ⟨i, hi⟩
        exact le_antisymm h1 h2
      -- iterate k' M c r = M (because M is a fixed point)
      rw [iterate_fixpoint k' M c r h_eq, h_eq]
    · -- Case: not a fixed point, continue iterating
      simp [h]
      -- Use commutativity and IH
      rw [ih (update M c r), iterate_update_comm]

/-- The horn-clause solver: computes a minimal environment for a right expression.
    Starts from the bottom mapping (all variables ⊥) and iterates up to n times. -/
def hornSolve [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (c : α) (r : RightExpr α n) : Mapping α n :=
  iterate_opt n (Mapping.const α n ⊥) c r

/-- hornSolve c r is a fixed point of update c r. -/
theorem hornSolve_fixpoint [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (c : α) (r : RightExpr α n) :
    update (hornSolve c r) c r = hornSolve c r := by
  unfold hornSolve
  -- Proof strategy:
  -- 1. iterate_opt n ⊥ = iterate n ⊥ (by iterate_opt_eq_iterate)
  -- 2. iterate (n+1) ⊥ = iterate n ⊥ (by iterate_stabilizes)
  -- 3. This means update (iterate n ⊥) = iterate n ⊥
  rw [iterate_opt_eq_iterate]
  have h_stab := iterate_stabilizes (Mapping.const α n ⊥) c r
  simp only [iterate] at h_stab
  exact h_stab

/-- hornSolve c r is the least fixed point of update c r. -/
theorem hornSolve_least_fixpoint [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (c : α) (r : RightExpr α n) (M : Mapping α n) :
    update M c r = M → hornSolve c r ≤ M := by
  intro hfp
  unfold hornSolve
  -- Proof strategy:
  -- 1. iterate_opt n ⊥ = iterate n ⊥ (by iterate_opt_eq_iterate)
  -- 2. iterate n ⊥ ≤ M (by iterate_least)
  rw [iterate_opt_eq_iterate]
  have h_bot_le : Mapping.const α n ⊥ ≤ M := by
    intro x
    simp [Mapping.get_const]
  exact iterate_least n M c r (Mapping.const α n ⊥) h_bot_le hfp

/-- Sufficiency theorem: if there exists M with eval M r ≥ e,
    then hornSolve e r also achieves e. -/
theorem hornSolve_sufficient [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (r : RightExpr α n) (e : α) :
    (∃ M, eval M r ≥ e) → eval (hornSolve e r) r ≥ e := by
  intro ⟨M, hM⟩
  -- Apply the general strategy: fixed point + const sufficiency
  apply fixpoint_and_consts_sufficient r (hornSolve e r) e
  · -- Fixed point property: hornSolve e r is a fixed point of update _ e r
    exact hornSolve_fixpoint e r
  · -- Const sufficiency: eval_for_consts (hornSolve e r) r ≥ e
    -- First, show that M satisfies const sufficiency
    have hconst_M : eval_for_consts M r ≥ e :=
      calc eval_for_consts M r
          ≥ eval M r := eval_le_eval_for_consts r M
        _ ≥ e := hM
    -- M is a fixed point of update _ e r (by update_fixpoint)
    have hfp_M : update M e r = M := update_fixpoint r M e hM
    -- hornSolve e r is the least fixed point, so hornSolve e r ≤ M
    have hle : hornSolve e r ≤ M := hornSolve_least_fixpoint e r M hfp_M
    -- By antitonicity of eval_for_consts
    have hantitone : eval_for_consts M r ≤ eval_for_consts (hornSolve e r) r :=
      eval_for_consts_antitone r (hornSolve e r) M hle
    -- Therefore: e ≤ eval_for_consts M r ≤ eval_for_consts (hornSolve e r) r
    calc e ≤ eval_for_consts M r := hconst_M
         _ ≤ eval_for_consts (hornSolve e r) r := hantitone

/-- If M(r) ≥ e, then M ≥ hornSolve e r.
    This shows that hornSolve e r is minimal among all environments satisfying r ≥ e. -/
theorem hornSolve_minimal [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (r : RightExpr α n) (M : Mapping α n) (e : α) :
    eval M r ≥ e → M ≥ hornSolve e r := by
  intro h
  -- By update_fixpoint, M is a fixed point of update e r
  have hfp : update M e r = M := update_fixpoint r M e h
  -- Since M is a fixed point of update e r, and hornSolve e r is the least such fixed point,
  -- we have hornSolve e r ≤ M
  exact hornSolve_least_fixpoint e r M hfp

/-- Key property: hornSolve c r ⊓ const(d) = hornSolve (c ⊓ d) r.
    This shows that capping the result is the same as using a smaller constant. -/
theorem hornSolve_inf_const [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (c d : α) (r : RightExpr α n) :
    hornSolve c r ⊓ Mapping.const α n d = hornSolve (c ⊓ d) r := by
  unfold hornSolve
  -- Use iterate_inf_const, then convert back to iterate_opt via iterate_opt_eq_iterate
  have h := iterate_inf_const n c d r (Mapping.const α n ⊥)
  rw [← iterate_opt_eq_iterate, ← iterate_opt_eq_iterate] at h
  -- Need to show: const ⊥ ⊓ const d = const ⊥
  have : Mapping.const α n ⊥ ⊓ Mapping.const α n d = Mapping.const α n ⊥ := by
    apply Vector.ext
    intro i hi
    show (Mapping.const α n ⊥ ⊓ Mapping.const α n d).get ⟨i, hi⟩ = (Mapping.const α n ⊥).get ⟨i, hi⟩
    rw [Mapping.get_inf, Mapping.get_const, Mapping.get_const]
    exact le_antisymm inf_le_left bot_le
  rw [this] at h
  exact h.symm

/-- Lifting lemma: if hornSolve e r achieves e, then hornSolve ⊤ r also achieves e. -/
theorem hornSolve_top_of_e [HeytingAlgebra α] [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (r : RightExpr α n) (e : α) :
    eval (hornSolve e r) r ≥ e → eval (hornSolve ⊤ r) r ≥ e := by
  intro h_e
  -- Key insight: hornSolve e r = hornSolve ⊤ r ⊓ const e (by hornSolve_inf_const)
  have heq : hornSolve e r = hornSolve ⊤ r ⊓ Mapping.const α n e := by
    have h1 : hornSolve e r = hornSolve (⊤ ⊓ e) r := by rw [top_inf_eq e]
    have h2 : hornSolve (⊤ ⊓ e) r = hornSolve ⊤ r ⊓ Mapping.const α n e :=
      (hornSolve_inf_const ⊤ e r).symm
    exact h1.trans h2
  -- Therefore: eval (hornSolve ⊤ r ⊓ const e) r ≥ e
  rw [heq] at h_e
  -- By eval_of_eval_inf_const with c := ⊤: eval (hornSolve ⊤ r) r ≥ ⊤ ⊓ e
  have h_result : eval (hornSolve ⊤ r) r ≥ ⊤ ⊓ e := by
    -- Convert e to ⊤ ⊓ e in h_e
    have h_e' : eval (hornSolve ⊤ r ⊓ Mapping.const α n e) r ≥ ⊤ ⊓ e := by
      rw [top_inf_eq e]; exact h_e
    exact eval_of_eval_inf_const r (hornSolve ⊤ r) ⊤ e h_e'
  -- Simplify ⊤ ⊓ e = e
  rw [top_inf_eq e] at h_result
  exact h_result

end RightExpr

/-! ## Single-Variable Solver

Phase 2 of the algorithm: solve for a single element e such that:
  S(r) ≥ e  ∧  e ≰ (S ⊓ e)(l)
-/

/-- Canonical form for left expressions: meet(join(x, joinConst), meetConst).
    When evaluated with x = e, this is equivalent to evaluating the original
    left expression with environment (S ⊓ Mapping.const α n e). -/
structure LeftCanonical (α : Type u) where
  /-- constant to join with variable -/
  joinConst : α
  /-- constant to meet with result -/
  meetConst : α

namespace LeftCanonical

/-- Evaluate the canonical form with a given value for the variable. -/
def eval [HeytingAlgebra α] (lc : LeftCanonical α) (e : α) : α :=
  (e ⊔ lc.joinConst) ⊓ lc.meetConst

/-- Convert a left expression to canonical form given environment S.
    The resulting canonical form satisfies:
    lc.eval e = LeftExpr.eval (S ⊓ Mapping.const α n e) l -/
def fromLeftExpr [HeytingAlgebra α] (S : Mapping α n) (l : LeftExpr α n) : LeftCanonical α :=
  match l with
  | LeftExpr.var i => { joinConst := ⊥, meetConst := S.get i }
  | LeftExpr.const c => { joinConst := ⊤, meetConst := c }
  | LeftExpr.join l₁ l₂ =>
      let lc₁ := fromLeftExpr S l₁
      let lc₂ := fromLeftExpr S l₂
      { joinConst := (lc₁.joinConst ⊔ lc₂.joinConst) ⊓ (lc₁.joinConst ⊔ lc₂.meetConst) ⊓ (lc₁.meetConst ⊔ lc₂.joinConst),
        meetConst := lc₁.meetConst ⊔ lc₂.meetConst }
  | LeftExpr.meet l₁ l₂ =>
      let lc₁ := fromLeftExpr S l₁
      let lc₂ := fromLeftExpr S l₂
      -- (e ⊔ a₁) ⊓ b₁ ⊓ (e ⊔ a₂) ⊓ b₂
      -- = (e ⊔ (a₁ ⊓ a₂)) ⊓ b₁ ⊓ b₂
      { joinConst := lc₁.joinConst ⊓ lc₂.joinConst, meetConst := lc₁.meetConst ⊓ lc₂.meetConst }

/-- The canonical form preserves the evaluation semantics of the original left expression. -/
theorem fromLeftExpr_correct [HeytingAlgebra α] (S : Mapping α n) (l : LeftExpr α n) (e : α) :
    (fromLeftExpr S l).eval e = LeftExpr.eval (S ⊓ Mapping.const α n e) l := by
  induction l with
  | var i =>
    -- fromLeftExpr gives { joinConst := ⊥, meetConst := S.get i }
    -- eval gives (e ⊔ ⊥) ⊓ S.get i = e ⊓ S.get i
    -- LeftExpr.eval gives (S ⊓ const e).get i = S.get i ⊓ e
    simp [fromLeftExpr, LeftCanonical.eval, LeftExpr.eval]
    rw [inf_comm]
  | const c =>
    -- fromLeftExpr gives { joinConst := ⊤, meetConst := c }
    -- eval gives (e ⊔ ⊤) ⊓ c = ⊤ ⊓ c = c
    -- LeftExpr.eval gives c
    simp [fromLeftExpr, LeftCanonical.eval, LeftExpr.eval]
  | join l₁ l₂ ih₁ ih₂ =>
    -- fromLeftExpr gives:
    --   { joinConst := (a₁ ⊔ a₂) ⊓ (a₁ ⊔ b₂) ⊓ (b₁ ⊔ a₂),
    --     meetConst := b₁ ⊔ b₂ }
    -- Goal: (e ⊔ ((a₁ ⊔ a₂) ⊓ (a₁ ⊔ b₂) ⊓ (b₁ ⊔ a₂))) ⊓ (b₁ ⊔ b₂)
    --     = ((e ⊔ a₁) ⊓ b₁) ⊔ ((e ⊔ a₂) ⊓ b₂)
    simp only [fromLeftExpr, LeftCanonical.eval, LeftExpr.eval]
    rw [←ih₁, ←ih₂]
    simp only [LeftCanonical.eval]
    -- Strategy: Transform RHS to match LHS using distributivity
    -- RHS: ((e ⊔ a₁) ⊓ b₁) ⊔ ((e ⊔ a₂) ⊓ b₂)
    -- LHS: (e ⊔ ((a₁ ⊔ a₂) ⊓ (a₁ ⊔ b₂) ⊓ (b₁ ⊔ a₂))) ⊓ (b₁ ⊔ b₂)
    -- Use the identity: (a ⊓ b) ⊔ (c ⊓ d) = (a ⊔ c) ⊓ (a ⊔ d) ⊓ (b ⊔ c) ⊓ (b ⊔ d)
    -- combined with: (e ⊔ x) ⊓ (e ⊔ y) ⊓ (e ⊔ z) = e ⊔ (x ⊓ y ⊓ z)
    -- The key lattice identity - manual proof using distributivity
    have key : ∀ (e a1 a2 b1 b2 : α),
        ((e ⊔ a1) ⊓ b1) ⊔ ((e ⊔ a2) ⊓ b2) =
        (e ⊔ ((a1 ⊔ a2) ⊓ (a1 ⊔ b2) ⊓ (b1 ⊔ a2))) ⊓ (b1 ⊔ b2) := fun e a1 a2 b1 b2 => by
      -- Step 1: Apply sup_inf_right: (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z)
      rw [sup_inf_right]
      -- Now: ((e ⊔ a1) ⊔ ((e ⊔ a2) ⊓ b2)) ⊓ (b1 ⊔ ((e ⊔ a2) ⊓ b2))
      -- Due to precedence (⊓ binds tighter), this is: ((e ⊔ a1) ⊔ (e ⊔ a2) ⊓ b2) ⊓ (b1 ⊔ (e ⊔ a2) ⊓ b2)
      -- Step 2: Apply sup_inf_left to left side: a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c)
      conv_lhs => arg 1; rw [sup_inf_left]
      -- Now: (((e ⊔ a1) ⊔ (e ⊔ a2)) ⊓ ((e ⊔ a1) ⊔ b2)) ⊓ (b1 ⊔ (e ⊔ a2) ⊓ b2)
      -- Step 3: Apply sup_inf_left to right side
      conv_lhs => arg 2; rw [sup_inf_left]
      -- Now: (((e ⊔ a1) ⊔ (e ⊔ a2)) ⊓ ((e ⊔ a1) ⊔ b2)) ⊓ ((b1 ⊔ (e ⊔ a2)) ⊓ (b1 ⊔ b2))
      -- Step 4: Flatten meets
      rw [inf_assoc, inf_assoc]
      -- Now: ((e ⊔ a1) ⊔ (e ⊔ a2)) ⊓ ((e ⊔ a1) ⊔ b2) ⊓ (b1 ⊔ (e ⊔ a2)) ⊓ (b1 ⊔ b2)
      -- Step 5: Simplify each join using AC
      -- First term: (e ⊔ a1) ⊔ (e ⊔ a2) at position arg 1
      conv_lhs => arg 1; rw [show (e ⊔ a1) ⊔ (e ⊔ a2) = e ⊔ (a1 ⊔ a2) by ac_rfl]
      -- Second term: (e ⊔ a1) ⊔ b2 at position arg 2; arg 1
      conv_lhs => arg 2; arg 1; rw [show (e ⊔ a1) ⊔ b2 = e ⊔ (a1 ⊔ b2) by ac_rfl]
      -- Third term: b1 ⊔ (e ⊔ a2) at position arg 2; arg 2; arg 1
      conv_lhs => arg 2; arg 2; arg 1; rw [show b1 ⊔ (e ⊔ a2) = e ⊔ (b1 ⊔ a2) by ac_rfl]
      -- Now: (e ⊔ (a1 ⊔ a2)) ⊓ ((e ⊔ (a1 ⊔ b2)) ⊓ ((e ⊔ (b1 ⊔ a2)) ⊓ (b1 ⊔ b2)))
      -- Step 6: Factor out e using ←sup_inf_left: (a ⊔ b) ⊓ (a ⊔ c) = a ⊔ (b ⊓ c)
      -- We need to apply this twice, but the meets are right-associated
      -- First, make the first two terms left-associated
      rw [←inf_assoc]
      -- Now: ((e ⊔ (a1 ⊔ a2)) ⊓ (e ⊔ (a1 ⊔ b2))) ⊓ ((e ⊔ (b1 ⊔ a2)) ⊓ (b1 ⊔ b2))
      -- Apply ←sup_inf_left to the first pair
      conv_lhs => arg 1; rw [←sup_inf_left]
      -- Now: (e ⊔ ((a1 ⊔ a2) ⊓ (a1 ⊔ b2))) ⊓ ((e ⊔ (b1 ⊔ a2)) ⊓ (b1 ⊔ b2))
      -- Make this left-associated again to expose the next pair
      rw [←inf_assoc]
      -- Now: ((e ⊔ ((a1 ⊔ a2) ⊓ (a1 ⊔ b2))) ⊓ (e ⊔ (b1 ⊔ a2))) ⊓ (b1 ⊔ b2)
      -- Apply ←sup_inf_left to this pair
      conv_lhs => arg 1; rw [←sup_inf_left]
      -- Now: (e ⊔ (((a1 ⊔ a2) ⊓ (a1 ⊔ b2)) ⊓ (b1 ⊔ a2))) ⊓ (b1 ⊔ b2)
      -- Flatten the inner meets
      conv_lhs => arg 1; arg 2; rw [inf_assoc]
      -- Now: (e ⊔ ((a1 ⊔ a2) ⊓ (a1 ⊔ b2) ⊓ (b1 ⊔ a2))) ⊓ (b1 ⊔ b2)
      -- This matches the target exactly!
    rw [key]
  | meet l₁ l₂ ih₁ ih₂ =>
    -- fromLeftExpr gives { joinConst := lc₁.joinConst ⊓ lc₂.joinConst, meetConst := lc₁.meetConst ⊓ lc₂.meetConst }
    -- eval gives (e ⊔ (a₁ ⊓ a₂)) ⊓ (b₁ ⊓ b₂)
    -- LeftExpr.eval gives LeftExpr.eval env l₁ ⊓ LeftExpr.eval env l₂
    --                   = ((e ⊔ a₁) ⊓ b₁) ⊓ ((e ⊔ a₂) ⊓ b₂) by IH
    simp only [fromLeftExpr, LeftCanonical.eval, LeftExpr.eval]
    -- Now the goal: (e ⊔ (a₁ ⊓ a₂)) ⊓ (b₁ ⊓ b₂) = eval(l₁) ⊓ eval(l₂)
    -- Rewrite the RHS using IH
    rw [←ih₁, ←ih₂]
    -- Unfold eval on LHS of IH equations
    simp only [LeftCanonical.eval]
    -- Now need to prove: (e ⊔ (a₁ ⊓ a₂)) ⊓ (b₁ ⊓ b₂) = ((e ⊔ a₁) ⊓ b₁) ⊓ ((e ⊔ a₂) ⊓ b₂)
    -- Use distributivity: e ⊔ (a₁ ⊓ a₂) = (e ⊔ a₁) ⊓ (e ⊔ a₂)
    rw [sup_inf_left]
    -- Now: ((e ⊔ a₁) ⊓ (e ⊔ a₂)) ⊓ (b₁ ⊓ b₂) = ((e ⊔ a₁) ⊓ b₁) ⊓ ((e ⊔ a₂) ⊓ b₂)
    -- Rearrange using associativity and commutativity
    ac_rfl

end LeftCanonical

namespace Equation

/-- Check if an element e satisfies the single-variable equation given S from Phase 1. -/
def satisfiesSingleVar [HeytingAlgebra α] (S : Mapping α n) (r : RightExpr α n) (l : LeftExpr α n) (e : α) : Prop :=
  RightExpr.eval S r ≥ e ∧ ¬(e ≤ LeftExpr.eval (S ⊓ Mapping.const α n e) l)

/-- Solve the single-variable equation (Phase 2) given S from Phase 1.
    Returns Some e if a solution exists, None otherwise. -/
def solveSingleVar [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    (S : Mapping α n) (r : RightExpr α n) (l : LeftExpr α n) : Option α :=
  -- Convert left expression to canonical form
  let lc := LeftCanonical.fromLeftExpr S l
  -- Evaluate right expression with environment S
  let Sr := RightExpr.eval S r
  -- Check if S(r) ≤ meetConst; if so, no solution exists
  if Sr ≤ lc.meetConst then
    none
  else
    -- S(r) is a solution to the single-variable equation
    some Sr

/-- If solveSingleVar returns some e, then e satisfies the single-variable equation. -/
theorem solveSingleVar_sound [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    (S : Mapping α n) (r : RightExpr α n) (l : LeftExpr α n) (e : α) :
    solveSingleVar S r l = some e → satisfiesSingleVar S r l e := by
  intro h
  simp only [solveSingleVar] at h
  split at h
  case isTrue h_le =>
    -- If Sr ≤ lc.meetConst, then solveSingleVar returns none, contradiction
    contradiction
  case isFalse h_nle =>
    -- If ¬(Sr ≤ lc.meetConst), then solveSingleVar returns some Sr
    injection h with h_eq
    -- So e = Sr
    subst h_eq
    simp only [satisfiesSingleVar]
    constructor
    · -- Prove RightExpr.eval S r ≥ RightExpr.eval S r
      exact le_refl _
    · -- Prove ¬(RightExpr.eval S r ≤ LeftExpr.eval (S ⊓ Mapping.const α n (RightExpr.eval S r)) l)
      let lc := LeftCanonical.fromLeftExpr S l
      let Sr := RightExpr.eval S r
      rw [← LeftCanonical.fromLeftExpr_correct]
      -- Need to show: ¬(Sr ≤ lc.eval Sr)
      -- We know: ¬(Sr ≤ lc.meetConst)
      intro h_contra
      -- lc.eval Sr = (Sr ⊔ lc.joinConst) ⊓ lc.meetConst ≤ lc.meetConst
      have h_le_meet : LeftCanonical.eval lc Sr ≤ lc.meetConst := by
        simp only [LeftCanonical.eval]
        exact inf_le_right
      -- By transitivity: Sr ≤ lc.meetConst
      have : Sr ≤ lc.meetConst := le_trans h_contra h_le_meet
      -- This contradicts h_nle
      exact h_nle this

/-- If there exists e satisfying the single-variable equation, solveSingleVar finds one. -/
theorem solveSingleVar_complete [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    (S : Mapping α n) (r : RightExpr α n) (l : LeftExpr α n) :
    (∃ e, satisfiesSingleVar S r l e) → solveSingleVar S r l ≠ none := by
  intro ⟨e, he⟩ h_none
  -- Extract the two parts of satisfiesSingleVar
  simp only [satisfiesSingleVar] at he
  obtain ⟨h_Sr_ge_e, h_not_le⟩ := he
  -- Unfold solveSingleVar and analyze when it returns none
  simp only [solveSingleVar] at h_none
  split at h_none
  case isFalse =>
    -- If the condition is false, solveSingleVar returns some, not none
    contradiction
  case isTrue h_Sr_le_meet =>
    -- If Sr ≤ lc.meetConst, then solveSingleVar returns none
    -- We'll derive a contradiction
    let lc := LeftCanonical.fromLeftExpr S l
    let Sr := RightExpr.eval S r
    -- Key lemma: ¬(e ≤ LeftExpr.eval (S ⊓ Mapping.const α n e) l) is equivalent to ¬(e ≤ lc.meetConst)
    rw [← LeftCanonical.fromLeftExpr_correct] at h_not_le
    -- Now h_not_le : ¬(e ≤ lc.eval e) = ¬(e ≤ (e ⊔ lc.joinConst) ⊓ lc.meetConst)
    -- Since e ≤ e ⊔ lc.joinConst, this is equivalent to ¬(e ≤ lc.meetConst)
    have h_e_not_le_meet : ¬(e ≤ lc.meetConst) := by
      intro h_e_le_meet
      apply h_not_le
      simp only [LeftCanonical.eval]
      -- Need to show: e ≤ (e ⊔ lc.joinConst) ⊓ lc.meetConst
      -- Since e ≤ e ⊔ lc.joinConst and e ≤ lc.meetConst
      exact le_inf (le_sup_left) h_e_le_meet
    -- From Sr ≥ e and Sr ≤ lc.meetConst, we get e ≤ lc.meetConst
    have h_e_le_meet : e ≤ lc.meetConst := le_trans h_Sr_ge_e h_Sr_le_meet
    -- This contradicts h_e_not_le_meet
    exact h_e_not_le_meet h_e_le_meet

/-- Attempts to find a counterexample to the equation r ≤ l.
    Returns Some env if a counterexample exists, None if the equation is valid. -/
def find_counterexample [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (eq : Equation α n) : Option (Mapping α n) :=
  let S := RightExpr.hornSolve ⊤ eq.right
  match solveSingleVar S eq.right eq.left with
  | none => none
  | some e => some (S ⊓ Mapping.const α n e)

/-- Decides whether the equation r ≤ l is valid.
    Returns true if valid, false if a counterexample exists. -/
def decide [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (eq : Equation α n) : Bool :=
  (find_counterexample eq).isNone

/-! ## Correctness Proofs -/

/-- If find_counterexample returns an environment, that environment is a counterexample
    where r ≰ l. -/
theorem find_counterexample_sound [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (eq : Equation α n) (env : Mapping α n) :
    find_counterexample eq = some env → not_satisfied env eq := by
  intro h
  unfold find_counterexample at h
  simp only at h
  let S := RightExpr.hornSolve ⊤ eq.right
  cases he : solveSingleVar S eq.right eq.left with
  | none =>
    rw [he] at h
    simp at h
  | some e =>
    rw [he] at h
    simp at h
    cases h
    unfold not_satisfied
    have hsv : satisfiesSingleVar S eq.right eq.left e := solveSingleVar_sound S eq.right eq.left e he
    unfold satisfiesSingleVar at hsv
    obtain ⟨hr, hl⟩ := hsv
    intro hcontra
    -- We have: S(r) ≥ e and ¬(e ≤ LeftExpr.eval (S ⊓ Mapping.const α n e) eq.left)
    -- Need to show contradiction with hcontra: r ≤ l
    -- By eval_meet_const_of_ge: since S(r) ≥ e, we have (S ⊓ const e)(r) ≥ e
    have h_right_ge : RightExpr.eval (S ⊓ Mapping.const α n e) eq.right ≥ e := by
      have : RightExpr.eval S eq.right ≥ e ⊓ e := by rw [inf_idem]; exact hr
      have := RightExpr.eval_meet_const_of_ge eq.right S e e this
      rw [inf_idem] at this
      exact this
    -- Chain: e ≤ (S ⊓ const e)(r) ≤ (S ⊓ const e)(l)
    have h_e_le_left : e ≤ LeftExpr.eval (S ⊓ Mapping.const α n e) eq.left :=
      le_trans h_right_ge hcontra
    -- This contradicts hl
    exact hl h_e_le_left

/-- If the equation is not valid (has a counterexample), find_counterexample finds one. -/
theorem find_counterexample_complete [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (eq : Equation α n) :
    not_valid eq → find_counterexample eq ≠ none := by
  intro ⟨env, hsat⟩
  unfold find_counterexample
  simp only
  let S := RightExpr.hornSolve ⊤ eq.right
  by_contra h
  cases he : solveSingleVar S eq.right eq.left with
  | some e =>
    rw [he] at h
    simp at h
  | none =>
    rw [he] at h
    apply solveSingleVar_complete S eq.right eq.left at he
    apply he
    unfold not_satisfied at hsat
    let e := RightExpr.eval env eq.right
    use e
    unfold satisfiesSingleVar
    constructor
    · show RightExpr.eval S eq.right ≥ e
      -- If ∃M such that M(r) ≥ e, then S(r) ≥ e (by sufficiency + lifting)
      have heval : RightExpr.eval env eq.right ≥ e := le_refl e
      have h_e := RightExpr.hornSolve_sufficient eq.right e ⟨env, heval⟩
      exact RightExpr.hornSolve_top_of_e eq.right e h_e
    · intro hcontra
      apply hsat
      calc RightExpr.eval env eq.right
          = e := rfl
        _ ≤ LeftExpr.eval (S ⊓ Mapping.const α n e) eq.left := hcontra
        _ ≤ LeftExpr.eval env eq.left := by
            -- Use hornSolve_minimal: since env(r) ≥ e, we have env ≥ hornSolve e r
            -- Then use hornSolve_inf_const to get env ≥ S ⊓ const(e)
            have hmin : env ≥ S ⊓ Mapping.const α n e := by
              have heval : RightExpr.eval env eq.right ≥ e := le_refl e
              have hmin' := RightExpr.hornSolve_minimal eq.right env e heval
              have heq : RightExpr.hornSolve e eq.right = S ⊓ Mapping.const α n e := by
                have h1 : RightExpr.hornSolve e eq.right = RightExpr.hornSolve (⊤ ⊓ e) eq.right := by
                  rw [top_inf_eq e]
                have h2 : RightExpr.hornSolve (⊤ ⊓ e) eq.right = S ⊓ Mapping.const α n e :=
                  (RightExpr.hornSolve_inf_const ⊤ e eq.right).symm
                exact h1.trans h2
              rw [← heq]; exact hmin'
            -- By monotonicity of left expressions
            exact LeftExpr.eval_mono eq.left hmin

/-- Main correctness theorem: decide returns true iff the equation is valid. -/
theorem decide_correct [HeytingAlgebra α] [DecidableRel (· ≤ · : α → α → Prop)]
    [DecidableRel (· ≤ · : Mapping α n → Mapping α n → Prop)]
    (eq : Equation α n) :
    decide eq = true ↔ valid eq := by
  unfold decide
  simp only [Option.isNone_iff_eq_none]
  constructor
  · intro h env
    by_contra hsat
    have : not_valid eq := ⟨env, hsat⟩
    have := find_counterexample_complete eq this
    contradiction
  · intro hvalid
    by_contra h
    obtain ⟨env, heq⟩ := Option.ne_none_iff_exists.mp h
    have : find_counterexample eq = some env := heq.symm
    have hsat := find_counterexample_sound eq env this
    exact hsat (hvalid env)

end Equation
