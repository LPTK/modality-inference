import ModalityInference.Proofs.ComparisonObserverGenerated
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic

/-! A finite-state bottom-up tree machine forgets arbitrary frontier states after
some depth exactly when it does so after at most the number of state pairs.
Unrolling a forgetting machine gives one shared finite-window function; monotone
transitions and constant fixed points give monotonicity and boundary values.
The final theorem reifies such functions by finite lattice terms. The machine is
an explicit parameter throughout: this criterion does not synthesize a complete
family of machines from comparison constraints. -/
namespace ModalityInference.ComparisonDefiniteTreeMachines

variable {A I Q : Type} [Fintype A] [Fintype I] [Fintype Q]
  [DecidableEq I] [DecidableEq Q]

/-- Advance pairs of states over the same input symbol and paired child states. -/
def next (step : A → (I → Q) → Q) (r : Finset (Q × Q)) : Finset (Q × Q) :=
  Finset.univ.filter fun p =>
    ∃ a x y, (∀ i, (x i, y i) ∈ r) ∧ p.1 = step a x ∧ p.2 = step a y

/-- State ambiguity after a common input prefix of the given depth. -/
def pairs (step : A → (I → Q) → Q) : Nat → Finset (Q × Q)
  | 0 => Finset.univ
  | n + 1 => next step (pairs step n)

theorem next_mono (step : A → (I → Q) → Q) : Monotone (next step) := by
  intro r s hrs p hp
  simp only [next, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  obtain ⟨a, x, y, hxy, hp, hq⟩ := hp
  exact ⟨a, x, y, fun i => hrs (hxy i), hp, hq⟩

theorem pairs_step (step : A → (I → Q) → Q) (n : Nat) :
    pairs step (n + 1) ⊆ pairs step n := by
  induction n with
  | zero => exact Finset.subset_univ _
  | succ n ih => exact next_mono step ih

theorem pairs_antitone (step : A → (I → Q) → Q) : Antitone (pairs step) := by
  exact antitone_nat_of_succ_le (pairs_step step)

theorem pairs_fixed (step : A → (I → Q) → Q) :
    pairs step (Fintype.card (Q × Q) + 1) = pairs step (Fintype.card (Q × Q)) := by
  let size := Fintype.card (Q × Q)
  let count := fun n => size - (pairs step n).card
  have hsize : ∀ n, (pairs step n).card ≤ size := fun _ => Finset.card_le_univ _
  have hmono : Monotone count := by
    intro m n hmn
    exact Nat.sub_le_sub_left (Finset.card_le_card (pairs_antitone step hmn)) size
  have hbound : ∀ n, count n ≤ size := fun _ => Nat.sub_le _ _
  have hstop : ∀ n, count n = count (n + 1) → count (n + 1) = count (n + 2) := by
    intro n h
    have hcard : (pairs step n).card = (pairs step (n + 1)).card := by
      have := hsize n
      have := hsize (n + 1)
      dsimp [count] at h
      omega
    have he : pairs step (n + 1) = pairs step n :=
      Finset.eq_of_subset_of_card_le (pairs_step step n) hcard.le
    have he' : pairs step (n + 2) = pairs step (n + 1) := congrArg (next step) he
    exact congrArg (fun s : Finset (Q × Q) => size - s.card) he'.symm
  have h := Nat.stabilises_of_monotone hmono hbound hstop (Nat.le_succ size)
  have hcard : (pairs step size).card = (pairs step (size + 1)).card := by
    have := hsize size
    have := hsize (size + 1)
    dsimp [count] at h
    omega
  exact Finset.eq_of_subset_of_card_le (pairs_step step size) hcard.le

theorem pairs_stable (step : A → (I → Q) → Q) (n : Nat)
    (hn : Fintype.card (Q × Q) ≤ n) :
    pairs step n = pairs step (Fintype.card (Q × Q)) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    change next step (pairs step n) = _
    rw [ih]
    exact pairs_fixed step

def down (i : I) (x : List I → A) : List I → A := fun p => x (i :: p)

def graft (a : A) (x : I → List I → A) : List I → A
  | [] => a
  | i :: p => x i p

def fold (step : A → (I → Q) → Q) : Nat → (List I → A) → (List I → Q) → Q
  | 0, _, leaf => leaf []
  | n + 1, x, leaf => step (x []) (fun i => fold step n (down i x) (down i leaf))

theorem fold_pair (step : A → (I → Q) → Q) (n : Nat)
    (x : List I → A) (u v : List I → Q) :
    (fold step n x u, fold step n x v) ∈ pairs step n := by
  induction n generalizing x u v with
  | zero => exact Finset.mem_univ _
  | succ n ih =>
    simp only [pairs, next, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨x [], _, _, fun i => ih (down i x) (down i u) (down i v), rfl, rfl⟩

/-- The root result is independent of every state at the frontier. -/
def Forgets (step : A → (I → Q) → Q) (n : Nat) : Prop :=
  ∀ x u v, fold step n x u = fold step n x v

theorem forgets_of_pairs (step : A → (I → Q) → Q) (n : Nat)
    (h : ∀ p ∈ pairs step n, p.1 = p.2) : Forgets step n := by
  intro x u v
  exact h _ (fold_pair step n x u v)

theorem pair_fold [Nonempty A] (step : A → (I → Q) → Q) (n : Nat)
    {p : Q × Q} (hp : p ∈ pairs step n) :
    ∃ x u v, fold step n x u = p.1 ∧ fold step n x v = p.2 := by
  classical
  induction n generalizing p with
  | zero => exact ⟨fun _ => Classical.choice inferInstance, fun _ => p.1,
      fun _ => p.2, rfl, rfl⟩
  | succ n ih =>
    simp only [pairs, next, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨a, left, right, hpair, hp, hq⟩ := hp
    rw [hp, hq]
    choose x u v hu hv using fun i => ih (hpair i)
    refine ⟨graft a x, graft (step a left) u, graft (step a right) v, ?_, ?_⟩
    · change step a (fun i => fold step n (x i) (u i)) = step a left
      exact congrArg (step a) (funext hu)
    · change step a (fun i => fold step n (x i) (v i)) = step a right
      exact congrArg (step a) (funext hv)

theorem forgets_iff_pairs [Nonempty A] (step : A → (I → Q) → Q) (n : Nat) :
    Forgets step n ↔ ∀ p ∈ pairs step n, p.1 = p.2 := by
  constructor
  · intro h p hp
    obtain ⟨x, u, v, hu, hv⟩ := pair_fold step n hp
    exact hu.symm.trans ((h x u v).trans hv)
  · exact forgets_of_pairs step n

/-- An effective stopping bound for a supplied finite machine. -/
theorem forgets_bounded [Nonempty A] (step : A → (I → Q) → Q) :
    (∃ n, Forgets step n) ↔ Forgets step (Fintype.card (Q × Q)) := by
  constructor
  · rintro ⟨n, hn⟩
    apply forgets_of_pairs
    intro p hp
    apply (forgets_iff_pairs step n).mp hn p
    rcases le_total n (Fintype.card (Q × Q)) with h | h
    · exact pairs_antitone step h hp
    · rwa [pairs_stable step n h]
  · exact fun h => ⟨_, h⟩

omit [Fintype A] [Fintype I] [Fintype Q] [DecidableEq I] [DecidableEq Q]

theorem fold_push (step : A → (I → Q) → Q) (n : Nat)
    (x : List I → A) (leaf : List I → Q) :
    fold step (n + 1) x leaf =
      fold step n x (fun p => step (x p) (fun i => leaf (p ++ [i]))) := by
  induction n generalizing x leaf with
  | zero => rfl
  | succ n ih =>
    simp only [fold]
    apply congrArg (step (x []))
    funext i
    change fold step (n + 1) (down i x) (down i leaf) = _
    rw [ih]
    rfl

def solution (step : A → (I → Q) → Q) (n : Nat) (seed : Q)
    (x : List I → A) : Q := fold step n x (fun _ => seed)

theorem solution_step (step : A → (I → Q) → Q) (n : Nat) (seed : Q)
    (hn : Forgets step n) (x : List I → A) :
    solution step n seed x = step (x []) (fun i => solution step n seed (down i x)) := by
  change fold step n x (fun _ => seed) = fold step (n + 1) x (fun _ => seed)
  rw [fold_push]
  exact hn _ _ _

theorem fold_prefix (step : A → (I → Q) → Q) (n : Nat)
    (x y : List I → A) (leaf : List I → Q)
    (h : ∀ p, p.length < n → x p = y p) : fold step n x leaf = fold step n y leaf := by
  induction n generalizing x y leaf with
  | zero => rfl
  | succ n ih =>
    simp only [fold]
    rw [h [] (by simp)]
    apply congrArg (step (y []))
    funext i
    apply ih
    intro p hp
    exact h (i :: p) (by simpa using Nat.succ_lt_succ hp)

theorem solution_prefix (step : A → (I → Q) → Q) (n : Nat) (seed : Q)
    (x y : List I → A) (h : ∀ p, p.length < n → x p = y p) :
    solution step n seed x = solution step n seed y := fold_prefix step n x y _ h

theorem fold_mono [Preorder A] [Preorder Q] (step : A → (I → Q) → Q)
    (hs : ∀ a b, a ≤ b → ∀ u v, (∀ i, u i ≤ v i) → step a u ≤ step b v)
    (n : Nat) (x y : List I → A) (u v : List I → Q)
    (hxy : ∀ p, x p ≤ y p) (huv : ∀ p, u p ≤ v p) :
    fold step n x u ≤ fold step n y v := by
  induction n generalizing x y u v with
  | zero => exact huv []
  | succ n ih => exact hs _ _ (hxy []) _ _ (fun i =>
      ih (down i x) (down i y) (down i u) (down i v)
        (fun p => hxy (i :: p)) (fun p => huv (i :: p)))

theorem solution_mono [Preorder A] [Preorder Q] (step : A → (I → Q) → Q)
    (hs : ∀ a b, a ≤ b → ∀ u v, (∀ i, u i ≤ v i) → step a u ≤ step b v)
    (n : Nat) (seed : Q) : Monotone (solution step n seed) := by
  intro x y hxy
  exact fold_mono step hs n x y _ _ hxy (fun _ => le_rfl)

theorem fold_constant (step : A → (I → Q) → Q) (a : A) (q : Q)
    (hs : step a (fun _ => q) = q) (n : Nat) :
    fold step n (fun _ => a) (fun _ => q) = q := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step a (fun _ => fold step n (fun _ => a) (fun _ => q)) = q
    rw [ih]
    exact hs

theorem solution_constant (step : A → (I → Q) → Q) (a : A) (q : Q)
    (hs : step a (fun _ => q) = q) (n : Nat) (seed : Q) (hn : Forgets step n) :
    solution step n seed (fun _ => a) = q := by
  exact (hn _ (fun _ => seed) (fun _ => q)).trans (fold_constant step a q hs n)

/-- A local transition certificate yields the same solution at every route. -/
theorem solution_satisfies (step : A → (I → Q) → Q) (n : Nat) (seed : Q)
    (hn : Forgets step n) (R : A → Q → (I → Q) → Prop)
    (hs : ∀ a child, R a (step a child) child) (x : List I → A) :
    R (x []) (solution step n seed x) (fun i => solution step n seed (down i x)) := by
  rw [solution_step step n seed hn x]
  exact hs _ _

theorem fold_prefix_mono [Preorder A] [Preorder Q] (step : A → (I → Q) → Q)
    (hs : ∀ a b, a ≤ b → ∀ u v, (∀ i, u i ≤ v i) → step a u ≤ step b v)
    (n : Nat) (x y : List I → A) (u v : List I → Q)
    (hxy : ∀ p, p.length < n → x p ≤ y p) (huv : ∀ p, u p ≤ v p) :
    fold step n x u ≤ fold step n y v := by
  induction n generalizing x y u v with
  | zero => exact huv []
  | succ n ih =>
    apply hs _ _ (hxy [] (by simp))
    intro i
    apply ih (down i x) (down i y) (down i u) (down i v)
    · intro p hp
      exact hxy (i :: p) (by simpa using Nat.succ_lt_succ hp)
    · exact fun p => huv (i :: p)

/-- Shared monotone outputs with both constant boundaries have finite lattice
realizations over the atoms in their finite window. -/
theorem finite_reify {J K L : Type} [Lattice L]
    (step : (J → Bool) → (I → K → Bool) → K → Bool)
    (hs : ∀ a b, a ≤ b → ∀ u v, (∀ i, u i ≤ v i) → step a u ≤ step b v)
    (hz : step (fun _ => false) (fun _ _ => false) = fun _ => false)
    (ho : step (fun _ => true) (fun _ _ => true) = fun _ => true)
    (n : Nat) (seed : K → Bool) (hn : Forgets step n)
    (atoms : List I → J → L) (p : Finset L)
    (hp : ∀ path, path.length < n → ∀ j, atoms path j ∈ p) :
    ∃ terms : K → L,
      (∀ k, ComparisonObserverChains.LatticeGenerated p (terms k)) ∧
      ∀ (f : LatticeHom L Bool) k,
        f (terms k) = solution step n seed (fun path j => f (atoms path j)) k := by
  classical
  have ht (k : K) : ∃ t : L,
      ComparisonObserverChains.LatticeGenerated p t ∧
      ∀ f : LatticeHom L Bool,
        f t = solution step n seed (fun path j => f (atoms path j)) k := by
    apply ComparisonObserverChains.finite_reify_property p
      (fun f => solution step n seed (fun path j => f (atoms path j)) k)
      ?_ ?_ ?_ (ComparisonObserverChains.LatticeGenerated p)
      (fun _ => .atom) (fun _ _ => .sup) (fun _ _ => .inf)
    · intro f g hfg
      exact fold_prefix_mono step hs n _ _ _ _
        (fun path hpath j => hfg _ (hp path hpath j)) (fun _ _ => le_rfl) k
    · exact congrFun (solution_constant step (fun _ => false) (fun _ => false) hz n seed hn) k
    · exact congrFun (solution_constant step (fun _ => true) (fun _ => true) ho n seed hn) k
  choose terms hg hv using ht
  exact ⟨terms, hg, fun f k => hv k f⟩

end ModalityInference.ComparisonDefiniteTreeMachines
