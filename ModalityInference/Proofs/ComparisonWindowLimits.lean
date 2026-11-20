import ModalityInference.Proofs.ComparisonWindowObservers

/-! Every sequence of paired closed observer trees has a recurrent limit pair.
Only the prefix alphabet is finite. The root legality predicate is arbitrary. -/
namespace ModalityInference.ComparisonWindowLimits

open ComparisonDefiniteTreeMachines ComparisonWindowObservers ComparisonStructuralLayout

variable {A I : Type}

private def Often (P : Nat → Prop) := ∀ N, ∃ i ≥ N, P i

private theorem often_fiber {B : Type} [Fintype B] {P : Nat → Prop} (h : Often P)
    (f : Nat → B) : ∃ b, Often (fun i => P i ∧ f i = b) := by
  classical
  by_contra hnone
  simp only [Often, not_exists, not_forall] at hnone
  choose cut hcut using hnone
  obtain ⟨i,hi,hP⟩ := h (Finset.univ.sup cut)
  exact hcut (f i) i ⟨(Finset.le_sup (f := cut) (Finset.mem_univ (f i))).trans hi, hP, rfl⟩

private structure Bucket where
  holds : Nat → Prop
  often : Often holds

private noncomputable def Bucket.next {B : Type} [Fintype B] (p : Bucket) (f : Nat → B) : Bucket :=
  let hb := often_fiber p.often f
  ⟨fun i => p.holds i ∧ f i = hb.choose, hb.choose_spec⟩

private noncomputable def stages {B : Nat → Type} [∀ n, Fintype (B n)]
    (f : (n : Nat) → Nat → B n) : Nat → Bucket
  | 0 => ⟨fun _ => True, fun N => ⟨N, le_rfl, trivial⟩⟩
  | n+1 => (stages f n).next (f n)

private theorem stages_mono {B : Nat → Type} [∀ n, Fintype (B n)]
    (f : (n : Nat) → Nat → B n) {n m : Nat} (h : n ≤ m) (i : Nat) :
    (stages f m).holds i → (stages f n).holds i := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun hi => ih hi.1

private theorem stages_same {B : Nat → Type} [∀ n, Fintype (B n)]
    (f : (n : Nat) → Nat → B n) {n i j} (hi : (stages f (n+1)).holds i)
    (hj : (stages f (n+1)).holds j) : f n i = f n j := hi.2.trans hj.2.symm

private theorem capture_at {n : Nat} {x y : Raw A I}
    (h : Window.capture n x = Window.capture n y) (p : List I) (hp : p.length < n) :
    x p = y p := by
  induction n generalizing x y p with
  | zero => omega
  | succ n ih =>
    cases p with
    | nil => exact congrArg Prod.fst h
    | cons i p =>
      exact ih (congrFun (congrArg Prod.snd h) i) p (by simpa using hp)

private theorem capture_of_at (n : Nat) {x y : Raw A I} (h : ∀ p, p.length < n → x p = y p) :
    Window.capture n x = Window.capture n y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext (h [] (by simp))
    exact funext fun i => ih (fun p hp => h (i :: p) (by simpa using hp))

private theorem raw_recurrent [Fintype A] [Fintype I] [DecidableEq I] (xs : Nat → Raw A I) :
    ∃ x : Raw A I, ∀ d N, ∃ i ≥ N, ∀ p, p.length ≤ d → x p = xs i p := by
  classical
  let f (k i : Nat) := Window.capture (k+1) (xs i)
  have ne (d : Nat) : ∃ i, (stages f (d+1)).holds i := by
    obtain ⟨i, _, hi⟩ := (stages f (d+1)).often 0
    exact ⟨i, hi⟩
  choose idx hi using ne
  refine ⟨fun p => xs (idx p.length) p, fun d N => ?_⟩
  obtain ⟨i, hN, hdi⟩ := (stages f (d+1)).often N
  refine ⟨i, hN, fun p hp => ?_⟩
  exact capture_at (stages_same f (hi p.length)
    (stages_mono f (Nat.succ_le_succ hp) i hdi)) p (Nat.lt_succ_self _)

private theorem legal {n : Nat} {ok : Window A I (n+1) → Prop}
    (x : Raw A I) (xs : Nat → Closed ok)
    (h : ∀ d, ∃ i, ∀ p, p.length ≤ d → x p = (xs i).val p) :
    ∀ p, ok (Window.capture (n+1) (sub x p)) := by
  intro p
  obtain ⟨i,hi⟩ := h (p.length + n)
  have hg : Window.capture (n+1) (sub x p) = Window.capture (n+1) (sub (xs i).val p) :=
    capture_of_at _ fun q hq => hi (p ++ q) (by simp; omega)
  exact hg ▸ (xs i).property p

private theorem closed_prefix {n : Nat} {ok : Window A I (n+1) → Prop}
    (k : Nat) (x y : Closed ok) (h : ∀ p, p.length ≤ k+n → x.val p = y.val p) :
    (closedTrees ok).Prefix k x y := by
  induction k generalizing x y with
  | zero => exact capture_of_at _ fun p hp => h p (by omega)
  | succ k ih =>
    refine ⟨capture_of_at _ (fun p hp => h p (by omega)), fun i => ih _ _ ?_⟩
    intro p hp
    exact h (i :: p) (by simp only [List.length_cons]; omega)

theorem closed_pair_compact [Fintype A] {n : Nat} (ok : Window A Constructor (n+1) → Prop)
    (xy : Nat → Closed ok × Closed ok) :
    ∃ x y : Closed ok, ∀ k N, ∃ i ≥ N,
      (closedTrees ok).Prefix k x (xy i).1 ∧ (closedTrees ok).Prefix k y (xy i).2 := by
  let z (i : Nat) (p : List Constructor) := ((xy i).1.val p, (xy i).2.val p)
  obtain ⟨lim, hl⟩ := raw_recurrent z
  let x : Closed ok := ⟨fun p => (lim p).1, legal _ (fun i => (xy i).1) (fun d => by
    obtain ⟨i, _, hi⟩ := hl d 0
    exact ⟨i, fun p hp => congrArg Prod.fst (hi p hp)⟩)⟩
  let y : Closed ok := ⟨fun p => (lim p).2, legal _ (fun i => (xy i).2) (fun d => by
    obtain ⟨i, _, hi⟩ := hl d 0
    exact ⟨i, fun p hp => congrArg Prod.snd (hi p hp)⟩)⟩
  refine ⟨x, y, fun k N => ?_⟩
  obtain ⟨i, hN, hi⟩ := hl (k+n) N
  exact ⟨i, hN, closed_prefix k x (xy i).1 (fun p hp => congrArg Prod.fst (hi p hp)),
    closed_prefix k y (xy i).2 (fun p hp => congrArg Prod.snd (hi p hp))⟩

end ModalityInference.ComparisonWindowLimits
