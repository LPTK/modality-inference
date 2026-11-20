import ModalityInference.Proofs.ComparisonWindowTerms
import ModalityInference.Proofs.ComparisonWindowLimits
import Mathlib.Order.Monotone.Basic

/-! Positive local observations and the constructor rank needed to represent them.
Paired observations transfer through the same constructor route. Remembering
which profiles can occur over each pair of root labels bounds their stabilization. -/

namespace ModalityInference.ComparisonWindowRank

open ComparisonWindowPumping
open Classical

variable {T A I : Type} [Fintype A] (s : Trees T A I)

private abbrev Bits := Bool × Bool

private abbrev Layer (A : Type) := A × A × Finset Bits

variable (p : Nat → T → T → Finset Bits)

/-- A pair of root labels belongs to a layer with cap `U` when two trees
with those roots realize only observation pairs in `U` at the given rank. -/
private noncomputable def layer (n : Nat) : Finset (Layer A) :=
  Finset.univ.filter fun z => ∃ x y, s.root x = z.1 ∧ s.root y = z.2.1 ∧ p n x y ⊆ z.2.2

@[simp] private theorem mem_layer {n z} :
    z ∈ layer s p n ↔ ∃ x y, s.root x = z.1 ∧ s.root y = z.2.1 ∧ p n x y ⊆ z.2.2 := by
  simp [layer]

/-- There are sixteen sets of pairs of Boolean observations per pair of root labels. -/
def pairBound (labels : Nat) := labels * labels * 16

private theorem layer_card : Fintype.card (Layer A) = pairBound (Fintype.card A) := by
  simp [Layer, Bits, pairBound, mul_assoc]

private def Extend (n m : Nat) := ∀ x y : T, ∃ u v,
  s.root u = s.root x ∧ s.root v = s.root y ∧ p m u v ⊆ p n x y

private theorem extend_iff {n m} : Extend s p n m ↔ layer s p n ⊆ layer s p m :=
  ⟨fun h _ hz =>
    let ⟨x, y, hx, hy, hp⟩ := (mem_layer s p).mp hz
    let ⟨u, v, hu, hv, hq⟩ := h x y
    (mem_layer s p).mpr ⟨u, v, hu.trans hx, hv.trans hy, hq.trans hp⟩,
   fun h x y => (mem_layer s p).mp (h (a := (s.root x, s.root y, p n x y))
     ((mem_layer s p).mpr ⟨x, y, rfl, rfl, Finset.Subset.refl _⟩))⟩

private def Transfer := ∀ {n m : Nat} {x y u v : T},
  s.root x = s.root u → s.root y = s.root v →
  (∀ i, p n (s.child x i) (s.child y i) ⊆ p m (s.child u i) (s.child v i)) →
  p (n+1) x y ⊆ p (m+1) u v

omit [Fintype A] in
private theorem advance (step : Transfer s p) {n m} (h : Extend s p n m) :
    Extend s p (n+1) (m+1) := by
  intro x y
  choose xs ys roots roots' lowers using fun i => h (s.child x i) (s.child y i)
  obtain ⟨u, hu, hxu⟩ := s.paste x xs roots
  obtain ⟨v, hv, hyv⟩ := s.paste y ys roots'
  exact ⟨u, v, hu, hv, step hu hv (hxu ▸ hyv ▸ lowers)⟩

private theorem layer_antitone (inc : ∀ n x y, p n x y ⊆ p (n+1) x y) :
    Antitone (layer s p) :=
  antitone_nat_of_succ_le fun n _ hz =>
    let ⟨x, y, hx, hy, hp⟩ := (mem_layer s p).mp hz
    (mem_layer s p).mpr ⟨x, y, hx, hy, (inc n x y).trans hp⟩

private theorem extend_all (inc : ∀ n x y, p n x y ⊆ p (n+1) x y) (step : Transfer s p)
    (n : Nat) : Extend s p (pairBound (Fintype.card A)) n := by
  let b := pairBound (Fintype.card A)
  let w := layer s p
  let count := fun i => b - (w i).card
  have anti : Antitone w := layer_antitone s p inc
  have bound (i) : (w i).card ≤ b := (Finset.card_le_univ _).trans_eq layer_card
  have mono : Monotone count := fun i j hij => Nat.sub_le_sub_left (Finset.card_le_card (anti hij)) b
  have eqLayer {i j} (hij : i ≤ j) (eq : count i = count j) : w j = w i := by
    apply Finset.eq_of_subset_of_card_le (anti hij)
    have := bound i
    have := bound j
    dsimp [count] at eq
    omega
  have next (i : Nat) (eq : count i = count (i+1)) : count (i+1) = count (i+2) := by
    have same := (eqLayer (Nat.le_succ i) eq).ge
    have forward := (extend_iff s p).mp (advance s p step ((extend_iff s p).mpr same))
    have fixed := Finset.Subset.antisymm forward (anti (Nat.le_succ _))
    exact congrArg (fun layer : Finset (Layer A) => b - layer.card) fixed
  exact (extend_iff s p).mpr ((le_total b n).elim
    (fun h => (eqLayer h (Nat.stabilises_of_monotone mono (fun _ => Nat.sub_le _ _) next h).symm).ge)
    (fun h => anti h))

/-- Graft the stabilized completions below the first `d` levels. The target
rank grows by one per preserved level, independently of the tested rank `n`. -/
private theorem preserve_prefix (inc : ∀ n x y, p n x y ⊆ p (n+1) x y) (step : Transfer s p)
    (d n : Nat) (x y : T) : ∃ u v,
    s.Prefix d x u ∧ s.Prefix d y v ∧ p n u v ⊆ p (pairBound (Fintype.card A) + d) x y := by
  induction d generalizing n x y with
  | zero =>
    obtain ⟨u, v, hu, hv, h⟩ := extend_all s p inc step n x y
    exact ⟨u, v, hu.symm, hv.symm, h⟩
  | succ d ih =>
    cases n with
    | zero =>
      exact ⟨x, y, s.prefix_refl _ x, s.prefix_refl _ y,
        (monotone_nat_of_le_succ (f := fun n => p n x y) (fun n => inc n x y)) (Nat.zero_le _)⟩
    | succ n =>
      choose us vs px py profiles using fun k => ih n (s.child x k) (s.child y k)
      obtain ⟨u, hu, hcs⟩ := s.paste x us (fun k => ((px k).root s).symm)
      obtain ⟨v, hv, hds⟩ := s.paste y vs (fun k => ((py k).root s).symm)
      exact ⟨u, v, ⟨hu.symm, hcs ▸ px⟩, ⟨hv.symm, hds ▸ py⟩,
        step hu hv (hcs ▸ hds ▸ profiles)⟩

section Terms

open ComparisonWindowTerms ComparisonWindowEndpoints ComparisonObserverMachine
  ComparisonRankedBasis ComparisonStructuralLayout

variable (t : Trees T A Constructor) (l : Fields A) (Δ : Bounds)
  (types : List TypeVar) (modes : List ModVar)

omit [Fintype A] in
private theorem profile_inc (n : Nat) (x y : T) :
    profile t l Δ types modes n x y ⊆ profile t l Δ types modes (n+1) x y :=
  fun _ hb =>
    let ⟨a, ha, hr, e⟩ := (mem_profile ..).mp hb
    (mem_profile ..).mpr ⟨a, ha, Nat.le_succ_of_le hr, e⟩

/-- The color respects every order on observations of the supported defined
types, including the constant observations that a positive type must preserve. -/
structure Positive (g : T → Bool) : Prop where
  order : ∀ x y, (∀ a, Allowed Δ types modes a →
    value (l.nodes t) a x ≤ value (l.nodes t) a y) → g x ≤ g y
  boundary : ∀ x b, (∀ a, Allowed Δ types modes a → value (l.nodes t) a x = b) → g x = b

omit [Fintype A] in
private theorem attainable {g : T → Bool} (hg : Positive t l Δ types modes g) (x : T) :
    ∃ a, Allowed Δ types modes a ∧ value (l.nodes t) a x = g x := by
  by_contra! h
  have opposite : ∀ b c : Bool, b ≠ c → b = !c := by decide
  exact (Bool.not_eq_self _).mp (hg.boundary x _ (fun a ha => opposite _ _ (h a ha))).symm

omit [Fintype A] in
private theorem separate {g : T → Bool} (hg : Positive t l Δ types modes g) {x y : T}
    (h : ¬g x ≤ g y) : ∃ a, Allowed Δ types modes a ∧
    value (l.nodes t) a x = true ∧ value (l.nodes t) a y = false := by
  have fail : ¬ ∀ a, Allowed Δ types modes a → value (l.nodes t) a x ≤ value (l.nodes t) a y :=
    fun eq => h (hg.order x y eq)
  have bool : ∀ b c : Bool, (¬b ≤ c) ↔ b = true ∧ c = false := by decide
  simpa only [not_forall, Classical.not_imp, bool, exists_prop] using fail

omit [Fintype A] in
private theorem realize_pair {g : T → Bool} (hg : Positive t l Δ types modes g) (x y : T) :
    ∃ a, Allowed Δ types modes a ∧ pair t l a x y = (g x, g y) := by
  obtain ⟨a, ha, ea⟩ := attainable t l Δ types modes hg x
  obtain ⟨b, hb, eb⟩ := attainable t l Δ types modes hg y
  cases ex : g x <;> cases ey : g y
  · exact ⟨.meet a b, ⟨CompareTy.definedUnder_meet_iff.mpr ⟨ha.1, hb.1⟩, ha.2, hb.2⟩,
      by simp [pair, value, ea, eb, ex, ey]⟩
  · obtain ⟨v, hv, hy, hx⟩ := separate t l Δ types modes hg (x := y) (y := x) (by simp [ex, ey])
    exact ⟨v, hv, Prod.ext hx hy⟩
  · obtain ⟨v, hv, hx, hy⟩ := separate t l Δ types modes hg (x := x) (y := y) (by simp [ex, ey])
    exact ⟨v, hv, Prod.ext hx hy⟩
  · exact ⟨.join a b, ⟨CompareTy.definedUnder_join_iff.mpr ⟨ha.1, hb.1⟩, ha.2, hb.2⟩,
      by simp [pair, value, ea, eb, ex, ey]⟩

private theorem bounded_pairs
    (cluster : ∀ w : Nat → T × T, ∃ x y, ∀ k N, ∃ i ≥ N,
      t.Prefix k x (w i).1 ∧ t.Prefix k y (w i).2)
    {d : Nat} {g : T → Bool} (reads : t.Reads d g) (hg : Positive t l Δ types modes g)
    (x y : T) :
    (g x, g y) ∈ profile t l Δ types modes (pairBound (Fintype.card A) + d) x y := by
  let p := profile t l Δ types modes
  have step : Transfer t p := fun hx hy => profile_transfer t l Δ types modes hx hy
  choose us vs px py sub using fun n => preserve_prefix t p (profile_inc t l Δ types modes) step d n x y
  obtain ⟨u, v, recur⟩ := cluster (fun i => (us i, vs i))
  obtain ⟨a, ha, ea⟩ := realize_pair t l Δ types modes hg u v
  obtain ⟨i, hi, hu, hv⟩ := recur (max d (rank a)) (rank a)
  have color := reads.mono t (Nat.le_max_left d (rank a))
  have obs := (value_reads t l a).mono t (Nat.le_max_right d (rank a))
  obtain ⟨au, av⟩ := Prod.mk.inj ea
  have xeq : g u = g x := (color u _ hu).trans (reads x _ (px i)).symm
  have yeq : g v = g y := (color v _ hv).trans (reads y _ (py i)).symm
  apply sub i
  exact (mem_profile ..).mpr ⟨a, ha, hi, Prod.ext
    ((obs u _ hu).symm.trans (au.trans xeq))
    ((obs v _ hv).symm.trans (av.trans yeq))⟩

end Terms

open ComparisonDefiniteTreeMachines ComparisonWindowTerms ComparisonWindowEndpoints
  ComparisonObserverMachine ComparisonRankedBasis ComparisonStructuralLayout ComparisonWindowObservers

/-- For a local Boolean function, order and constant boundaries are exactly the
conditions for a bounded defined positive image. The additional rank depends
only on the finite label alphabet of the observer presentation. -/
theorem positive_iff_bounded {B : Type} [Fintype B] {r : Nat}
    (ok : Window B Constructor (r+1) → Prop) (l : Fields (Window B Constructor (r+1)))
    (Δ : Bounds) (types : List TypeVar) (modes : List ModVar)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) {d} {g : Closed ok → Bool}
    (reads : (closedTrees ok).Reads d g) :
    Positive (closedTrees ok) l Δ types modes g ↔
      ∃ a, Allowed Δ types modes a ∧ rank a ≤ pairBound (Fintype.card (Window B Constructor (r+1))) + d ∧
        a.WellShaped Δ ∧ ∀ t, value (l.nodes (closedTrees ok)) a t = g t :=
  ⟨fun hg => positive_reify _ _ _ _ _ hn _ g
      (bounded_pairs _ _ _ _ _ (ComparisonWindowLimits.closed_pair_compact ok) reads hg),
   fun ⟨a, ha, _, _, eq⟩ => ⟨
     fun x y rel => eq x ▸ eq y ▸ rel a ha,
     fun x _ all => (eq x).symm.trans (all a ha)⟩⟩

end ModalityInference.ComparisonWindowRank
