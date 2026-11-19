import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-! Compress finite observation windows for guarded binary constraints on trees.
A prefix retains the possible joint outputs of its completions. Layers with
the same families of possible outputs can be spliced. An odd cycle of layers
gives a uniform local solution by coordinatewise majority. -/
namespace ModalityInference.ComparisonWindowPumping

/-- The root label includes the finite boundary on which independent successor
trees must agree before they can be pasted below the root. -/
structure Trees (T A I : Type) where
  root : T → A
  child : T → I → T
  paste : ∀ t cs, (∀ i, root (cs i) = root (child t i)) →
    ∃ u, root u = root t ∧ child u = cs

namespace Trees

open Classical

variable {T A I Q : Type} (s : Trees T A I)

def Prefix : Nat → T → T → Prop
  | 0, x, y => s.root x = s.root y
  | n + 1, x, y => s.root x = s.root y ∧ ∀ i, Prefix n (s.child x i) (s.child y i)

def Reads (n : Nat) (f : T → Q) : Prop := ∀ x y, s.Prefix n x y → f x = f y

theorem Prefix.root {n x y} (h : s.Prefix n x y) : s.root x = s.root y :=
  match n, h with
  | 0, h => h
  | _ + 1, h => h.1

theorem prefix_refl (n : Nat) (t : T) : s.Prefix n t t :=
  match n with
  | 0 => rfl
  | n + 1 => ⟨rfl, fun i => prefix_refl n (s.child t i)⟩

theorem prefix_trim (n : Nat) {x y} (h : s.Prefix (n+1) x y) : s.Prefix n x y :=
  match n, h with
  | 0, h => h.1
  | n+1, h => ⟨h.1, fun i => prefix_trim n (h.2 i)⟩

theorem Reads.mono {n m} {f : T → Q} (h : s.Reads n f) (hnm : n ≤ m) : s.Reads m f := by
  induction hnm with
  | refl => exact h
  | step h ih => exact fun _ _ he => ih _ _ (s.prefix_trim _ he)

abbrev Family (A Q : Type) := A → Finset (Finset Q)

/-- A layer transition chooses one parent menu for the observed child menus.
It must allow every combination of one joint output from each child. -/
def Step (R : A → Q → (I → Q) → Prop) (F G : Family A Q) : Prop :=
  ∀ t : T, ∀ m : I → Finset Q, (∀ i, m i ∈ F (s.root (s.child t i))) →
    ∃ p ∈ G (s.root t), ∀ v : I → Q, (∀ i, v i ∈ m i) → ∃ b ∈ p, R (s.root t) b v

noncomputable def menu [Fintype Q] (f : T → Q) (n : Nat) (t : T) : Finset Q :=
  Finset.univ.filter (fun b => ∃ u, s.Prefix n t u ∧ f u = b)

noncomputable def family [Fintype Q] (f : T → Q) (n : Nat) : Family A Q := fun a =>
  Finset.univ.filter (fun m => ∃ t, s.root t = a ∧ s.menu f n t = m)

@[simp] theorem mem_menu [Fintype Q] {f : T → Q} {n t b} :
    b ∈ s.menu f n t ↔ ∃ u, s.Prefix n t u ∧ f u = b := by simp [menu]

@[simp] theorem mem_family [Fintype Q] {f : T → Q} {n a m} :
    m ∈ s.family f n a ↔ ∃ t, s.root t = a ∧ s.menu f n t = m := by simp [family]

theorem family_step [Fintype Q] {R : A → Q → (I → Q) → Prop} (f : T → Q)
    (hf : ∀ t, R (s.root t) (f t) (fun i => f (s.child t i))) (n : Nat) :
    s.Step R (s.family f n) (s.family f (n+1)) := fun t m hm => by
  choose cs hroot hmenu using fun i => (s.mem_family.mp (hm i))
  obtain ⟨u, hu, hcs⟩ := s.paste t cs hroot
  refine ⟨_, s.mem_family.mpr ⟨u, hu, rfl⟩, fun v hv => ?_⟩
  choose ds hp hd using fun i => s.mem_menu.mp (hmenu i ▸ hv i : v i ∈ s.menu f n (cs i))
  obtain ⟨z, hz, hds⟩ := s.paste t ds (fun i => ((hp i).root s).symm.trans (hroot i))
  refine ⟨f z, s.mem_menu.mpr ⟨z, ⟨hu.trans hz.symm, hcs ▸ hds ▸ hp⟩, rfl⟩, ?_⟩
  simpa only [hz, hds, hd] using hf z


private inductive Path {V : Type} (r : V → V → Prop) : V → List V → V → Prop where
  | nil (v) : Path r v [] v
  | cons {x y rest z} : r x y → Path r y rest z → Path r x (y :: rest) z

private theorem Path.snoc {V} {r : V → V → Prop} {x xs y z}
    (h : Path r x xs y) (e : r y z) : Path r x (xs ++ [z]) z :=
  match h with
  | .nil _ => .cons e (.nil _)
  | .cons edge tail => .cons edge (tail.snoc e)

private theorem Path.suffix {V} {r : V → V → Prop} {x pre y post z}
    (h : Path r x (pre ++ y :: post) z) : Path r y post z := by
  induction pre generalizing x with
  | nil => cases h with | cons _ tail => exact tail
  | cons _ _ ih => cases h with | cons _ tail => exact ih tail

private theorem Path.short {V} {r : V → V → Prop} {x xs y}
    (h : Path r x xs y) : ∃ ys, Path r x ys y ∧ ys.Nodup := by
  induction h with
  | nil v => exact ⟨[], .nil v, .nil⟩
  | @cons x z xs y e _ ih =>
    obtain ⟨ys, path, unique⟩ := ih
    by_cases hz : z ∈ ys
    · obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hz
      exact ⟨z :: post, .cons e path.suffix, (List.nodup_append.mp unique).2.1⟩
    · exact ⟨z :: ys, .cons e path, List.nodup_cons.mpr ⟨hz, unique⟩⟩


private theorem Path.odd_short {V} [Fintype V] {r : V → V → Prop} {x xs y}
    (h : Path r x xs y) (loop : r x x) :
    ∃ ys, Path r x ys y ∧ Odd ys.length ∧ ys.length ≤ Fintype.card V + 1 := by
  obtain ⟨ys, hp, hu⟩ := h.short
  have bound := hu.length_le_card
  by_cases ho : Odd ys.length
  · exact ⟨ys, hp, ho, by omega⟩
  · have ne : ys.length ≠ 2 * (ys.length / 2) + 1 := fun eq => ho ⟨_, eq⟩
    exact ⟨x :: ys, .cons loop hp, ⟨ys.length / 2, by simp only [List.length_cons]; omega⟩,
      Nat.succ_le_succ bound⟩


private theorem menu_zero_reads [Fintype Q] (f : T → Q) : s.Reads 0 (s.menu f 0) :=
  fun x y (h : s.root x = s.root y) => Finset.ext fun _ => by simp only [mem_menu, Prefix, h]

private theorem menu_member [Fintype Q] (f : T → Q) (k : Nat) (t : T) :
    s.menu f k t ∈ s.family f k (s.root t) := s.mem_family.mpr ⟨_, rfl, rfl⟩

private theorem inside_seed [Fintype Q] (f : T → Q) {m k t}
    (hm : m ∈ s.family f k (s.root t)) : m ⊆ s.menu f 0 t :=
  let ⟨_, he, hmenu⟩ := s.mem_family.mp hm
  fun _ hb =>
    let ⟨u, hu, eq⟩ := s.mem_menu.mp (hmenu ▸ hb)
    s.mem_menu.mpr ⟨u, he.symm.trans (hu.root s), eq⟩

private theorem seed_loop [Fintype Q] {R : A → Q → (I → Q) → Prop} (f : T → Q)
    (hf : ∀ t, R (s.root t) (f t) (fun i => f (s.child t i))) :
    s.Step R (s.family f 0) (s.family f 0) := fun t ms hm =>
  let ⟨_, hnext, lift⟩ := s.family_step f hf 0 t ms hm
  ⟨_, s.menu_member f 0 t, fun v hv =>
    let ⟨b, hb, ok⟩ := lift v hv
    ⟨b, s.inside_seed f hnext hb, ok⟩⟩

private theorem terminal [Fintype Q] {f : T → Q} {n} (hf : s.Reads n f)
    {t m} (hm : m ∈ s.family f n (s.root t)) :
    ∃ b ∈ s.menu f 0 t, m = {b} :=
  let ⟨x, he, hmenu⟩ := s.mem_family.mp hm
  ⟨f x, s.mem_menu.mpr ⟨x, he.symm, rfl⟩, hmenu ▸ Finset.ext (fun b => by
    simp only [mem_menu, Finset.mem_singleton]
    exact ⟨fun ⟨y, hp, hv⟩ => hv.symm.trans (hf x y hp).symm,
      fun eq => ⟨x, s.prefix_refl n x, eq.symm⟩⟩)⟩

private theorem family_path [Fintype Q] {R : A → Q → (I → Q) → Prop} (f : T → Q)
    (hf : ∀ t, R (s.root t) (f t) (fun i => f (s.child t i))) (n : Nat) :
    ∃ xs, Path (s.Step R) (s.family f 0) xs (s.family f n) :=
  match n with
  | 0 => ⟨[], .nil _⟩
  | k+1 =>
    let ⟨_, path⟩ := family_path f hf k
    ⟨_, path.snoc (s.family_step f hf k)⟩


/-- Selection uses just its displayed arguments. In particular the choice of
a parent menu may not inspect the tree below its child menus. -/
private noncomputable def pick {V : Type} [Nonempty V] (P : V → Prop) : V :=
  if h : ∃ v, P v then h.choose else Classical.choice inferInstance

private theorem pick_spec {V : Type} [Nonempty V] {P : V → Prop} (h : ∃ v, P v) :
    P (pick P) := by simpa only [pick, dif_pos h] using h.choose_spec

private def Allows (R : A → Q → (I → Q) → Prop) (a : A)
    (m : I → Finset Q) (p : Finset Q) : Prop :=
  ∀ v : I → Q, (∀ i, v i ∈ m i) → ∃ b ∈ p, R a b v

private noncomputable def push (R : A → Q → (I → Q) → Prop) (G : Family A Q)
    (m : T → Finset Q) (t : T) : Finset Q :=
  pick fun p => p ∈ G (s.root t) ∧ Allows R (s.root t) (fun i => m (s.child t i)) p

private theorem push_spec {R : A → Q → (I → Q) → Prop} {F G : Family A Q}
    (step : s.Step R F G) {m : T → Finset Q} (hm : ∀ t, m t ∈ F (s.root t)) (t : T) :
    s.push R G m t ∈ G (s.root t) ∧
      Allows R (s.root t) (fun i => m (s.child t i)) (s.push R G m t) :=
  pick_spec (step t _ (fun _ => hm _))

private theorem push_reads (R : A → Q → (I → Q) → Prop) (G : Family A Q)
    {m : T → Finset Q} {k} (hm : s.Reads k m) : s.Reads (k+1) (s.push R G m) :=
  fun x y h => by simp only [push, h.1, funext (fun i => hm _ _ (h.2 i))]

private noncomputable def selectOutput [Nonempty Q] (R : A → Q → (I → Q) → Prop)
    (m : T → Finset Q) (f : T → Q) (t : T) : Q :=
  pick fun b => b ∈ m t ∧ R (s.root t) b (fun i => f (s.child t i))

private theorem select_reads [Nonempty Q] (R : A → Q → (I → Q) → Prop)
    {m : T → Finset Q} {f : T → Q} {k} (hm : s.Reads (k+1) m) (hf : s.Reads k f) :
    s.Reads (k+1) (s.selectOutput R m f) :=
  fun x y h => by simp only [selectOutput, h.1, hm x y h, funext (fun i => hf _ _ (h.2 i))]

private def Link (R : A → Q → (I → Q) → Prop) (f g : T → Q) : Prop :=
  ∀ t, R (s.root t) (g t) (fun i => f (s.child t i))

private theorem execute [Nonempty Q] {R : A → Q → (I → Q) → Prop} {F xs G}
    (path : Path (s.Step R) F xs G) {m : T → Finset Q} {k : Nat}
    (hm : ∀ t, m t ∈ F (s.root t)) (hmk : s.Reads k m) :
    ∃ finalMenu : T → Finset Q,
      (∀ t, finalMenu t ∈ G (s.root t)) ∧ s.Reads (k + xs.length) finalMenu ∧
      ∀ (f : T → Q) (d : Nat), k ≤ d → s.Reads d f → (∀ t, f t ∈ m t) →
        ∃ fs g, Path (s.Link R) f fs g ∧ fs.length = xs.length ∧
          (∀ v ∈ fs, s.Reads (d + xs.length) v) ∧ ∀ t, g t ∈ finalMenu t := by
  induction path generalizing m k with
  | nil => exact ⟨m, hm, hmk, fun f _ _ _ h => ⟨[], f, .nil _, rfl, by simp, h⟩⟩
  | @cons F H xs G step _ ih =>
    let next := s.push R H m
    have member (t : T) : next t ∈ H (s.root t) := (s.push_spec step hm t).1
    have reads : s.Reads (k+1) next := s.push_reads R H hmk
    obtain ⟨last, hl, hlr, run⟩ := ih member reads
    refine ⟨last, hl, by simpa only [List.length_cons, Nat.succ_add, Nat.add_succ] using hlr,
      fun f d hkd hfd hfm => ?_⟩
    let g := s.selectOutput R next f
    have choice (t : T) : g t ∈ next t ∧ R (s.root t) (g t) (fun i => f (s.child t i)) :=
      pick_spec ((s.push_spec step hm t).2 _ (fun _ => hfm _))
    have gr : s.Reads (d+1) g := s.select_reads R (reads.mono s (Nat.succ_le_succ hkd)) hfd
    obtain ⟨fs, v, path, len, bounded, mem⟩ := run g (d+1) (Nat.succ_le_succ hkd) gr (fun t => (choice t).1)
    refine ⟨g :: fs, v, .cons (fun t => (choice t).2) path, by simp [len], ?_, mem⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | h
    · exact gr.mono s (by simp)
    · simpa only [List.length_cons, Nat.succ_add, Nat.add_succ] using bounded w h


private theorem Path.edges {V} {r : V → V → Prop} {x xs y}
    (h : Path r x xs y) : ∃ es : List (V × V),
      es.map Prod.snd = xs ∧ (x :: xs).Perm (y :: es.map Prod.fst) ∧
      ∀ e ∈ es, r e.1 e.2 := by
  induction h with
  | nil x => exact ⟨[], rfl, .refl _, by simp⟩
  | @cons x z xs y edge _ ih =>
    obtain ⟨es, ends, starts, ok⟩ := ih
    exact ⟨(x,z) :: es, congrArg (z :: ·) ends,
      (starts.cons x).trans (.swap _ _ _), fun e he => (List.mem_cons.mp he).elim
        (fun h => h ▸ edge) (ok e)⟩

/-- The source endpoint compiler needs only constants, signed output bits, and
their selected successor occurrences once its finite input guard is fixed. -/
inductive Port (I J : Type) where
  | const (b : Bool)
  | here (j : J)
  | child (i : I) (j : J)
  | neg (p : Port I J)

def Port.eval {J} : Port I J → (J → Bool) → (I → J → Bool) → Bool
  | .const b, _, _ => b
  | .here j, p, _ => p j
  | .child i j, _, c => c i j
  | .neg p, b, c => !(p.eval b c)

def Clauses {J} (rules : A → Port I J → Port I J → Prop)
    (a : A) (parent : J → Bool) (children : I → J → Bool) : Prop :=
  ∀ p q, rules a p q → p.eval parent children ≤ q.eval parent children

private def vote {V : Type} (xs : List V) (b : V → Bool) : Bool :=
  decide (xs.length < 2 * xs.countP b)

private theorem vote_map {V W} (xs : List V) (h : V → W) (b : W → Bool) :
    vote (xs.map h) b = vote xs (fun v => b (h v)) := by simp [vote, Function.comp_def]

private theorem vote_perm {V} {xs ys : List V} (hp : xs.Perm ys) (b : V → Bool) :
    vote xs b = vote ys b := by simp only [vote, hp.length_eq, hp.countP_eq b]

private theorem vote_mono {V} (xs : List V) {a b : V → Bool} (h : ∀ x ∈ xs, a x ≤ b x) :
    vote xs a ≤ vote xs b :=
  have hc := List.countP_mono_left (l := xs) (fun x hx => Bool.le_iff_imp.mp (h x hx))
  Bool.le_iff_imp.mpr (fun ha => decide_eq_true (by have := of_decide_eq_true ha; omega))

private theorem vote_neg {V} {xs : List V} (h : Odd xs.length) (b : V → Bool) :
    vote xs (fun v => !(b v)) = !(vote xs b) := by
  obtain ⟨k, hk⟩ := h
  have counts := xs.length_eq_countP_add_countP b
  simp at counts
  by_cases hb : xs.length < 2 * xs.countP b <;> simp [vote, hb] <;> omega


private theorem vote_const {V} {xs : List V} (h : Odd xs.length) (b : Bool) :
    vote xs (fun _ => b) = b := by
  obtain ⟨k, hk⟩ := h
  cases b <;> simp [vote, hk]
  omega

private theorem Port.vote_eval {V J} (p : Port I J) {es : List V} (ho : Odd es.length)
    (b : V → J → Bool) (c : V → I → J → Bool) :
    p.eval (fun j => vote es (fun e => b e j)) (fun i j => vote es (fun e => c e i j)) =
      vote es (fun e => p.eval (b e) (c e)) := by
  induction p with
  | const v => exact (vote_const ho v).symm
  | here | child => rfl
  | neg p ih => exact (congrArg Bool.not ih).trans (vote_neg ho _).symm

private theorem uniform {J} {rules : A → Port I J → Port I J → Prop} {f fs}
    (path : Path (s.Link (Clauses rules)) f fs f) (ho : Odd fs.length) :
    let g := fun t j => vote fs (fun v => v t j)
    ∀ t, Clauses rules (s.root t) (g t) (fun i => g (s.child t i)) := by
  obtain ⟨es, ends, starts, each⟩ := path.edges
  have odd : Odd es.length := by simpa only [← ends, List.length_map] using ho
  have parent (t : T) (j : J) :
      vote fs (fun v => v t j) = vote es (fun e => e.2 t j) :=
    ends ▸ vote_map es Prod.snd (fun v => v t j)
  have child (t : T) (j : J) :
      vote fs (fun v => v t j) = vote es (fun e => e.1 t j) :=
    (vote_perm starts.cons_inv _).trans (vote_map es Prod.fst (fun v => v t j))
  intro g t p q h
  have eval (v : Port I J) :
      v.eval (fun j => vote fs (fun a => a t j)) (fun i j => vote fs (fun a => a (s.child t i) j)) =
        vote es (fun e => v.eval (e.2 t) (fun i => e.1 (s.child t i))) :=
    (congrArg₂ v.eval (funext (parent t)) (funext fun i => funext (child (s.child t i)))).trans
      (v.vote_eval odd _ _)
  exact (eval p) ▸ (eval q) ▸ vote_mono es (fun e he => each e he t p q h)


/-- Twice the maximum length of the shortened odd cycle. The arguments count
root labels and complete output tuples, respectively. -/
def windowBound (labels tuples : Nat) : Nat := 2 * ((2 ^ (2 ^ tuples)) ^ labels + 1)

private theorem vote_reads {J : Type} (fs : List (T → J → Bool)) {n}
    (hr : ∀ f ∈ fs, s.Reads n f) : s.Reads n (fun t j => vote fs (fun f => f t j)) :=
  fun x y h => funext fun j => by
    have eq : fs.map (fun f => f x j) = fs.map (fun f => f y j) :=
      List.map_congr_left fun f hf => congrFun (hr f hf x y h) j
    exact (vote_map fs (fun f => f x j) id).symm.trans
      ((congrArg (fun bs => vote bs id) eq).trans (vote_map fs (fun f => f y j) id))

/-- Input-only stopping for the guarded binary tree constraints. Each bit of
the returned tuple has the same window, including across different child routes.
Reification as positive type images additionally requires order between distinct
observer trees. -/
theorem finite_window_bound [Fintype A] {J : Type} [Fintype J]
    (rules : A → Port I J → Port I J → Prop) {n} (f : T → J → Bool)
    (hf : s.Reads n f) (ok : ∀ t, Clauses rules (s.root t) (f t) (fun i => f (s.child t i))) :
    ∃ g : T → J → Bool, s.Reads (windowBound (Fintype.card A) (2 ^ Fintype.card J)) g ∧
      ∀ t, Clauses rules (s.root t) (g t) (fun i => g (s.child t i)) := by
  classical
  obtain ⟨xs, path⟩ := s.family_path f ok n
  obtain ⟨ys, short, odd, bound⟩ := path.odd_short (s.seed_loop f ok)
  obtain ⟨m, hm, hmr, run⟩ := s.execute short (s.menu_member f 0) (s.menu_zero_reads f)
  let seed (t : T) : J → Bool := pick (· ∈ m t)
  have singleton (t : T) : m t = {seed t} := by
    obtain ⟨b, _, hb⟩ := s.terminal hf (hm t)
    have inside : seed t ∈ m t := pick_spec ⟨b, hb ▸ Finset.mem_singleton_self b⟩
    simp only [hb, Finset.mem_singleton] at inside
    exact inside ▸ hb
  have sr : s.Reads ys.length seed := fun x y he => congrArg (fun ms => pick (· ∈ ms))
    (hmr x y (by simpa only [Nat.zero_add] using he))
  obtain ⟨fs, g, links, len, depth, mem⟩ := run seed ys.length (Nat.zero_le _) sr
    (fun t => s.inside_seed f (hm t) ((singleton t) ▸ Finset.mem_singleton_self _))
  have eq : g = seed := funext fun t => Finset.mem_singleton.mp (singleton t ▸ mem t)
  subst g
  refine ⟨_, (s.vote_reads fs depth).mono s ?_, s.uniform links (len ▸ odd)⟩
  simp only [Family, Fintype.card_fun, Fintype.card_finset, Fintype.card_bool] at bound
  unfold windowBound
  omega

end Trees
end ModalityInference.ComparisonWindowPumping
