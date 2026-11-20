import ModalityInference.Proofs.ComparisonWindowObservers

/-! Pair profiles of bounded positive types, their one-level simulation, and
simultaneous reification on a certified finite observation window. -/
namespace ModalityInference.ComparisonWindowTerms

open ComparisonWindowPumping ComparisonWindowEndpoints ComparisonObserverMachine
  ComparisonRankedBasis ComparisonStructuralLayout ComparisonInterpolation

variable {T A : Type}

def Allowed (Δ : Bounds) (types : List TypeVar) (modes : List ModVar) (a : CompareTy) : Prop :=
  a.DefinedUnder Δ ∧ Supports (· ∈ types) (· ∈ modes) a

def pair (s : Trees T A Constructor) (l : Fields A) (a : CompareTy) (x y : T) : Bool × Bool :=
  (value (l.nodes s) a x, value (l.nodes s) a y)

noncomputable def profile (s : Trees T A Constructor) (l : Fields A) (Δ : Bounds)
    (types : List TypeVar) (modes : List ModVar) (n : Nat) (x y : T) : Finset (Bool × Bool) :=
  open Classical in Finset.univ.filter (fun p => ∃ a, Allowed Δ types modes a ∧ rank a ≤ n ∧
    pair s l a x y = p)

@[simp] theorem mem_profile (s : Trees T A Constructor) (l : Fields A) (Δ : Bounds)
    (types : List TypeVar) (modes : List ModVar) (n : Nat) (x y : T) (p : Bool × Bool) :
    p ∈ profile s l Δ types modes n x y ↔
      ∃ a, Allowed Δ types modes a ∧ rank a ≤ n ∧ pair s l a x y = p := by
  simp [profile]

private theorem allowed_op (Δ types modes) (op : Constructor) (a b : CompareTy) :
    Allowed Δ types modes (op.op a b) ↔ Allowed Δ types modes a ∧ Allowed Δ types modes b := by
  cases op <;> simp only [Allowed, Constructor.op, Supports,
    CompareTy.definedUnder_prod_iff, CompareTy.definedUnder_sum_iff, CompareTy.definedUnder_fn_iff]
  all_goals tauto

private theorem allowed_join (Δ types modes) (a b : CompareTy) :
    Allowed Δ types modes (.join a b) ↔ Allowed Δ types modes a ∧ Allowed Δ types modes b := by
  simp only [Allowed, Supports, CompareTy.definedUnder_join_iff]
  tauto

private theorem allowed_meet (Δ types modes) (a b : CompareTy) :
    Allowed Δ types modes (.meet a b) ↔ Allowed Δ types modes a ∧ Allowed Δ types modes b := by
  simp only [Allowed, Supports, CompareTy.definedUnder_meet_iff]
  tauto

private theorem rank_op (op : Constructor) (a b) :
    rank (op.op a b) = max (rank a) (rank b) + 1 := by cases op <;> rfl

private theorem transfer_op (s : Trees T A Constructor) (l : Fields A) (Δ types modes)
    {n m : Nat} {x y x' y' : T} (hx : s.root x = s.root x') (hy : s.root y = s.root y')
    (op : Constructor)
    (ch : profile s l Δ types modes n (s.child x op) (s.child y op) ⊆
      profile s l Δ types modes m (s.child x' op) (s.child y' op))
    (a b : CompareTy) (ha : Allowed Δ types modes (op.op a b)) (hr : rank (op.op a b) ≤ n+1) :
    pair s l (op.op a b) x y ∈ profile s l Δ types modes (m+1) x' y' := by
  obtain ⟨hat, hbt⟩ := (allowed_op ..).mp ha
  have hmax := Nat.le_of_succ_le_succ ((rank_op op a b) ▸ hr)
  have get (t : CompareTy) (ht : Allowed Δ types modes t) (htr : rank t ≤ n) :=
    (mem_profile ..).mp (ch ((mem_profile ..).mpr ⟨t, ht, htr, rfl⟩))
  obtain ⟨a', ha', ra', va⟩ := get a hat ((Nat.le_max_left ..).trans hmax)
  obtain ⟨b', hb', rb', vb⟩ := get b hbt ((Nat.le_max_right ..).trans hmax)
  refine (mem_profile ..).mpr ⟨op.op a' b', (allowed_op ..).mpr ⟨ha', hb'⟩,
    (rank_op op a' b') ▸ Nat.succ_le_succ (max_le ra' rb'), ?_⟩
  have exa := congrArg Prod.fst va
  have eya := congrArg Prod.snd va
  have exb := congrArg Prod.fst vb
  have eyb := congrArg Prod.snd vb
  simp only [pair] at exa eya exb eyb
  simp only [pair, value_constructor, branchValue, Fields.nodes, hx, hy, exa, eya, exb, eyb]

private theorem allowed_modal (Δ types modes) (a : CompareTy) (m : ModExpr) :
    Allowed Δ types modes (.modal a m) ↔
      Allowed Δ types modes a ∧ Entails Δ (.defined m) ∧ ∀ v ∈ m.vars, v ∈ modes := by
  simp only [Allowed, Supports, CompareTy.definedUnder_modal_iff]
  tauto

theorem profile_transfer (s : Trees T A Constructor) (l : Fields A) (Δ types modes)
    {n m : Nat} {x y x' y' : T} (hx : s.root x = s.root x') (hy : s.root y = s.root y')
    (hc : ∀ i, profile s l Δ types modes n (s.child x i) (s.child y i) ⊆
      profile s l Δ types modes m (s.child x' i) (s.child y' i)) :
    profile s l Δ types modes (n+1) x y ⊆ profile s l Δ types modes (m+1) x' y' := by
  intro p hp
  obtain ⟨a, ha, hr, rfl⟩ := (mem_profile ..).mp hp
  clear hp
  induction a with
  | var v | unit | credit =>
    exact (mem_profile ..).mpr ⟨_, ha, Nat.zero_le _, by simp only [pair, value, Fields.nodes, hx, hy]⟩
  | prod a b _ _ => exact transfer_op s l Δ types modes hx hy .prod (hc .prod) a b ha hr
  | sum a b _ _ => exact transfer_op s l Δ types modes hx hy .sum (hc .sum) a b ha hr
  | fn a b _ _ => exact transfer_op s l Δ types modes hx hy .fn (hc .fn) a b ha hr
  | modal a ω ih =>
    obtain ⟨hat, hw⟩ := (allowed_modal ..).mp ha
    obtain ⟨a', ha', hr', eq⟩ := (mem_profile ..).mp (ih hat hr)
    refine (mem_profile ..).mpr ⟨.modal a' ω, (allowed_modal ..).mpr ⟨ha', hw⟩, hr', ?_⟩
    obtain ⟨ex, ey⟩ := Prod.mk.inj eq
    simp only [pair, value, Fields.nodes, hx, hy, ex, ey]
  | join a b iha ihb =>
    obtain ⟨hat, hbt⟩ := (allowed_join ..).mp ha
    obtain ⟨a', ha', hra, ea⟩ := (mem_profile ..).mp (iha hat (le_trans (Nat.le_max_left ..) hr))
    obtain ⟨b', hb', hrb, eb⟩ := (mem_profile ..).mp (ihb hbt (le_trans (Nat.le_max_right ..) hr))
    refine (mem_profile ..).mpr ⟨.join a' b', (allowed_join ..).mpr ⟨ha', hb'⟩, max_le hra hrb, ?_⟩
    obtain ⟨xa, ya⟩ := Prod.mk.inj ea
    obtain ⟨xb, yb⟩ := Prod.mk.inj eb
    simp only [pair, value, xa, ya, xb, yb]
  | meet a b iha ihb =>
    obtain ⟨hat, hbt⟩ := (allowed_meet ..).mp ha
    obtain ⟨a', ha', hra, ea⟩ := (mem_profile ..).mp (iha hat (le_trans (Nat.le_max_left ..) hr))
    obtain ⟨b', hb', hrb, eb⟩ := (mem_profile ..).mp (ihb hbt (le_trans (Nat.le_max_right ..) hr))
    refine (mem_profile ..).mpr ⟨.meet a' b', (allowed_meet ..).mpr ⟨ha', hb'⟩, max_le hra hrb, ?_⟩
    obtain ⟨xa, ya⟩ := Prod.mk.inj ea
    obtain ⟨xb, yb⟩ := Prod.mk.inj eb
    simp only [pair, value, xa, ya, xb, yb]

private theorem meet_at (s : Trees T A Constructor) (l : Fields A) (Δ types modes) (k : Nat)
    (g : T → Bool) (hg : ∀ x y, (g x, g y) ∈ profile s l Δ types modes k x y)
    (x : T) (ys : List T) :
    ∃ a, Allowed Δ types modes a ∧ rank a ≤ k ∧ value (l.nodes s) a x = g x ∧
      ∀ y ∈ ys, value (l.nodes s) a y ≤ g y := by
  induction ys with
  | nil =>
    obtain ⟨a, ha, hr, he⟩ := (mem_profile ..).mp (hg x x)
    exact ⟨a, ha, hr, congrArg Prod.fst he, by simp⟩
  | cons y ys ih =>
    obtain ⟨a, ha, ra, ex, le⟩ := ih
    obtain ⟨b, hb, rb, eq⟩ := (mem_profile ..).mp (hg x y)
    obtain ⟨bx, byv⟩ := Prod.mk.inj eq
    refine ⟨.meet a b, (allowed_meet ..).mpr ⟨ha, hb⟩, max_le ra rb,
      by simp only [value, ex, bx, Bool.and_self], fun z hz => ?_⟩
    change value (l.nodes s) a z ⊓ value (l.nodes s) b z ≤ g z
    rcases List.mem_cons.mp hz with rfl | h
    · exact (inf_le_right : _ ⊓ _ ≤ value (l.nodes s) b z).trans byv.le
    · exact inf_le_left.trans (le z h)

private theorem reify_list (s : Trees T A Constructor) (l : Fields A) (Δ types modes)
    (k : Nat) (g : T → Bool) (hg : ∀ x y, (g x, g y) ∈ profile s l Δ types modes k x y)
    (xs : List T) : ∃ a, Allowed Δ types modes a ∧ rank a ≤ k ∧
      ∀ x ∈ xs, value (l.nodes s) a x = g x := by
  cases xs with
  | nil =>
    exact ⟨.unit, ⟨fun _ _ => by simp [CompareTy.wellFormedBounds, ModeModels], trivial⟩,
      Nat.zero_le _, by simp⟩
  | cons x xs =>
    let all := x :: xs
    have fold (ys : List T) :
        ∃ a, Allowed Δ types modes a ∧ rank a ≤ k ∧
          (∀ z ∈ all, value (l.nodes s) a z ≤ g z) ∧
            ∀ y ∈ ys, g y ≤ value (l.nodes s) a y := by
      induction ys with
      | nil =>
        obtain ⟨a, ha, ra, _, low⟩ := meet_at s l Δ types modes k g hg x all
        exact ⟨a, ha, ra, low, by simp⟩
      | cons y ys ih =>
        obtain ⟨a, ha, ra, low, high⟩ := ih
        obtain ⟨b, hb, rb, eqb, leb⟩ := meet_at s l Δ types modes k g hg y all
        refine ⟨.join a b, (allowed_join ..).mpr ⟨ha, hb⟩, max_le ra rb,
          fun z hz => sup_le (low z hz) (leb z hz), fun z hz => ?_⟩
        rcases List.mem_cons.mp hz with rfl | h
        · exact eqb.ge.trans le_sup_right
        · exact (high z h).trans le_sup_left
    obtain ⟨a, ha, ra, low, high⟩ := fold all
    exact ⟨a, ha, ra, fun z hz => le_antisymm (low z hz) (high z hz)⟩

open ComparisonDefiniteTreeMachines

private def block (s : Trees T A Constructor) : (k : Nat) → T → Window A Constructor (k+1)
  | 0, t => (s.root t, fun _ => PUnit.unit)
  | k+1, t => (s.root t, fun i => block s k (s.child t i))

private theorem prefix_of_block (s : Trees T A Constructor) (k : Nat) (x y : T)
    (h : block s k x = block s k y) : s.Prefix k x y := by
  induction k generalizing x y with
  | zero => exact congrArg Prod.fst h
  | succ k ih => exact ⟨congrArg Prod.fst h, fun i => ih _ _ (congrFun (congrArg Prod.snd h) i)⟩

theorem positive_reify [Fintype A] (s : Trees T A Constructor) (l : Fields A) (Δ types modes)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (k : Nat) (g : T → Bool)
    (hg : ∀ x y, (g x, g y) ∈ profile s l Δ types modes k x y) :
    ∃ a, Allowed Δ types modes a ∧ rank a ≤ k ∧ a.WellShaped Δ ∧
      ∀ t, value (l.nodes s) a t = g t := by
  classical
  let Ix := Set.range (block s k)
  letI : Fintype Ix := Fintype.ofFinite Ix
  let pick (i : Ix) := i.property.choose
  let xs := (Finset.univ : Finset Ix).toList.map pick
  obtain ⟨a, ha, ra, ok⟩ := reify_list s l Δ types modes k g hg xs
  refine ⟨a, ha, ra, a.wellShaped_of_no_models hn, fun t => ?_⟩
  let i : Ix := ⟨block s k t, t, rfl⟩
  have ep := prefix_of_block s k (pick i) t i.property.choose_spec
  have localEq := ok (pick i) (List.mem_map.mpr ⟨i, by simp, rfl⟩)
  obtain ⟨b, _, rb, he⟩ := (mem_profile ..).mp (hg (pick i) t)
  obtain ⟨bg, bt⟩ := Prod.mk.inj he
  calc
    _ = value (l.nodes s) a (pick i) := ((value_reads s l a).mono s ra _ _ ep).symm
    _ = g (pick i) := localEq
    _ = value (l.nodes s) b (pick i) := bg.symm
    _ = value (l.nodes s) b t := (value_reads s l b).mono s rb _ _ ep
    _ = _ := bt

end ModalityInference.ComparisonWindowTerms
