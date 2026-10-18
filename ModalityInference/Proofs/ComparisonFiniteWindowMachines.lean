import ModalityInference.Proofs.ComparisonDefiniteTreeMachines

/-! Output-reading finite machines characterize shared finite-window functions
on a finite tree alphabet, with any fixed finite set of constructor routes.
The characterization retains local constraints, monotonicity, prescribed constant
outputs, and realization by finite lattice terms over the observation window.
The canonical prefix-memory construction depends on the function's window depth;
this theorem does not bound machine size from the local constraints. -/
namespace ModalityInference.ComparisonDefiniteTreeMachines

variable {A I Q B : Type}

/-- Only the observed output, rather than all auxiliary states, must forget the frontier. -/
def OutputForgets (step : A → (I → Q) → Q) (read : Q → B) (n : Nat) : Prop :=
  ∀ x u v, read (fold step n x u) = read (fold step n x v)

def output (step : A → (I → Q) → Q) (read : Q → B)
    (n : Nat) (seed : Q) (x : List I → A) : B := read (solution step n seed x)

theorem outputForgets_of_pairs [Fintype A] [Fintype I] [Fintype Q]
    [DecidableEq I] [DecidableEq Q]
    (step : A → (I → Q) → Q) (read : Q → B) (n : Nat)
    (h : ∀ p ∈ pairs step n, read p.1 = read p.2) : OutputForgets step read n := by
  intro x u v
  exact h _ (fold_pair step n x u v)

theorem outputForgets_iff_pairs [Fintype A] [Fintype I] [Fintype Q]
    [DecidableEq I] [DecidableEq Q] [Nonempty A]
    (step : A → (I → Q) → Q) (read : Q → B) (n : Nat) :
    OutputForgets step read n ↔ ∀ p ∈ pairs step n, read p.1 = read p.2 := by
  constructor
  · intro h p hp
    obtain ⟨x, u, v, hu, hv⟩ := pair_fold step n hp
    exact (congrArg read hu).symm.trans ((h x u v).trans (congrArg read hv))
  · exact outputForgets_of_pairs step read n

theorem outputForgets_bounded [Fintype A] [Fintype I] [Fintype Q]
    [DecidableEq I] [DecidableEq Q] [Nonempty A]
    (step : A → (I → Q) → Q) (read : Q → B) :
    (∃ n, OutputForgets step read n) ↔
      OutputForgets step read (Fintype.card (Q × Q)) := by
  constructor
  · rintro ⟨n, hn⟩
    apply outputForgets_of_pairs
    intro p hp
    apply (outputForgets_iff_pairs step read n).mp hn p
    rcases le_total n (Fintype.card (Q × Q)) with h | h
    · exact pairs_antitone step h hp
    · rwa [pairs_stable step n h]
  · exact fun h => ⟨_, h⟩

theorem outputForgets_succ (step : A → (I → Q) → Q) (read : Q → B)
    (n : Nat) (hn : OutputForgets step read n) : OutputForgets step read (n + 1) := by
  intro x u v
  rw [fold_push, fold_push]
  exact hn _ _ _

theorem outputForgets_mono (step : A → (I → Q) → Q) (read : Q → B)
    {n m : Nat} (hn : OutputForgets step read n) (hm : n ≤ m) :
    OutputForgets step read m := by
  induction m, hm using Nat.le_induction with
  | base => exact hn
  | succ m hm ih => exact outputForgets_succ step read m ih

theorem output_stable (step : A → (I → Q) → Q) (read : Q → B)
    {n m : Nat} (hn : OutputForgets step read n) (hm : n ≤ m) (seed : Q)
    (x : List I → A) : output step read m seed x = output step read n seed x := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    change read (fold step (m + 1) x _) = _
    rw [fold_push, outputForgets_mono step read hn hm x _ (fun _ => seed)]
    exact ih

theorem output_satisfies (step : A → (I → Q) → Q) (read : Q → B)
    (n : Nat) (seed : Q) (hn : OutputForgets step read n)
    (R : A → B → (I → B) → Prop)
    (hs : ∀ a child, R a (read (step a child)) (fun i => read (child i)))
    (x : List I → A) :
    R (x []) (output step read n seed x) (fun i => output step read n seed (down i x)) := by
  have he : output step read n seed x =
      read (step (x []) (fun i => solution step n seed (down i x))) := by
    change read (fold step n x (fun _ => seed)) =
      read (fold step (n + 1) x (fun _ => seed))
    rw [fold_push]
    exact hn _ _ _
  rw [he]
  exact hs _ _

def Depends (n : Nat) (f : (List I → A) → B) : Prop :=
  ∀ x y, (∀ p, p.length < n → x p = y p) → f x = f y

theorem output_depends (step : A → (I → Q) → Q) (read : Q → B)
    (n : Nat) (seed : Q) : Depends n (output step read n seed) := by
  intro x y h
  exact congrArg read (solution_prefix step n seed x y h)

/-- A finite prefix, retaining all constructor routes to the chosen depth. -/
def Window (A I : Type) : Nat → Type
  | 0 => PUnit
  | n + 1 => A × (I → Window A I n)

namespace Window

def trim : (n : Nat) → Window A I (n + 1) → Window A I n
  | 0, _ => PUnit.unit
  | n + 1, w => (w.1, fun i => trim n (w.2 i))

def capture (n : Nat) (x : List I → A) : Window A I n :=
  match n with
  | 0 => PUnit.unit
  | n + 1 => (x [], fun i => capture n (down i x))

def step (n : Nat) (a : A) (children : I → Window A I n) : Window A I n :=
  match n with
  | 0 => PUnit.unit
  | n + 1 => (a, fun i => trim n (children i))

def tree (n : Nat) (fallback : A) (w : Window A I n) : List I → A :=
  match n with
  | 0 => fun _ => fallback
  | n + 1 => graft w.1 (fun i => tree n fallback (w.2 i))

theorem trim_step (n : Nat) (a : A) (children : I → Window A I (n + 1)) :
    trim n (step (n + 1) a children) = step n a (fun i => trim n (children i)) := by
  cases n <;> rfl

theorem trim_fold (n depth : Nat) (x : List I → A)
    (leaves : List I → Window A I (n + 1)) :
    trim n (fold (step (n + 1)) depth x leaves) =
      fold (step n) depth x (fun p => trim n (leaves p)) := by
  induction depth generalizing x leaves with
  | zero => rfl
  | succ depth ih =>
    simp only [fold, trim_step]
    apply congrArg (step n (x []))
    funext i
    exact ih (down i x) (down i leaves)

theorem fold_depth (n : Nat) (x : List I → A) (leaves : List I → Window A I n) :
    fold (step n) n x leaves = capture n x := by
  induction n generalizing x with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ n ih =>
    change (x [], fun i => trim n (fold (step (n + 1)) n (down i x) (down i leaves))) = _
    simp only [trim_fold]
    change (x [], _) = (x [], _)
    congr 1
    funext i
    exact ih (down i x) _

theorem forgets (n : Nat) : Forgets (step (A := A) (I := I) n) n := by
  intro x u v
  rw [fold_depth, fold_depth]

theorem capture_tree (n : Nat) (fallback : A) (w : Window A I n) :
    capture n (tree n fallback w) = w := by
  induction n with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ n ih =>
    change (w.1, fun i => capture n (tree n fallback (w.2 i))) = w
    simp only [ih]
    rfl

theorem tree_capture (n : Nat) (fallback : A) (x : List I → A)
    (p : List I) (hp : p.length < n) : tree n fallback (capture n x) p = x p := by
  induction n generalizing x p with
  | zero => omega
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons i p =>
      exact ih (down i x) p (by simpa using hp)

theorem trim_capture (n : Nat) (x : List I → A) :
    trim n (capture (n + 1) x) = capture n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change (x [], fun i => trim n (capture (n + 1) (down i x))) = _
    simp only [ih]
    rfl

theorem step_capture (n : Nat) (a : A) (x : I → List I → A) :
    step n a (fun i => capture n (x i)) = capture n (graft a x) := by
  cases n with
  | zero => rfl
  | succ n =>
    change (a, fun i => trim n (capture (n + 1) (x i))) = _
    simp only [trim_capture]
    rfl

def finite [Fintype A] [Fintype I] [DecidableEq I] : (n : Nat) → Fintype (Window A I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI := finite n
    exact inferInstanceAs (Fintype (A × (I → Window A I n)))

attribute [instance] finite

def preorder [Preorder A] : (n : Nat) → Preorder (Window A I n)
  | 0 => inferInstanceAs (Preorder PUnit)
  | n + 1 => by
    letI := preorder n
    exact inferInstanceAs (Preorder (A × (I → Window A I n)))

attribute [instance] preorder

theorem trim_mono [Preorder A] (n : Nat) : Monotone (trim (A := A) (I := I) n) := by
  induction n with
  | zero => intro u v h; exact le_rfl
  | succ n ih =>
    intro u v h
    exact ⟨h.1, fun i => ih (h.2 i)⟩

theorem step_mono [Preorder A] (n : Nat) (a b : A) (hab : a ≤ b)
    (u v : I → Window A I n) (huv : ∀ i, u i ≤ v i) : step n a u ≤ step n b v := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact ⟨hab, fun i => trim_mono n (huv i)⟩

theorem tree_mono [Preorder A] (n : Nat) (fallback : A) :
    Monotone (tree (I := I) n fallback) := by
  induction n with
  | zero => intro u v h p; exact le_rfl
  | succ n ih =>
    intro u v h p
    cases p with
    | nil => exact h.1
    | cons i p => exact ih (h.2 i) p

theorem constant_fixed (n : Nat) (a : A) :
    step (I := I) n a (fun _ => capture n (fun _ => a)) = capture n (fun _ => a) := by
  rw [step_capture]
  apply congrArg (capture n)
  funext p
  cases p <;> rfl

def read (n : Nat) (fallback : A) (f : (List I → A) → B) (w : Window A I n) : B :=
  f (tree n fallback w)

theorem read_mono [Preorder A] [Preorder B] (n : Nat) (fallback : A)
    (f : (List I → A) → B) (hf : Monotone f) : Monotone (read n fallback f) := by
  exact hf.comp (tree_mono n fallback)

theorem read_capture (n : Nat) (fallback : A) (f : (List I → A) → B)
    (hf : Depends n f) (x : List I → A) : read n fallback f (capture n x) = f x := by
  apply hf
  exact tree_capture n fallback x

theorem read_step (n : Nat) (fallback : A) (f : (List I → A) → B)
    (hf : Depends n f) (a : A) (children : I → Window A I n) :
    read n fallback f (step n a children) =
      f (graft a (fun i => tree n fallback (children i))) := by
  have he : step n a children =
      capture n (graft a (fun i => tree n fallback (children i))) := by
    rw [← step_capture]
    exact congrArg (step n a) (funext fun i => (capture_tree n fallback (children i)).symm)
  rw [he]
  exact read_capture n fallback f hf _

theorem read_local (n : Nat) (fallback : A) (f : (List I → A) → B)
    (hf : Depends n f) (R : A → B → (I → B) → Prop)
    (hr : ∀ x, R (x []) (f x) (fun i => f (down i x)))
    (a : A) (children : I → Window A I n) :
    R a (read n fallback f (step n a children))
      (fun i => read n fallback f (children i)) := by
  rw [read_step n fallback f hf]
  exact hr (graft a (fun i => tree n fallback (children i)))

end Window

/-- Auxiliary memory is finite; all outputs use the same transition and read map. -/
structure Machine (A I B : Type) where
  State : Type
  finite : Fintype State
  seed : State
  step : A → (I → State) → State
  read : State → B

attribute [instance] Machine.finite

namespace Machine

def ofWindow [Fintype A] [Fintype I] [DecidableEq I]
    (n : Nat) (fallback : A) (f : (List I → A) → B) : Machine A I B :=
  ⟨Window A I n, inferInstance, Window.capture n (fun _ => fallback),
    Window.step n, Window.read n fallback f⟩

def depth (m : Machine A I B) : Nat := Fintype.card (m.State × m.State)

def Forgets (m : Machine A I B) : Prop := OutputForgets m.step m.read m.depth

def value (m : Machine A I B) : (List I → A) → B := output m.step m.read m.depth m.seed

def Local (m : Machine A I B) (R : A → B → (I → B) → Prop) : Prop :=
  ∀ a child, R a (m.read (m.step a child)) (fun i => m.read (child i))

theorem value_depends (m : Machine A I B) : Depends m.depth m.value :=
  output_depends m.step m.read m.depth m.seed

theorem value_local (m : Machine A I B) (hm : m.Forgets)
    (R : A → B → (I → B) → Prop) (hr : m.Local R) (x : List I → A) :
    R (x []) (m.value x) (fun i => m.value (down i x)) :=
  output_satisfies m.step m.read m.depth m.seed hm R hr x

theorem ofWindow_forgets [Fintype A] [Fintype I] [DecidableEq I] [Nonempty A]
    (n : Nat) (fallback : A) (f : (List I → A) → B) : (ofWindow n fallback f).Forgets := by
  classical
  apply (outputForgets_bounded _ _).mp
  exact ⟨n, fun x u v => congrArg (Window.read n fallback f) (Window.forgets n x u v)⟩

theorem ofWindow_value [Fintype A] [Fintype I] [DecidableEq I] [Nonempty A]
    (n : Nat) (fallback : A) (f : (List I → A) → B) (hf : Depends n f) :
    (ofWindow n fallback f).value = f := by
  classical
  let m := ofWindow n fallback f
  have hn : OutputForgets m.step m.read n := fun x u v =>
    congrArg m.read (Window.forgets n x u v)
  have hbound : m.Forgets := ofWindow_forgets n fallback f
  funext x
  have he : m.value x = output m.step m.read n m.seed x := by
    rcases le_total n m.depth with h | h
    · exact output_stable m.step m.read hn h m.seed x
    · exact (output_stable m.step m.read hbound h m.seed x).symm
  change m.value x = _
  rw [he]
  change Window.read n fallback f (fold (Window.step n) n x _) = _
  rw [Window.fold_depth]
  exact Window.read_capture n fallback f hf x

def Ordered [Preorder A] [Preorder B] (m : Machine A I B) (order : Preorder m.State) : Prop :=
  (∀ a b, a ≤ b → ∀ u v, (∀ i, order.le (u i) (v i)) →
    order.le (m.step a u) (m.step b v)) ∧
  (∀ u v, order.le u v → m.read u ≤ m.read v)

def Boundary (m : Machine A I B) (a : A) (b : B) : Prop :=
  ∃ q, m.step a (fun _ => q) = q ∧ m.read q = b

theorem value_mono [Preorder A] [Preorder B] (m : Machine A I B)
    (order : Preorder m.State) (h : m.Ordered order) : Monotone m.value := by
  letI := order
  intro x y hxy
  exact h.2 _ _ (solution_mono m.step h.1 m.depth m.seed hxy)

theorem value_boundary (m : Machine A I B) (hm : m.Forgets)
    (a : A) (b : B) (hb : m.Boundary a b) : m.value (fun _ => a) = b := by
  obtain ⟨q, hq, hr⟩ := hb
  exact (hm (fun _ => a) (fun _ => m.seed) (fun _ => q)).trans
    ((congrArg m.read (fold_constant m.step a q hq m.depth)).trans hr)

theorem ofWindow_ordered [Fintype A] [Fintype I] [DecidableEq I]
    [Preorder A] [Preorder B]
    (n : Nat) (fallback : A) (f : (List I → A) → B) (hf : Monotone f) :
    (ofWindow n fallback f).Ordered (Window.preorder n) := by
  exact ⟨Window.step_mono n, Window.read_mono n fallback f hf⟩

theorem ofWindow_boundary [Fintype A] [Fintype I] [DecidableEq I]
    (n : Nat) (fallback : A) (f : (List I → A) → B) (hf : Depends n f) (a : A) :
    (ofWindow n fallback f).Boundary a (f (fun _ => a)) := by
  exact ⟨Window.capture n (fun _ => a), Window.constant_fixed n a,
    Window.read_capture n fallback f hf _⟩

end Machine

theorem finite_window_machine [Fintype A] [Fintype I] [Nonempty A]
    (f : (List I → A) → B) (n : Nat) (hf : Depends n f)
    (R : A → B → (I → B) → Prop)
    (hr : ∀ x, R (x []) (f x) (fun i => f (down i x))) :
    ∃ m : Machine A I B, m.Forgets ∧ m.Local R ∧ m.value = f := by
  classical
  let fallback : A := Classical.choice inferInstance
  exact ⟨Machine.ofWindow n fallback f, Machine.ofWindow_forgets n fallback f,
    Window.read_local n fallback f hf R hr, Machine.ofWindow_value n fallback f hf⟩

theorem finite_window_iff_machine [Fintype A] [Fintype I] [Nonempty A]
    (f : (List I → A) → B) (R : A → B → (I → B) → Prop) :
    ((∃ n, Depends n f) ∧ ∀ x, R (x []) (f x) (fun i => f (down i x))) ↔
      ∃ m : Machine A I B, m.Forgets ∧ m.Local R ∧ m.value = f := by
  constructor
  · rintro ⟨⟨n, hn⟩, hr⟩
    exact finite_window_machine f n hn R hr
  · rintro ⟨m, hm, hr, rfl⟩
    exact ⟨⟨_, m.value_depends⟩, m.value_local hm R hr⟩

/-- The finite certificate also preserves pointwise order and all prescribed
constant inputs. No state bound derived from `R` is assumed or concluded. -/
theorem finite_window_ordered_iff [Fintype A] [Fintype I] [Nonempty A]
    [Preorder A] [Preorder B]
    (f : (List I → A) → B) (R : A → B → (I → B) → Prop) (boundary : A → B) :
    ((∃ n, Depends n f) ∧ Monotone f ∧ (∀ a, f (fun _ => a) = boundary a) ∧
      ∀ x, R (x []) (f x) (fun i => f (down i x))) ↔
    ∃ m : Machine A I B, ∃ order : Preorder m.State,
      m.Forgets ∧ m.Ordered order ∧ m.Local R ∧
      (∀ a, m.Boundary a (boundary a)) ∧ m.value = f := by
  classical
  constructor
  · rintro ⟨⟨n, hn⟩, hm, hb, hr⟩
    let fallback : A := Classical.choice inferInstance
    refine ⟨Machine.ofWindow n fallback f, Window.preorder n,
      Machine.ofWindow_forgets n fallback f, Machine.ofWindow_ordered n fallback f hm,
      Window.read_local n fallback f hn R hr, ?_, Machine.ofWindow_value n fallback f hn⟩
    intro a
    rw [← hb a]
    exact Machine.ofWindow_boundary n fallback f hn a
  · rintro ⟨m, order, hm, ho, hr, hb, rfl⟩
    exact ⟨⟨_, m.value_depends⟩, m.value_mono order ho,
      fun a => m.value_boundary hm a _ (hb a), m.value_local hm R hr⟩

/-- The observed tuple is realized simultaneously by finite positive lattice
terms over the supplied finite observation window. -/
theorem Machine.finite_reify {J K L : Type} [Lattice L]
    (m : Machine (J → Bool) I (K → Bool)) (order : Preorder m.State)
    (hm : m.Forgets) (ho : m.Ordered order)
    (hz : m.Boundary (fun _ => false) (fun _ => false))
    (ht : m.Boundary (fun _ => true) (fun _ => true))
    (atoms : List I → J → L) (p : Finset L)
    (hp : ∀ path, path.length < m.depth → ∀ j, atoms path j ∈ p) :
    ∃ terms : K → L,
      (∀ k, ComparisonObserverChains.LatticeGenerated p (terms k)) ∧
      ∀ (f : LatticeHom L Bool) k,
        f (terms k) = m.value (fun path j => f (atoms path j)) k := by
  classical
  letI := order
  have hterm (k : K) : ∃ t : L,
      ComparisonObserverChains.LatticeGenerated p t ∧
      ∀ f : LatticeHom L Bool, f t = m.value (fun path j => f (atoms path j)) k := by
    apply ComparisonObserverChains.finite_reify_property p
      (fun f => m.value (fun path j => f (atoms path j)) k)
      ?_ ?_ ?_ (ComparisonObserverChains.LatticeGenerated p)
      (fun _ => .atom) (fun _ _ => .sup) (fun _ _ => .inf)
    · intro f g hfg
      apply ho.2
      exact fold_prefix_mono m.step ho.1 m.depth _ _ _ _
        (fun path hpath j => hfg _ (hp path hpath j)) (fun _ => le_rfl)
    · exact congrFun (m.value_boundary hm _ _ hz) k
    · exact congrFun (m.value_boundary hm _ _ ht) k
  choose terms hg hv using hterm
  exact ⟨terms, hg, fun f k => hv k f⟩

end ModalityInference.ComparisonDefiniteTreeMachines
