import ModalityInference.Proofs.ComparisonWindowWitness

/-! A signed implication can run up one observer and down a second, crossing an
order comparison between their roots. A long common constructor route forces
the implication between every pair of fillings of its two end headers. -/
namespace ModalityInference.ComparisonWindowExcursions

open ComparisonWindowPumping ComparisonWindowPumping.Trees ComparisonWindowTerms
  ComparisonWindowEndpoints ComparisonObserverMachine ComparisonStructuralLayout ComparisonRankedBasis
open Classical

inductive Walk {V : Type} (edge : V → V → Prop) : Nat → V → V → Prop where
  | nil (x) : Walk edge 0 x x
  | cons {x y z n} : edge x y → Walk edge n y z → Walk edge (n+1) x z

private theorem long_walk {V : Type} [Fintype V] {edge : V → V → Prop} {x z : V}
    {k : Nat} (h : Walk edge k x z) (hk : Fintype.card V ≤ k) (d : Nat) :
    ∃ n ≥ d, Walk edge n x z := by
  let L (e : Nat) := Finset.univ.filter fun u => ∃ n ≥ e, Walk edge n u z
  have mem (e : Nat) (u : V) : u ∈ L e ↔ ∃ n ≥ e, Walk edge n u z := by simp [L]
  have step (e : Nat) (u : V) : u ∈ L (e+1) ↔ ∃ v ∈ L e, edge u v := by
    constructor
    · intro hu
      obtain ⟨n, hn, path⟩ := (mem _ _).mp hu
      cases path with
      | nil => omega
      | cons first tail => exact ⟨_, (mem _ _).mpr ⟨_, by omega, tail⟩, first⟩
    · rintro ⟨v, hv, first⟩
      obtain ⟨n, hn, tail⟩ := (mem _ _).mp hv
      exact (mem _ _).mpr ⟨_, Nat.succ_le_succ hn, .cons first tail⟩
  have anti : Antitone L := by
    intro a b hab u hu
    obtain ⟨n, hn, path⟩ := (mem _ _).mp hu
    exact (mem _ _).mpr ⟨n, hab.trans hn, path⟩
  let size := Fintype.card V
  let c (i : Nat) := size - (L i).card
  have mono : Monotone c := fun _ _ hab => Nat.sub_le_sub_left (Finset.card_le_card (anti hab)) _
  have eqs {i j} (hij : i ≤ j) (hc : c i = c j) : L j = L i := by
    apply Finset.eq_of_subset_of_card_le (anti hij)
    have hi : (L i).card ≤ size := Finset.card_le_univ _
    have hj : (L j).card ≤ size := Finset.card_le_univ _
    dsimp [c] at hc
    omega
  have steady (i : Nat) (hc : c i = c (i+1)) : c (i+1) = c (i+2) := by
    have e := eqs (Nat.le_succ _) hc
    have later : L (i+2) = L (i+1) := Finset.ext fun u => by
      rw [step (i+1) u, step i u, e]
    exact congrArg (fun S : Finset V => size - S.card) later.symm
  have atSize := (mem size x).mpr ⟨_, hk, h⟩
  apply (mem _ _).mp
  rcases le_total d size with hd | hd
  · exact anti hd atSize
  · rw [eqs hd (Nat.stabilises_of_monotone mono (fun i => Nat.sub_le _ _) steady hd).symm]
    exact atSize

variable {T A : Type} (s : Trees T A Constructor) (l : Fields A)
  (Δ : Bounds) (types : List TypeVar) (modes : List ModVar)

/-- Pairs observable by a single supported type defined under the input bounds. -/
noncomputable def outcomes (x y : T) : Finset (Bool × Bool) :=
  Finset.univ.filter fun b => ∃ a, Allowed Δ types modes a ∧ pair s l a x y = b

private theorem finite_rank (x y : T) :
    ∃ m, outcomes s l Δ types modes x y ⊆ profile s l Δ types modes m x y := by
  let U := outcomes s l Δ types modes x y
  have witness (b : ↥U) : ∃ a, Allowed Δ types modes a ∧ pair s l a x y = b.val :=
    (Finset.mem_filter.mp b.property).2
  choose a ha eq using witness
  refine ⟨Finset.univ.sup (fun b => rank (a b)), fun b hb =>
    (mem_profile ..).mpr ⟨a ⟨b,hb⟩, ha _, Finset.le_sup (f := fun i => rank (a i)) (Finset.mem_univ _), eq _⟩⟩

private theorem transfer {x y u v : T} (hx : s.root x = s.root u) (hy : s.root y = s.root v)
    (ch : ∀ i, outcomes s l Δ types modes (s.child x i) (s.child y i) ⊆
      outcomes s l Δ types modes (s.child u i) (s.child v i)) :
    outcomes s l Δ types modes x y ⊆ outcomes s l Δ types modes u v := by
  choose m hm using fun i => finite_rank s l Δ types modes (s.child u i) (s.child v i)
  let M := max (m .prod) (max (m .sum) (m .fn))
  have bound (i : Constructor) : m i ≤ M := by cases i <;> dsimp [M] <;> omega
  intro b hb
  obtain ⟨a,ha,eq⟩ := (Finset.mem_filter.mp hb).2
  have incl (i : Constructor) : profile s l Δ types modes (rank a) (s.child x i) (s.child y i) ⊆
      profile s l Δ types modes M (s.child u i) (s.child v i) := by
    intro c hc
    obtain ⟨t, ht, _, et⟩ := (mem_profile ..).mp hc
    have hc' := hm i (ch i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, et⟩))
    obtain ⟨w, hw, rw', ew⟩ := (mem_profile ..).mp hc'
    exact (mem_profile ..).mpr ⟨w, hw, rw'.trans (bound i), ew⟩
  have parent := profile_transfer s l Δ types modes hx hy incl
  obtain ⟨t,ht,_,et⟩ := (mem_profile ..).mp (parent ((mem_profile ..).mpr
    ⟨a,ha,Nat.le_succ _,eq⟩))
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, ht, et⟩

variable {J : Type}

/-- The two endpoint literals include their signs in `J`. -/
structure Vertex (A J : Type) where
  leftRoot : A
  rightRoot : A
  cap : Finset (Bool × Bool)
  leftRole : J
  rightRole : J

private def vertexEquiv (A J : Type) : (A × A × Finset (Bool × Bool) × J × J) ≃ Vertex A J :=
  ⟨fun x => ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2⟩,
    fun v => (v.leftRoot,v.rightRoot,v.cap,v.leftRole,v.rightRole), fun _ => rfl, fun _ => rfl⟩

instance [Fintype A] [Fintype J] : Fintype (Vertex A J) := Fintype.ofEquiv _ (vertexEquiv A J)

/-- Sixteen observation caps, two headers, and two signed roles. -/
def cutoff (headers roles : Nat) := headers * (headers * (16 * (roles * roles)))

private theorem card_vertex [Fintype A] [Fintype J] :
    Fintype.card (Vertex A J) = cutoff (Fintype.card A) (Fintype.card J) := by
  rw [Fintype.card_congr (vertexEquiv A J).symm]
  simp [cutoff]

def Fits (v : Vertex A J) (x y : T) :=
  s.root x = v.leftRoot ∧ s.root y = v.rightRoot ∧ outcomes s l Δ types modes x y ⊆ v.cap

/-- A step follows a selected successor in both trees, carrying a signed
implication towards the left root and away from the right root. The child cap is
contained in the paired outcomes of the witnessing frame. -/
structure Step (up down : A → Constructor → J → J → Prop) (v w : Vertex A J) : Prop where
  frame : ∃ x y i, Fits s l Δ types modes v x y ∧
    s.root (s.child x i) = w.leftRoot ∧ s.root (s.child y i) = w.rightRoot ∧
    w.cap ⊆ outcomes s l Δ types modes (s.child x i) (s.child y i) ∧
    up v.leftRoot i v.leftRole w.leftRole ∧ down v.rightRoot i v.rightRole w.rightRole

/-- A synchronized excursion is written from its two outer roots to its holes. -/
abbrev Spine (up down : A → Constructor → J → J → Prop) := Walk (Step s l Δ types modes up down)

private theorem paste_one (x : T) (i : Constructor) (u : T)
    (hr : s.root u = s.root (s.child x i)) :
    ∃ y, s.root y = s.root x ∧ s.child y i = u ∧ ∀ j, j ≠ i → s.child y j = s.child x j := by
  let cs (j : Constructor) := if j = i then u else s.child x j
  obtain ⟨y,hy,cy⟩ := s.paste x cs (by intro j; by_cases h : j=i <;> simp [h, cs, hr])
  exact ⟨y,hy,by simp [cy, cs],fun j h => by simp [cy, cs, h]⟩

private theorem realize {f : T → J → Bool} {up down : A → Constructor → J → J → Prop}
    (hu : ∀ t i a b, up (s.root t) i a b → f (s.child t i) b ≤ f t a)
    (hd : ∀ t i a b, down (s.root t) i a b → f t a ≤ f (s.child t i) b)
    {n : Nat} {v z : Vertex A J} (path : Spine s l Δ types modes up down n v z)
    {u w : T} (seed : Fits s l Δ types modes z u w)
    {u' w' : T} (lu : s.root u' = z.leftRoot) (rw' : s.root w' = z.rightRoot) :
    ∃ x y x' y', Fits s l Δ types modes v x y ∧ s.Prefix n x x' ∧ s.Prefix n y y' ∧
      f u' z.leftRole ≤ f x' v.leftRole ∧ f y' v.rightRole ≤ f w' z.rightRole := by
  induction path with
  | nil => exact ⟨u,w,u',w',seed,seed.1.trans lu.symm,seed.2.1.trans rw'.symm,le_rfl,le_rfl⟩
  | @cons v mid z n e _ ih =>
    obtain ⟨xc,yc,xc',yc',fit,px,py,left,right⟩ := ih seed lu rw'
    obtain ⟨tx,ty,i,top,cx,cy,subcap,upStep,downStep⟩ := e.frame
    obtain ⟨x,hx,ex,sx⟩ := paste_one s tx i xc (fit.1.trans cx.symm)
    obtain ⟨y,hy,ey,sy⟩ := paste_one s ty i yc (fit.2.1.trans cy.symm)
    obtain ⟨x',hx',ex',sx'⟩ := paste_one s tx i xc' (((px.root s).symm.trans fit.1).trans cx.symm)
    obtain ⟨y',hy',ey',sy'⟩ := paste_one s ty i yc' (((py.root s).symm.trans fit.2.1).trans cy.symm)
    have lower : ∀ j, outcomes s l Δ types modes (s.child x j) (s.child y j) ⊆
        outcomes s l Δ types modes (s.child tx j) (s.child ty j) := by
      intro j
      by_cases h : j=i
      · subst j
        rw [ex,ey]
        exact fit.2.2.trans subcap
      · rw [sx j h, sy j h]
    have extendPrefix {a b t a' b' : T} (ra : s.root a = s.root t) (rb : s.root b = s.root t)
        (ea : s.child a i = a') (eb : s.child b i = b') (p : s.Prefix n a' b')
        (sa : ∀ j, j ≠ i → s.child a j = s.child t j)
        (sb : ∀ j, j ≠ i → s.child b j = s.child t j) : s.Prefix (n+1) a b := by
      refine ⟨ra.trans rb.symm, fun j => ?_⟩
      by_cases h : j=i
      · subst j
        rw [ea,eb]
        exact p
      · rw [sa j h,sb j h]
        exact s.prefix_refl _ _
    refine ⟨x,y,x',y',⟨hx.trans top.1,hy.trans top.2.1,
      (transfer s l Δ types modes hx hy lower).trans top.2.2⟩,
      extendPrefix hx hx' ex ex' px sx sx', extendPrefix hy hy' ey ey' py sy sy',
      left.trans ?_, le_trans ?_ right⟩
    · have h := hu x' i _ _ ((hx'.trans top.1) ▸ upStep)
      simpa only [ex'] using h
    · have h := hd y' i _ _ ((hy'.trans top.2.1) ▸ downStep)
      simpa only [ey'] using h

/-- Once a synchronized route reaches the input-only cutoff, a comparison
between its roots implies the same signed inequality for *independent*
fillings of the terminal headers. The length test does not use the radius of
the solution. -/
theorem rectangle [Fintype A] [Fintype J] {f : T → J → Bool}
    {up down : A → Constructor → J → J → Prop} {d n : Nat}
    (reads : s.Reads d f)
    (hu : ∀ t i a b, up (s.root t) i a b → f (s.child t i) b ≤ f t a)
    (hd : ∀ t i a b, down (s.root t) i a b → f t a ≤ f (s.child t i) b)
    {v z : Vertex A J} (path : Spine s l Δ types modes up down n v z)
    (long : cutoff (Fintype.card A) (Fintype.card J) ≤ n)
    (seed : ∃ u w, Fits s l Δ types modes z u w)
    (bridge : ∀ x y, Fits s l Δ types modes v x y → f x v.leftRole ≤ f y v.rightRole)
    {u w : T} (lu : s.root u = z.leftRoot) (rw' : s.root w = z.rightRoot) :
    f u z.leftRole ≤ f w z.rightRole := by
  obtain ⟨m,hm,more⟩ := long_walk path ((card_vertex (A := A) (J := J)).le.trans long) d
  obtain ⟨u₀,w₀,fit⟩ := seed
  obtain ⟨x,y,x',y',top,px,py,left,right⟩ :=
    realize s l Δ types modes hu hd more fit lu rw'
  rw [← reads.mono s hm x x' px] at left
  rw [← reads.mono s hm y y' py] at right
  exact left.trans ((bridge x y top).trans right)

open ComparisonWindowWitness ComparisonSelectedBases ComparisonWindowObservers ComparisonDefiniteTreeMachines

abbrev Label (p : SchemePreparation.Prepared) :=
  Window (Letter (typeNames p) (modeNames p)) Constructor (radius p.assumptions + 1)

abbrev Role (p : SchemePreparation.Prepared) := Slot (ComparisonSignedObservation.endpoints p) × Bool

/-- The synchronized path cutoff uses only the prepared input. -/
def preparedCutoff (p : SchemePreparation.Prepared) : Nat :=
  cutoff (rootLabelCount p) ((written (ComparisonSignedObservation.endpoints p)).card * 2)

private def signedBit (neg value : Bool) := if neg then !value else value

noncomputable def observe {p : SchemePreparation.Prepared} {d : Nat} (w : PositiveWindow p d) (t : States p)
    (j : Role p) : Bool :=
  signedBit j.2 (eval (trees p) (fields p) (inputTypeKeys p)
    ({modes := w.modes} : CompareSubstitution).mode w.bits j.1.val t)

/-- Use every signed parent/child implication of the compiled written
clauses, with the same mode action on both sides. -/
def localStep (p : SchemePreparation.Prepared) (ms : List (Nat × ModExpr)) (upward : Bool)
    (a : Label p) (i : Constructor) (parent child : Role p) : Prop :=
  ∀ b c, Clauses (Rule (ComparisonSignedObservation.endpoints p) (fields p) (inputTypeKeys p)
    ({modes := ms} : CompareSubstitution).mode) a b c →
    let x := signedBit parent.2 (b parent.1)
    let y := signedBit child.2 (c i child.1)
    if upward then y ≤ x else x ≤ y

private theorem eval_local (keys : List Nat) (ms : ModVar → ModExpr) {bits : T → Nat → Bool} {d : Nat}
    (reads : s.Reads d bits) (a : Ty) : ∃ n, s.Reads n (eval s l keys ms bits a) := by
  induction a with
  | var v =>
    refine ⟨d, fun x y h => ?_⟩
    cases v <;> simp only [eval, reads x y h, h.root s]
  | unit => exact ⟨0, fun _ _ h => congrArg l.unit h⟩
  | credit => exact ⟨0, fun _ _ h => congrArg l.credit h⟩
  | modal a m ih =>
    obtain ⟨n,hn⟩ := ih
    exact ⟨n, fun x y h => by simp only [eval, h.root s, hn x y h]⟩
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    obtain ⟨n,ha⟩ := ia
    obtain ⟨m,hb⟩ := ib
    refine ⟨max n m + 1, fun x y h => ?_⟩
    have ea := fun k => ha.mono s (Nat.le_max_left n m) _ _ (h.2 k)
    have eb := fun k => hb.mono s (Nat.le_max_right n m) _ _ (h.2 k)
    simp only [eval, h.1, ea, eb]

private theorem observe_local {p : SchemePreparation.Prepared} {d : Nat} (w : PositiveWindow p d) :
    ∃ n, (trees p).Reads n (observe w) := by
  choose n hn using fun j : Role p => eval_local (trees p) (fields p) (inputTypeKeys p)
    ({modes := w.modes} : CompareSubstitution).mode w.reads j.1.val
  refine ⟨Finset.univ.sup n, fun x y h => funext fun j => ?_⟩
  exact congrArg (signedBit j.2) ((hn j).mono (trees p) (Finset.le_sup (Finset.mem_univ j)) x y h)

/-- A shared positive solution satisfies the resulting rectangle on the actual
scheme endpoints. Only the two terminal headers are imposed on its fillings. -/
theorem prepared_rectangle {p : SchemePreparation.Prepared} {d n : Nat} (w : PositiveWindow p d)
    {v z : Vertex (Label p) (Role p)}
    (path : Spine (trees p) (fields p) p.assumptions (typeNames p) (modeNames p)
      (localStep p w.modes true) (localStep p w.modes false) n v z)
    (long : preparedCutoff p ≤ n)
    (seed : ∃ u v, Fits (trees p) (fields p) p.assumptions (typeNames p) (modeNames p) z u v)
    (ordered : ∀ b ∈ v.cap, b.1 ≤ b.2)
    {k : Nat} (key : k ∈ inputTypeKeys p)
    (left : v.leftRole.1.val = .var (.flex k)) (right : v.rightRole = v.leftRole)
    (positiveSign : v.leftRole.2 = false)
    {u t : States p} (lu : (trees p).root u = z.leftRoot) (rt : (trees p).root t = z.rightRoot) :
    observe w u z.leftRole ≤ observe w t z.rightRole := by
  obtain ⟨r,hr⟩ := observe_local w
  have valid := (canonical_clauses_iff _ (trees p) (fields p) (inputTypeKeys p)
    ({modes := w.modes} : CompareSubstitution).mode w.bits).mpr w.endpoints
  have length : cutoff (Fintype.card (Label p)) (Fintype.card (Role p)) ≤ n := by
    simpa only [preparedCutoff, rootLabelCount_eq_card, Label, Role, Slot, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_coe] using long
  apply rectangle (trees p) (fields p) p.assumptions (typeNames p) (modeNames p) hr
    (fun x i a b e => e _ _ (valid x)) (fun y i a b e => e _ _ (valid y)) path length seed _ lu rt
  intro x y h
  have link := (w.positive k key).order x y (fun a ha =>
    ordered _ (h.2.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, ha, rfl⟩)))
  simpa only [observe, right, left, positiveSign, signedBit, Bool.false_eq_true, if_false,
    eval, List.contains_iff_mem.mpr key, if_true] using link

end ModalityInference.ComparisonWindowExcursions
