import ModalityInference.ComparisonStructuralCoherence
import ModalityInference.Proofs.ComparisonStructuralLayout

/-! Function roots have a finite range condition equivalent to their future
modality coherence law. The added clauses preserve all genuine recursive
observer models, including constant observers and inconsistent contexts. -/
namespace ModalityInference.ComparisonStructuralCoherence
open ComparisonAlgebra ComparisonControls ComparisonStructuralAlignment ComparisonStructuralLayout

/-- Function comparisons retain only the future coordinates. -/
theorem coordinate_fn (c : Coordinate) (x : Bool) (m n : Mode)
    (hle : m.le (n.compose Mode.top) = true)
    (hr : c = .uniqueness → x = true) :
    coordinateValue c x m ≤ coordinateValue c x n := by
  rcases m with ⟨ml,ma,mu⟩
  rcases n with ⟨nl,na,nu⟩
  cases c <;> cases x <;> cases ml <;> cases ma <;> cases mu <;>
    cases nl <;> cases na <;> cases nu <;>
    simp_all [coordinateValue,Mode.le,Mode.compose,Mode.top]

theorem guarded_fn {Δ : Bounds} (c : Coordinate) (η : ModVar → Mode)
    (hm : c = .unaffected ∨ ModeModels Δ η)
    (m n : GuardedMode Δ) (hle : Submode Δ m.expression (.compose n.expression .top))
    (x : Bool) (hr : c = .uniqueness → x = true) :
    coordinateValue c x (m.value η) ≤ coordinateValue c x (n.value η) := by
  rcases hm with rfl | hm
  · exact le_refl _
  · apply coordinate_fn c x (m.value η) (n.value η) ?_ hr
    have h := hle.denote hm
    simpa [ModExpr.Below,ModExpr.top,ModExpr.eval,m.eval η hm,n.eval η hm] using h

theorem fn_top_below {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) :
    AlgebraSubtype Δ (.modal (.fn a.type b.type) .top) (.fn a.type b.type) := by
  apply AlgebraSubtype.trans
    (AlgebraSubtype.fn (.refl a.shaped) (.refl b.shaped) (n := .epsilon) ?_)
    (.shaped (.identity ⟨a.shaped,b.shaped⟩))
  exact .valid (fun _ _ => ⟨Mode.top,Mode.top,rfl,rfl,rfl⟩)

theorem Model.fn_true {Δ : Bounds} {s t : ComparisonShape}
    {f : LatticeHom (Order Δ (.fn s t)) Bool} {ls : List (GuardedMode Δ)} {η : ModVar → Mode}
    (h : Model f ls .uniqueness η) (htop : ∃m∈ls,m.expression = .top)
    (a : Carrier Δ s) (b : Carrier Δ t) :
    observer f (Constructor.fn.carrier a b) = true := by
  obtain ⟨m,hm,he⟩ := htop
  have hη : ModeModels Δ η := h.modeModel.resolve_left (by decide)
  have hval : m.value η = Mode.top := by
    have hv := m.eval η hη
    rw [he] at hv
    exact (Option.some.inj hv).symm
  have hact := h.action (Constructor.fn.carrier a b) m hm
  have htrue : observer f (m.act (Constructor.fn.carrier a b)) = true := by
    simpa only [hval,coordinateValue,Mode.top,Bool.not_false,Bool.or_true] using hact
  apply observer_mono f (b := Constructor.fn.carrier a b) ?_ htrue
  change AlgebraSubtype Δ (.modal (.fn a.type b.type) m.expression) (.fn a.type b.type)
  rw [he]
  exact fn_top_below a b

theorem coordinateTest_correct {c : Coordinate} {world : Nat → Bool}
    (hfirst : world (choiceAtom 1) = (coordinateBits c).1)
    (hsecond : world (choiceAtom 2) = (coordinateBits c).2) (d : Coordinate) :
    (coordinateTest d).eval world = true ↔ d = c := by
  cases c <;> cases d <;>
    simp [coordinateTest, coordinateBits, BoolExpr.equal, BoolExpr.eval, hfirst, hsecond]

theorem rangeClause_correct {c : Coordinate} {world : Nat → Bool}
    (hfirst : world (choiceAtom 1) = (coordinateBits c).1)
    (hsecond : world (choiceAtom 2) = (coordinateBits c).2)
    (takeLeft : Bool) (child : Nat → Nat) (range : Bool → Prop)
    (hf : world (child (choiceAtom 3)) = true ↔ range false)
    (ht : world (child (choiceAtom 4)) = true ↔ range true) :
    (rangeClause takeLeft child).eval world = true ↔
      (c = .uniqueness → ∀x, range x → signed takeLeft x = true) := by
  have hc := coordinateTest_correct hfirst hsecond .uniqueness
  cases takeLeft <;> cases c <;>
    simp_all [rangeClause, signed, BoolExpr.eval, Bool.forall_bool]
  · exact Bool.eq_false_iff.trans (not_congr hf)
  · exact Bool.eq_false_iff.trans (not_congr ht)

theorem rangeClause_transfer {Δ : Bounds} {c : Coordinate} {η : ModVar → Mode}
    {world : Nat → Bool} (hfirst : world (choiceAtom 1) = (coordinateBits c).1)
    (hsecond : world (choiceAtom 2) = (coordinateBits c).2)
    (takeLeft : Bool) (child : Nat → Nat) (range : Bool → Prop)
    (hf : world (child (choiceAtom 3)) = true ↔ range false)
    (ht : world (child (choiceAtom 4)) = true ↔ range true)
    (hc : (rangeClause takeLeft child).eval world = true)
    (hη : c = .unaffected ∨ ModeModels Δ η)
    (m n : GuardedMode Δ) (hle : Submode Δ m.expression (.compose n.expression .top))
    (x : Bool) (hx : range x) :
    coordinateValue c (signed takeLeft x) (m.value η) ≤
      coordinateValue c (signed takeLeft x) (n.value η) := by
  apply guarded_fn c η hη m n hle
  intro hu
  exact ((rangeClause_correct hfirst hsecond takeLeft child range hf ht).mp hc) hu x hx

theorem rangeClause_left {Δ : Bounds} {s t : ComparisonShape}
    {f : LatticeHom (Order Δ (.fn s t)) Bool} {g : LatticeHom (Order Δ s) Bool}
    {ls : List (GuardedMode Δ)} {c d : Coordinate} {η θ : ModVar → Mode}
    {basis childBasis : Basis} {world : Nat → Bool} {child : Nat → Nat}
    (hm : Model f ls c η) (htop : ∃m∈ls,m.expression = .top)
    (hp : Observes basis f c η world) (hc : Observes childBasis g d θ (world ∘ child))
    (b : Carrier Δ t)
    (hv : ∀a b, observer f (Constructor.fn.carrier a b) = !(observer g a)) :
    (rangeClause true child).eval world = true := by
  apply (rangeClause_correct hp.first hp.second true child
    (fun x => ∃a, observer g a = x) hc.falseRange hc.trueRange).mpr
  rintro rfl x ⟨a,ha⟩
  change (!x) = true
  rw [←ha]
  exact (hv a b).symm.trans (Model.fn_true hm htop a b)

theorem rangeClause_right {Δ : Bounds} {s t : ComparisonShape}
    {f : LatticeHom (Order Δ (.fn s t)) Bool} {g : LatticeHom (Order Δ t) Bool}
    {ls : List (GuardedMode Δ)} {c d : Coordinate} {η θ : ModVar → Mode}
    {basis childBasis : Basis} {world : Nat → Bool} {child : Nat → Nat}
    (hm : Model f ls c η) (htop : ∃m∈ls,m.expression = .top)
    (hp : Observes basis f c η world) (hc : Observes childBasis g d θ (world ∘ child))
    (a : Carrier Δ s)
    (hv : ∀a b, observer f (Constructor.fn.carrier a b) = observer g b) :
    (rangeClause false child).eval world = true := by
  apply (rangeClause_correct hp.first hp.second false child
    (fun x => ∃b, observer g b = x) hc.falseRange hc.trueRange).mpr
  rintro rfl x ⟨b,hb⟩
  change x = true
  rw [←hb]
  exact (hv a b).symm.trans (Model.fn_true hm htop a b)

theorem complete_fn {Δ : Bounds} (c : Coordinate) (η : ModVar → Mode)
    (hm : c = .unaffected ∨ ModeModels Δ η) (m n : ModExpr)
    (hle : Submode Δ m (.compose n .top))
    (x : Bool) (hr : c = .uniqueness → x = true) :
    coordinateValue c x (m.complete η) ≤ coordinateValue c x (n.complete η) := by
  rcases hm with rfl | hm
  · exact le_refl _
  · obtain ⟨a,b,ha,hb,hle⟩ := hle.denote hm
    rw [←ModExpr.complete_of_eval ha, ←ModExpr.complete_of_eval hb] at hle
    exact coordinate_fn c x (m.complete η) (n.complete η) hle hr

theorem rangeClause_transfer_complete {Δ : Bounds} {c : Coordinate} {η : ModVar → Mode}
    {world : Nat → Bool} (hfirst : world (choiceAtom 1) = (coordinateBits c).1)
    (hsecond : world (choiceAtom 2) = (coordinateBits c).2)
    (takeLeft : Bool) (child : Nat → Nat) (range : Bool → Prop)
    (hf : world (child (choiceAtom 3)) = true ↔ range false)
    (ht : world (child (choiceAtom 4)) = true ↔ range true)
    (hc : (rangeClause takeLeft child).eval world = true)
    (hη : c = .unaffected ∨ ModeModels Δ η)
    (m n : ModExpr) (hle : Submode Δ m (.compose n .top))
    (x : Bool) (hx : range x) :
    coordinateValue c (signed takeLeft x) (m.complete η) ≤
      coordinateValue c (signed takeLeft x) (n.complete η) := by
  apply complete_fn c η hη m n hle
  intro hu
  exact ((rangeClause_correct hfirst hsecond takeLeft child range hf ht).mp hc) hu x hx

/-- The finite range clause is exactly the function transfer condition over
the original guarded scalar relation, not a strengthening of that relation. -/
theorem rangeClause_transfer_iff {Δ : Bounds} {c : Coordinate} {η : ModVar → Mode}
    {world : Nat → Bool} (hfirst : world (choiceAtom 1) = (coordinateBits c).1)
    (hsecond : world (choiceAtom 2) = (coordinateBits c).2)
    (takeLeft : Bool) (child : Nat → Nat) (range : Bool → Prop)
    (hf : world (child (choiceAtom 3)) = true ↔ range false)
    (ht : world (child (choiceAtom 4)) = true ↔ range true)
    (hη : c = .unaffected ∨ ModeModels Δ η) :
    (rangeClause takeLeft child).eval world = true ↔
      ∀m n, Submode Δ m (.compose n .top) → ∀x, range x →
        coordinateValue c (signed takeLeft x) (m.complete η) ≤
          coordinateValue c (signed takeLeft x) (n.complete η) := by
  constructor
  · intro hc m n hmn x hx
    exact rangeClause_transfer_complete hfirst hsecond takeLeft child range hf ht hc hη m n hmn x hx
  · intro h
    apply (rangeClause_correct hfirst hsecond takeLeft child range hf ht).mpr
    rintro rfl x hx
    have htop : Submode Δ .top (.compose .epsilon .top) :=
      .valid (fun _ _ => ⟨Mode.top,Mode.top,rfl,rfl,rfl⟩)
    have he := h .top .epsilon htop x hx
    simpa [coordinateValue,ModExpr.complete,ModExpr.top,ModExpr.epsilon,
      Mode.top,Mode.identity,Bool.le_iff_imp] using he

def ClosedRange (c : Coordinate) (range : Bool → Prop) : Prop :=
  match c with
  | .unaffected => True
  | .locality | .affinity => range true → range false
  | .uniqueness => range false → range true

theorem closedRange_iff (c : Coordinate) (range : Bool → Prop) :
    ClosedRange c range ↔ ∀x, range x → ∀m, range (coordinateValue c x m) := by
  cases c with
  | unaffected => simp [ClosedRange,coordinateValue]
  | locality =>
    constructor
    · intro h x hx m
      cases x <;> cases hm : m.isLocal <;> simp_all [ClosedRange,coordinateValue]
    · intro h hx
      exact h true hx Mode.bottom
  | affinity =>
    constructor
    · intro h x hx m
      cases x <;> cases hm : m.once <;> simp_all [ClosedRange,coordinateValue]
    · intro h hx
      exact h true hx Mode.bottom
  | uniqueness =>
    constructor
    · intro h x hx m
      cases x <;> cases hm : m.unique <;> simp_all [ClosedRange,coordinateValue]
    · intro h hx
      exact h false hx Mode.top

theorem rangeClosure_correct {c : Coordinate} {world : Nat → Bool}
    (hfirst : world (choiceAtom 1) = (coordinateBits c).1)
    (hsecond : world (choiceAtom 2) = (coordinateBits c).2)
    (range : Bool → Prop)
    (hf : world (choiceAtom 3) = true ↔ range false)
    (ht : world (choiceAtom 4) = true ↔ range true) :
    rangeClosure.eval world = true ↔ ClosedRange c range := by
  cases c <;> cases hf' : world (choiceAtom 3) <;> cases ht' : world (choiceAtom 4) <;>
    simp_all [rangeClosure,ClosedRange,coordinateTest,coordinateBits,BoolExpr.equal,
      BoolExpr.eval,rangeAtom]

theorem Model.constant {Δ shape f ls c η} (h : @Model Δ shape f ls c η)
    {m : GuardedMode Δ} (hm : m∈ls) {p : Mode} (he : m.expression = .const p)
    (a : Carrier Δ shape) :
    observer f (m.act a) = coordinateValue c (observer f a) p := by
  rw [h.action a m hm]
  rcases h.modeModel with rfl | hη
  · rfl
  · have hv := m.eval η hη
    rw [he] at hv
    have he : p = m.value η := Option.some.inj hv
    rw [he]

theorem Model.closedRange {Δ shape f ls c η} (h : @Model Δ shape f ls c η)
    (hbottom : ∃m∈ls,m.expression = .const Mode.bottom)
    (htop : ∃m∈ls,m.expression = .top) :
    ClosedRange c (fun x => ∃a, observer f a = x) := by
  cases c with
  | unaffected => trivial
  | locality =>
    rintro ⟨a,ha⟩
    obtain ⟨m,hm,he⟩ := hbottom
    exact ⟨m.act a, by simpa [coordinateValue,Mode.bottom] using Model.constant h hm he a⟩
  | affinity =>
    rintro ⟨a,ha⟩
    obtain ⟨m,hm,he⟩ := hbottom
    exact ⟨m.act a, by simpa [coordinateValue,Mode.bottom] using Model.constant h hm he a⟩
  | uniqueness =>
    rintro ⟨a,ha⟩
    obtain ⟨m,hm,he⟩ := htop
    exact ⟨m.act a, by simpa [coordinateValue,Mode.top] using Model.constant h hm he a⟩

theorem rangeClosure_observer {Δ shape basis f ls c η world}
    (h : @Model Δ shape f ls c η) (ho : Observes basis f c η world)
    (hbottom : ∃m∈ls,m.expression = .const Mode.bottom)
    (htop : ∃m∈ls,m.expression = .top) : rangeClosure.eval world = true :=
  (rangeClosure_correct ho.first ho.second _ ho.falseRange ho.trueRange).mpr
    (Model.closedRange h hbottom htop)

private theorem implies_true (a b : Bool) : ((!a) || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

theorem Observes.range_value {Δ shape basis f c η world}
    (h : @Observes Δ shape basis f c η world) (x : Bool) :
    world (choiceAtom (if x then 4 else 3)) = true ↔ ∃a, observer f a = x := by
  cases x
  · exact h.falseRange
  · exact h.trueRange

theorem rangeInclusion_correct (k : Constructor) (takeLeft : Bool) (child : Nat → Nat)
    (world : Nat → Bool) (parentRange childRange : Bool → Prop)
    (hp : ∀x,world (choiceAtom (if x then 4 else 3)) = true ↔ parentRange x)
    (hc : ∀x,world (child (choiceAtom (if x then 4 else 3))) = true ↔ childRange x) :
    (rangeInclusion k takeLeft child).eval world = true ↔
      ∀x,childRange x → parentRange (constructorSigned k takeLeft x) := by
  simp only [rangeInclusion,rangeAtom,BoolExpr.eval,Bool.and_eq_true,implies_true,Bool.forall_bool]
  exact and_congr (imp_congr (hc false) (hp _)) (imp_congr (hc true) (hp _))

theorem rangeInclusion_left {Δ s t k basis childBasis f g c d η θ world child}
    (hp : @Observes Δ (k.shape s t) basis f c η world)
    (hc : @Observes Δ s childBasis g d θ (world ∘ child))
    (b : Carrier Δ t)
    (hv : ∀a b,observer f (k.carrier a b) =
      ComparisonStructuralObservers.leftSign k.kind (observer g a)) :
    (rangeInclusion k true child).eval world = true := by
  apply (rangeInclusion_correct k true child world _ _
    (Observes.range_value hp) (Observes.range_value hc)).mpr
  rintro x ⟨a,ha⟩
  refine ⟨k.carrier a b, ?_⟩
  rw [hv,ha]
  cases k <;> rfl

theorem rangeInclusion_right {Δ s t k basis childBasis f g c d η θ world child}
    (hp : @Observes Δ (k.shape s t) basis f c η world)
    (hc : @Observes Δ t childBasis g d θ (world ∘ child))
    (a : Carrier Δ s)
    (hv : ∀a b,observer f (k.carrier a b) = observer g b) :
    (rangeInclusion k false child).eval world = true := by
  apply (rangeInclusion_correct k false child world _ _
    (Observes.range_value hp) (Observes.range_value hc)).mpr
  rintro x ⟨b,hb⟩
  refine ⟨k.carrier a b, ?_⟩
  rw [hv,hb]
  cases k <;> rfl

private theorem all_true (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all es).eval world = true ↔ ∀e∈es,e.eval world = true := by
  induction es <;> simp_all [BoolExpr.all,BoolExpr.eval]

private theorem equal_true (a b : BoolExpr) (world : Nat → Bool) :
    (BoolExpr.equal a b).eval world = true ↔ a.eval world = b.eval world := by
  cases ha : a.eval world <;> cases hb : b.eval world <;>
    simp_all [BoolExpr.equal,BoolExpr.eval]

theorem headCoherence_correct (basis : Basis) (world : Nat → Bool) :
    (headCoherence basis).eval world = true ↔
      ∀i (hi : i<basis.heads.length),
        world (headAtom i) = world (headAtom (basis.heads.idxOf basis.heads[i])) := by
  rw [headCoherence,all_true]
  constructor
  · intro h i hi
    apply (equal_true (.atom (headAtom i))
      (.atom (headAtom (basis.heads.idxOf basis.heads[i]))) world).mp
    apply h
    exact List.mem_iff_getElem.mpr ⟨i,by simpa using hi,by simp⟩
  · intro h e he
    obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp he
    simp only [List.getElem_mapIdx]
    exact (equal_true _ _ world).mpr (h i (by simpa using hi))

theorem headCoherence_observer {Δ shape basis f c η world}
    (h : @Observes Δ shape basis f c η world) : (headCoherence basis).eval world = true := by
  apply (headCoherence_correct basis world).mpr
  intro i hi
  exact (h.heads i hi).trans (h.head_mem (List.getElem_mem hi)).symm

theorem Realized.theory {Δ : Bounds} {ls : List (GuardedMode Δ)}
    {layout : Layout} {f : LatticeHom (Order Δ layout.shape) Bool}
    {c : Coordinate} {η : ModVar → Mode} {world : Nat → Bool}
    (h : Realized Δ ls layout f c η world) {modes : List ModVar}
    (hv : Valid Δ modes layout) (hbottom : ∃m∈ls,m.expression = .const Mode.bottom)
    (htop : ∃m∈ls,m.expression = .top) :
    (theory layout).eval world = true := by
  induction h with
  | leaf hm ho =>
    change ((headCoherence _).eval _ && rangeClosure.eval _) = true
    simp only [headCoherence_observer ho,rangeClosure_observer hm ho hbottom htop,Bool.and_self]
  | @left k basis left right f c η world child θ g hm ho hside hi hvalue subtree ih =>
    cases hv with
    | fork hh hnames hl hr hcells =>
      have hs := ih hl
      have hheads := headCoherence_observer ho
      have hrange := rangeClosure_observer hm ho hbottom htop
      have hinc := rangeInclusion_left ho subtree.observes
        (represented (hr.heads right.basis.head (by simp [Basis.heads]))) hvalue
      have hc : (childClause k true leftAtom).eval world = true := by
        cases k with
        | prod | sum => rfl
        | fn =>
          exact rangeClause_left hm htop ho subtree.observes
            (represented (hr.heads right.basis.head (by simp [Basis.heads])))
            (by simpa only [Constructor.kind,ComparisonStructuralObservers.leftSign] using hvalue)
      simp only [ComparisonStructuralCoherence.theory,BoolExpr.eval,hside,Bool.not_true,
        Bool.false_and,Bool.or_false,rename_eval,hc,hs,hheads,hrange,hinc,Bool.and_self]
  | @right k basis left right f c η world child θ g hm ho hside hi hvalue subtree ih =>
    cases hv with
    | fork hh hnames hl hr hcells =>
      have hs := ih hr
      have hheads := headCoherence_observer ho
      have hrange := rangeClosure_observer hm ho hbottom htop
      have hinc := rangeInclusion_right ho subtree.observes
        (represented (hl.heads left.basis.head (by simp [Basis.heads]))) hvalue
      have hc : (childClause k false rightAtom).eval world = true := by
        cases k with
        | prod | sum => rfl
        | fn =>
          exact rangeClause_right hm htop ho subtree.observes
            (represented (hl.heads left.basis.head (by simp [Basis.heads]))) hvalue
      simp only [ComparisonStructuralCoherence.theory,BoolExpr.eval,hside,Bool.false_and,Bool.not_false,
        Bool.or_false,Bool.false_or,rename_eval,hc,hs,hheads,hrange,hinc,Bool.and_self]

theorem theory_heads {layout world} (h : (theory layout).eval world = true) :
    (headCoherence layout.basis).eval world = true := by
  cases layout <;> simp only [theory,BoolExpr.eval,Bool.and_eq_true] at h <;> exact h.1

theorem theory_range {layout world} (h : (theory layout).eval world = true) :
    rangeClosure.eval world = true := by
  cases layout <;> simp only [theory,BoolExpr.eval,Bool.and_eq_true] at h
  · exact h.2
  · exact h.2.1

theorem theory_left_parts {k basis left right world}
    (hside : world (choiceAtom 0) = true)
    (h : (theory (.fork k basis left right)).eval world = true) :
    rangeClosure.eval world = true ∧
      (childClause k true leftAtom).eval world = true ∧
      (rangeInclusion k true leftAtom).eval world = true ∧
      (theory left).eval (world ∘ leftAtom) = true := by
  simp [theory,BoolExpr.eval,hside,rename_eval] at h
  exact h.2

theorem theory_right_parts {k basis left right world}
    (hside : world (choiceAtom 0) = false)
    (h : (theory (.fork k basis left right)).eval world = true) :
    rangeClosure.eval world = true ∧
      (childClause k false rightAtom).eval world = true ∧
      (rangeInclusion k false rightAtom).eval world = true ∧
      (theory right).eval (world ∘ rightAtom) = true := by
  simp [theory,BoolExpr.eval,hside,rename_eval] at h
  exact h.2

theorem theory_left {k basis left right world}
    (hside : world (choiceAtom 0) = true)
    (h : (theory (.fork k basis left right)).eval world = true) :
    (childClause k true leftAtom).eval world = true ∧
      (theory left).eval (world ∘ leftAtom) = true := by
  have hh := theory_left_parts hside h
  exact ⟨hh.2.1,hh.2.2.2⟩

theorem theory_right {k basis left right world}
    (hside : world (choiceAtom 0) = false)
    (h : (theory (.fork k basis left right)).eval world = true) :
    (childClause k false rightAtom).eval world = true ∧
      (theory right).eval (world ∘ rightAtom) = true := by
  have hh := theory_right_parts hside h
  exact ⟨hh.2.1,hh.2.2.2⟩

theorem run_complete {assumptions endpoints layout q}
    (hq : query assumptions endpoints layout = some q) :
    ∃threshold output, ∀fuel≥threshold,
      run fuel assumptions endpoints layout = .success output := by
  obtain ⟨threshold,output,he⟩ := CompactCNF.toCNF_complete (.and q (theory layout)) true
  exact ⟨threshold,output,fun fuel hf => by simp only [run,hq]; exact he fuel hf⟩

theorem run_correct {fuel assumptions endpoints layout output}
    (hr : run fuel assumptions endpoints layout = .success output) :
    ∃q, query assumptions endpoints layout = some q ∧
      ∀world, CNFHolds world output ↔
        q.eval world = true ∧ (theory layout).eval world = true := by
  cases hq : query assumptions endpoints layout <;> simp only [run,hq] at hr
  · cases hr
  · refine ⟨_,rfl,fun world => ?_⟩
    simpa only [BoolExpr.eval,Bool.and_eq_true] using CompactCNF.toCNF_correct hr world

theorem run_realized {Δ : Bounds} {names modes fixed layout}
    (hb : Based names modes fixed layout)
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (fixed v))
    {endpoints : ComparisonShape → List (CompareTy × CompareTy)}
    (hinput : ∀s,∀pair∈endpoints s, AlgebraSubtype Δ pair.1 pair.2)
    {fuel output} (hr : run fuel Δ endpoints layout = .success output)
    (f : LatticeHom (Order Δ layout.shape) Bool) :
    ∃c η world, CNFHolds world output ∧
      Realized Δ (labels Δ modes) layout f c η world := by
  have hv := hb.valid hs
  let anchor := represented (hv.heads layout.basis.head (by simp [Basis.heads]))
  obtain ⟨c,η,hm⟩ := observer_model f anchor (labels Δ modes)
  obtain ⟨q,hq,hqcorrect⟩ := run_correct hr
  obtain ⟨world,_,hw,htree⟩ := query_realized (labels_tests Δ modes) (labels_support Δ modes)
    (fun b => labels_basis Δ b) hinput hv hq f hm
  have htop : ∃m∈labels Δ modes,m.expression = .top :=
    labels_mem.mpr (by simp [labelExpressions,tests,ModExpr.top])
  have hbottom : ∃m∈labels Δ modes,m.expression = .const Mode.bottom :=
    labels_mem.mpr (by simp [labelExpressions])
  exact ⟨c,η,world,(hqcorrect world).mpr ⟨hw,Realized.theory htree hv hbottom htop⟩,htree⟩

/-- Function range constraints retain every genuine recursive observer model.
Compilation keeps the original whole endpoint constraints at every node. -/
theorem selected_run_complete {Δ : Bounds} {shapeLayout : ComparisonShapeSelectors.Layout}
    {names modes fixed s branch}
    (hbranch : branch∈ComparisonSelectedBases.bases shapeLayout names modes fixed s)
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (fixed v))
    (endpoints : ComparisonShape → List (CompareTy × CompareTy))
    (hforms : ∀s b, ComparisonStructuralBasis.basis names modes fixed s = some b →
      ∀pair∈endpoints s, LatticeForm b.types pair.1 ∧ LatticeForm b.types pair.2)
    (hinput : ∀s,∀pair∈endpoints s, AlgebraSubtype Δ pair.1 pair.2) :
    ∃layout threshold output, selected names modes fixed branch = some layout ∧
      layout.shape = branch.shape ∧ layout.basis = branch.basis ∧
      (∀fuel≥threshold, run fuel Δ endpoints layout = .success output) ∧
      ∀f : LatticeHom (Order Δ layout.shape) Bool,
        ∃c η world, CNFHolds world output ∧
          Realized Δ (labels Δ modes) layout f c η world := by
  obtain ⟨layout,hl,hshape,hbasis,hb⟩ := selected_complete hbranch
  obtain ⟨q,hq⟩ := hb.query_complete Δ endpoints hforms
  obtain ⟨threshold,output,hr⟩ := run_complete hq
  exact ⟨layout,threshold,output,hl,hshape,hbasis,hr,
    fun f => run_realized hb hs hinput (hr threshold (le_refl _)) f⟩

end ModalityInference.ComparisonStructuralCoherence
