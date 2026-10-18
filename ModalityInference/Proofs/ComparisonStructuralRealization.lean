import ModalityInference.Proofs.ComparisonStructuralWorld
import ModalityInference.Proofs.ComparisonStructuralEndpointValues

/-! Candidate sorted observers are reconstructed from finite node values and
genuine child observers. Their guarded transition, declared whole bounds, and
global range are certified before exposing the resulting lattice observer. -/
namespace ModalityInference.ComparisonStructuralRealization
open ComparisonAlgebra ComparisonControls ComparisonStructuralLayout ComparisonStructuralWorld
  ComparisonStructuralCoherence ComparisonShapedObserverGluing ComparisonStructuralLattice

private def constantObserver {Δ : Bounds} {shape : ComparisonShape} (x : Bool) :
    LatticeHom (Order Δ shape) Bool where
  toFun _ := x
  map_sup' _ _ := by simp
  map_inf' _ _ := by simp

noncomputable def constantChild {Δ : Bounds} {shape : ComparisonShape} (x : Bool) : Child Δ shape where
  observer := constantObserver x
  transition := ComparisonCoordinateTransition.transition .unaffected (fun _=>Mode.identity) (.inl rfl)
  action m hm a ha := by
    rw [booleanValue_represented _ a ha,
      booleanValue_represented _ (.modal a m) (representable_modal ha hm)]
    rfl

@[simp] theorem constantChild_value {Δ shape} (x : Bool) {a : CompareTy}
    (ha : Representable Δ shape a) : booleanValue (constantChild (Δ:=Δ) (shape:=shape) x).observer a=x := by
  rw [booleanValue_represented _ a ha]
  rfl

@[simp] theorem constantChild_range {Δ shape} (x y : Bool)
    (h : (constantChild (Δ:=Δ) (shape:=shape) x).Range y) : y=x := by
  obtain ⟨a,ha⟩ := h
  exact ha.symm

structure Realizes (Δ : Bounds) (names : List ModVar) (shape : ComparisonShape)
    (basis : Basis) (world : Nat → Bool) where
  view : View Δ names basis world
  child : Child Δ shape
  transition : ∀m x,child.transition.apply m x=
    coordinateValue view.coordinate x (m.complete (modes names world))
  types : ∀i (hi : i<basis.types.length),world (basisAtom i)=booleanValue child.observer basis.types[i]
  heads : ∀i (hi : i<basis.heads.length),world (headAtom i)=booleanValue child.observer basis.heads[i]
  ranges : ∀x,child.Range x→ range world x

noncomputable def Data.child {Δ shape} (d : Data Δ shape) (hr : Resolved Δ shape)
    (hc : Coherent d) (hb : BoundsHold d) (hΔ : Δ.TypeBoundsDefined) : Child Δ shape where
  observer := d.observer hr hc hb hΔ
  transition := d.transition
  action m hm a ha := by
    rw [d.observer_value hr hc hb hΔ ha,
      d.observer_value hr hc hb hΔ (representable_modal ha hm)]
    rfl

theorem data_realizes {Δ names shape basis world}
    (view : View Δ names basis world) (hm : basis.modes=names)
    (hrep : ∀a∈basis.heads,Representable Δ shape a)
    (d : Data Δ shape) (hr : Resolved Δ shape) (hc : Coherent d)
    (hb : BoundsHold d) (hΔ : Δ.TypeBoundsDefined)
    (ht : ∀m x,d.transition.apply m x=
      coordinateValue view.coordinate x (m.complete (modes names world)))
    (hh : ∀i (hi : i<basis.heads.length),world (headAtom i)=d.value basis.heads[i])
    (hvalues : ∀a,Representable Δ shape a→ range world (d.value a)) :
    Nonempty (Realizes Δ names shape basis world) := by
  let g := Data.child d hr hc hb hΔ
  have hvalue {a} (ha : Representable Δ shape a) : booleanValue g.observer a=d.value a :=
    d.observer_value hr hc hb hΔ ha
  refine ⟨⟨view,g,ht,?_,?_,?_⟩⟩
  · intro i hi
    exact (view.basis_value hm d.value (fun _ _=>rfl) (fun _ _=>rfl) hh (fun a m=>ht m (d.value a)) i hi).trans
      (hvalue (ComparisonStructuralNode.basis_representable basis hrep _ (List.getElem_mem hi))).symm
  · intro i hi
    exact (hh i hi).trans (hvalue (hrep _ (List.getElem_mem hi))).symm
  · intro x hx
    obtain ⟨a,rfl⟩ := hx
    have he : ComparisonAlgebra.observer g.observer a=d.value a.type := by rfl
    exact he.symm ▸ hvalues a.type ⟨a.shaped,a.defined,a.shape_eq⟩

theorem Data.value_range {Δ shape} (d : Data Δ shape) (hr : Resolved Δ shape)
    (r : Bool → Prop) (hv : ∀v,r (d.atom v)) (hu : r d.unitValue) (hcredit : r d.creditValue)
    (hm : ∀m x,r x→ r (d.transition.apply m x))
    (hc : ∀k,Root k shape→ ∀a b,Representable Δ (leftShape shape) a→
      Representable Δ (rightShape shape) b→ r (branchValue (d.branch k) k a b))
    {a : CompareTy} (ha : Representable Δ shape a) : r (d.value a) := by
  induction a with
  | var v => exact hv v
  | unit => exact hu
  | credit => exact hcredit
  | prod a b _ _ =>
    obtain ⟨hk,hal,har⟩ := hr.children .prod ha
    exact hc .prod hk a b hal har
  | sum a b _ _ =>
    obtain ⟨hk,hal,har⟩ := hr.children .sum ha
    exact hc .sum hk a b hal har
  | fn a b _ _ =>
    obtain ⟨hk,hal,har⟩ := hr.children .fn ha
    exact hc .fn hk a b hal har
  | modal a m ih =>
    exact hm m _ (ih ⟨ha.1,(CompareTy.definedUnder_modal_iff.mp ha.2.1).1,ha.2.2⟩)
  | join a b iha ihb =>
    have hl := iha ha.left
    have hr := ihb ha.right
    change r (d.value a || d.value b)
    cases he : d.value a <;> simp_all
  | meet a b iha ihb =>
    have hl := iha ha.left
    have hr := ihb ha.right
    change r (d.value a && d.value b)
    cases he : d.value a <;> simp_all

def lookup (basis : Basis) (world : Nat → Bool) (t : CompareTy) : Bool :=
  if t∈basis.heads then headValue basis world t else headValue basis world basis.head

theorem lookup_mem {basis world t} (ht : t∈basis.heads) :
    lookup basis world t=headValue basis world t := by simp [lookup,ht]

theorem View.lookup_range {Δ names basis world} (h : View Δ names basis world) (t : CompareTy) :
    range world (lookup basis world t) := by
  unfold lookup
  split
  next ht => exact h.head_range ht
  next => exact h.head_range (by simp [Basis.heads])

noncomputable def nodeData {Δ names shape basis world} (view : View Δ names basis world)
    (branch : Kind → Branch Δ shape) : Data Δ shape where
  transition := ComparisonCoordinateTransition.transition view.coordinate (modes names world) view.scalar
  atom v := lookup basis world (.var v)
  unitValue := lookup basis world .unit
  creditValue := lookup basis world .credit
  branch := branch

theorem root_kind {k : Constructor} {s t : ComparisonShape} {other : Kind}
    (h : Root other (k.shape s t)) : other=k.kind := by
  cases k <;> cases other <;> simp_all [Root,leftShape,rightShape,Kind.shape,Constructor.shape,Constructor.kind]

private theorem all_eval (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all es).eval world=true ↔ ∀e∈es,e.eval world=true := by
  induction es <;> simp_all [BoolExpr.all,BoolExpr.eval]

private theorem equal_eval (a b : BoolExpr) (world : Nat → Bool) :
    (BoolExpr.equal a b).eval world=true ↔ a.eval world=b.eval world := by
  cases ha : a.eval world <;> cases hb : b.eval world <;>
    simp_all [BoolExpr.equal,BoolExpr.eval]

theorem Realizes.type_mem {Δ names shape basis world} (h : Realizes Δ names shape basis world)
    {a : CompareTy} (ha : a∈basis.types) :
    world (basisAtom (basis.types.idxOf a))=booleanValue h.child.observer a := by
  have hi := List.idxOf_lt_length_of_mem ha
  have he : basis.types[basis.types.idxOf a]=a := by
    simpa only [List.idxOf,beq_iff_eq] using
      (List.findIdx_getElem (xs:=basis.types) (p:=(·==a)) (w:=hi))
  exact (h.types _ hi).trans (congrArg (booleanValue h.child.observer) he)

theorem links_left_value {Δ names shape world k basis left right}
    (child : Realizes Δ names shape left (world ∘ leftAtom))
    (h : (links k basis left right true).eval world=true)
    {a b : CompareTy} (ha : a∈left.types) (hb : b∈right.types) :
    headValue basis world (k.op a b)=
      ComparisonStructuralObservers.leftSign k.kind (booleanValue child.child.observer a) := by
  have hh := (all_eval _ _).mp h _ (List.mem_flatMap.mpr
    ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩)
  have he := (equal_eval _ _ world).mp hh
  have hc := child.type_mem ha
  change world (leftAtom (basisAtom (left.types.idxOf a)))=booleanValue child.child.observer a at hc
  cases k <;> simpa [Constructor.dual,Constructor.kind,headValue,BoolExpr.eval,
    ComparisonStructuralObservers.leftSign,hc] using he

theorem links_right_value {Δ names shape world k basis left right}
    (child : Realizes Δ names shape right (world ∘ rightAtom))
    (h : (links k basis left right false).eval world=true)
    {a b : CompareTy} (ha : a∈left.types) (hb : b∈right.types) :
    headValue basis world (k.op a b)=booleanValue child.child.observer b := by
  have hh := (all_eval _ _).mp h _ (List.mem_flatMap.mpr
    ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩)
  have he := (equal_eval _ _ world).mp hh
  have hc := child.type_mem hb
  change world (rightAtom (basisAtom (right.types.idxOf b)))=booleanValue child.child.observer b at hc
  simpa [headValue,BoolExpr.eval,hc] using he

def leftBranch {Δ s t} (k : Constructor) (g : Child Δ s) : Branch Δ (k.shape s t) := by
  cases k <;> exact .inl g

def rightBranch {Δ s t} (k : Constructor) (g : Child Δ t) : Branch Δ (k.shape s t) := by
  cases k <;> exact .inr g

theorem leftBranch_value {Δ s t} (k : Constructor) (g : Child Δ s) (a b : CompareTy) :
    branchValue (leftBranch (t:=t) k g) k.kind a b=
      ComparisonStructuralObservers.leftSign k.kind (booleanValue g.observer a) := by cases k <;> rfl

theorem rightBranch_value {Δ s t} (k : Constructor) (g : Child Δ t) (a b : CompareTy) :
    branchValue (rightBranch (s:=s) k g) k.kind a b=booleanValue g.observer b := by cases k <;> rfl

@[simp] theorem leftBranch_transition {Δ s t} (k : Constructor) (g : Child Δ s) :
    branchTransition (leftBranch (t:=t) k g)=g.transition := by cases k <;> rfl

@[simp] theorem leftBranch_range {Δ s t} (k : Constructor) (g : Child Δ s) (x : Bool) :
    branchRange (leftBranch (t:=t) k g) x↔g.Range x := by cases k <;> rfl

@[simp] theorem rightBranch_transition {Δ s t} (k : Constructor) (g : Child Δ t) :
    branchTransition (rightBranch (s:=s) k g)=g.transition := by cases k <;> rfl

@[simp] theorem rightBranch_range {Δ s t} (k : Constructor) (g : Child Δ t) (x : Bool) :
    branchRange (rightBranch (s:=s) k g) x↔g.Range x := by cases k <;> rfl

theorem fork_left_coherent {Δ names s t basis childBasis world k}
    (view : View Δ names basis world)
    (child : Realizes Δ names s childBasis (world ∘ leftAtom))
    (hi : (childTheory k names leftAtom).eval world=true)
    (hf : (childClause k true leftAtom).eval world=true) :
    Coherent (nodeData (shape:=k.shape s t) view (fun _=>leftBranch k child.child)) := by
  constructor
  · intro j hj hroot m hm x hx
    have he := root_kind hroot
    subst j
    have hk : k.dual=false := by cases k <;> simp_all [Constructor.kind,Constructor.dual]
    obtain ⟨hmode,hcoord⟩ := childTheory_inherits view child.view hk hi
    change coordinateValue view.coordinate
      ((branchTransition (leftBranch k child.child)).apply m x) (m.complete (modes names world)) = _
    rw [leftBranch_transition,child.transition,←hmode]
    exact ComparisonCoordinateTransition.pair_absorption _ _ _ _ hcoord
  · intro hroot m n hmn x hx
    have he := root_kind hroot
    have hk : k=Constructor.fn := by
      cases k with
      | prod | sum => cases he
      | fn => rfl
    subst k
    change coordinateValue view.coordinate (!x) (m.complete (modes names world))≤
      coordinateValue view.coordinate (!x) (n.complete (modes names world))
    apply rangeClause_transfer_complete view.first view.second true leftAtom
      (range (world ∘ leftAtom)) Iff.rfl Iff.rfl hf view.scalar m n hmn x
    exact child.ranges x hx

theorem fork_right_coherent {Δ names s t basis childBasis world k}
    (view : View Δ names basis world)
    (child : Realizes Δ names t childBasis (world ∘ rightAtom))
    (hi : (childTheory k names rightAtom).eval world=true)
    (hf : (childClause k false rightAtom).eval world=true) :
    Coherent (nodeData (shape:=k.shape s t) view (fun _=>rightBranch k child.child)) := by
  constructor
  · intro j hj hroot m hm x hx
    have he := root_kind hroot
    subst j
    have hk : k.dual=false := by cases k <;> simp_all [Constructor.kind,Constructor.dual]
    obtain ⟨hmode,hcoord⟩ := childTheory_inherits view child.view hk hi
    change coordinateValue view.coordinate
      ((branchTransition (rightBranch k child.child)).apply m x) (m.complete (modes names world)) = _
    rw [rightBranch_transition,child.transition,←hmode]
    exact ComparisonCoordinateTransition.pair_absorption _ _ _ _ hcoord
  · intro hroot m n hmn x hx
    have he := root_kind hroot
    have hk : k=Constructor.fn := by
      cases k with
      | prod | sum => cases he
      | fn => rfl
    subst k
    change coordinateValue view.coordinate x (m.complete (modes names world))≤
      coordinateValue view.coordinate x (n.complete (modes names world))
    apply rangeClause_transfer_complete view.first view.second false rightAtom
      (range (world ∘ rightAtom)) Iff.rfl Iff.rfl hf view.scalar m n hmn x
    exact child.ranges x hx

theorem fork_left_range {Δ names s t basis childBasis world k}
    (view : View Δ names basis world)
    (child : Realizes Δ names s childBasis (world ∘ leftAtom))
    (hr : Resolved Δ (k.shape s t)) (hclosed : rangeClosure.eval world=true)
    (hinc : (rangeInclusion k true leftAtom).eval world=true)
    {a : CompareTy} (ha : Representable Δ (k.shape s t) a) :
    range world ((nodeData view (fun _=>leftBranch (t:=t) k child.child)).value a) := by
  apply Data.value_range _ hr (range world) (fun v=>View.lookup_range view (.var v))
    (View.lookup_range view .unit) (View.lookup_range view .credit) _ _ ha
  · intro m x hx
    exact (closedRange_iff _ _).mp (view.closed_range hclosed) x hx _
  · intro j hj a b hal har
    have he := root_kind hj
    subst j
    change range world (branchValue (leftBranch k child.child) k.kind a b)
    rw [leftBranch_value]
    have hca : Representable Δ s a := by cases k <;> exact hal
    have hx := child.ranges _ (child.child.range_value hca)
    have hi := (rangeInclusion_correct k true leftAtom world (range world)
      (range (world ∘ leftAtom)) (fun _=>Iff.rfl) (fun _=>Iff.rfl)).mp hinc _ hx
    cases k <;> exact hi

theorem fork_right_range {Δ names s t basis childBasis world k}
    (view : View Δ names basis world)
    (child : Realizes Δ names t childBasis (world ∘ rightAtom))
    (hr : Resolved Δ (k.shape s t)) (hclosed : rangeClosure.eval world=true)
    (hinc : (rangeInclusion k false rightAtom).eval world=true)
    {a : CompareTy} (ha : Representable Δ (k.shape s t) a) :
    range world ((nodeData view (fun _=>rightBranch (s:=s) k child.child)).value a) := by
  apply Data.value_range _ hr (range world) (fun v=>View.lookup_range view (.var v))
    (View.lookup_range view .unit) (View.lookup_range view .credit) _ _ ha
  · intro m x hx
    exact (closedRange_iff _ _).mp (view.closed_range hclosed) x hx _
  · intro j hj a b hal har
    have he := root_kind hj
    subst j
    change range world (branchValue (rightBranch k child.child) k.kind a b)
    rw [rightBranch_value]
    have hca : Representable Δ t b := by cases k <;> exact har
    have hx := child.ranges _ (child.child.range_value hca)
    have hi := (rangeInclusion_correct k false rightAtom world (range world)
      (range (world ∘ rightAtom)) (fun _=>Iff.rfl) (fun _=>Iff.rfl)).mp hinc _ hx
    cases k <;> exact hi

theorem fork_head_cases {names modes fixed s t basis left right} {k : Constructor}
    (hp : ComparisonStructuralBasis.basis names modes fixed (k.shape s t)=some basis)
    (hl : ComparisonStructuralBasis.basis names modes fixed s=some left)
    (hr : ComparisonStructuralBasis.basis names modes fixed t=some right)
    {a : CompareTy} (ha : a∈basis.heads) :
    (∃v,a=.var v) ∨ ∃x∈left.types,∃y∈right.types,a=k.op x y := by
  rw [(ComparisonStructuralBasis.basis_spec hp).1] at ha
  have hh : a∈ComparisonStructuralBasis.fixedHeads names fixed (k.shape s t) ++
      ComparisonStructuralBasis.pairs k.op left.types right.types := by
    rw [(ComparisonStructuralBasis.basis_spec hl).2.2,(ComparisonStructuralBasis.basis_spec hr).2.2]
    cases k <;> exact ha
  rcases List.mem_append.mp hh with hh|hh
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hh
    exact .inl ⟨v,rfl⟩
  · obtain ⟨x,hx,hh⟩ := List.mem_flatMap.mp hh
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hh
    exact .inr ⟨x,hx,y,hy,rfl⟩

theorem nodeData_op {Δ names shape basis world} (view : View Δ names basis world)
    (branch : Kind→Branch Δ shape) (k : Constructor) (a b : CompareTy) :
    (nodeData view branch).value (k.op a b)=branchValue (branch k.kind) k.kind a b := by
  cases k <;> rfl

theorem fork_left_heads {Δ modes names fixed s t basis left right world k}
    (view : View Δ modes basis world)
    (child : Realizes Δ modes s left (world ∘ leftAtom))
    (hp : ComparisonStructuralBasis.basis names modes fixed (k.shape s t)=some basis)
    (hl : ComparisonStructuralBasis.basis names modes fixed s=some left)
    (hr : ComparisonStructuralBasis.basis names modes fixed t=some right)
    (hcoh : (headCoherence basis).eval world=true)
    (hlinks : (links k basis left right true).eval world=true) :
    ∀i (hi : i<basis.heads.length),world (headAtom i)=
      (nodeData view (fun _=>leftBranch (t:=t) k child.child)).value basis.heads[i] := by
  intro i hi
  have hmem := List.getElem_mem hi
  have he := (headCoherence_correct basis world).mp hcoh i hi
  change world (headAtom i)=headValue basis world basis.heads[i] at he
  refine he.trans ?_
  rcases fork_head_cases hp hl hr hmem with ⟨v,hv⟩|⟨x,hx,y,hy,hxy⟩
  · rw [hv] at hmem ⊢
    exact (lookup_mem hmem).symm
  · rw [hxy,nodeData_op,leftBranch_value]
    exact links_left_value child hlinks hx hy

theorem fork_right_heads {Δ modes names fixed s t basis left right world k}
    (view : View Δ modes basis world)
    (child : Realizes Δ modes t right (world ∘ rightAtom))
    (hp : ComparisonStructuralBasis.basis names modes fixed (k.shape s t)=some basis)
    (hl : ComparisonStructuralBasis.basis names modes fixed s=some left)
    (hr : ComparisonStructuralBasis.basis names modes fixed t=some right)
    (hcoh : (headCoherence basis).eval world=true)
    (hlinks : (links k basis left right false).eval world=true) :
    ∀i (hi : i<basis.heads.length),world (headAtom i)=
      (nodeData view (fun _=>rightBranch (s:=s) k child.child)).value basis.heads[i] := by
  intro i hi
  have hmem := List.getElem_mem hi
  have he := (headCoherence_correct basis world).mp hcoh i hi
  change world (headAtom i)=headValue basis world basis.heads[i] at he
  refine he.trans ?_
  rcases fork_head_cases hp hl hr hmem with ⟨v,hv⟩|⟨x,hx,y,hy,hxy⟩
  · rw [hv] at hmem ⊢
    exact (lookup_mem hmem).symm
  · rw [hxy,nodeData_op,rightBranch_value]
    exact links_right_value child hlinks hx hy

def defaultValue {Δ names basis world} (view : View Δ names basis world) : Bool :=
  if view.coordinate=.uniqueness then true else headValue basis world basis.head

theorem defaultValue_range {Δ names basis world} (view : View Δ names basis world)
    (hc : rangeClosure.eval world=true) : range world (defaultValue view) := by
  unfold defaultValue
  split
  next he =>
    have hh := view.closed_range hc
    rw [he] at hh
    obtain ⟨x,hx⟩ := view.range_nonempty
    cases x
    · exact hh hx
    · exact hx
  next => exact view.head_range (by simp [Basis.heads])

noncomputable def leafData {Δ names shape basis world} (view : View Δ names basis world) : Data Δ shape :=
  nodeData view (fun _=>.inr (constantChild (defaultValue view)))

theorem leaf_coherent {Δ names shape basis world} (view : View Δ names basis world) :
    Coherent (leafData (shape:=shape) view) := by
  constructor
  · intro k hk hr m hm x hx
    rfl
  · intro hr m n hmn x hx
    change coordinateValue view.coordinate x (m.complete (modes names world))≤
      coordinateValue view.coordinate x (n.complete (modes names world))
    apply complete_fn view.coordinate _ view.scalar m n hmn
    intro hu
    have he := constantChild_range (Δ:=Δ) (shape:=rightShape shape) (defaultValue view) x hx
    simpa [defaultValue,hu] using he

theorem leaf_range {Δ names shape basis world} (view : View Δ names basis world)
    (hr : Resolved Δ shape) (hc : rangeClosure.eval world=true)
    {a : CompareTy} (ha : Representable Δ shape a) :
    range world ((leafData (shape:=shape) view).value a) := by
  apply Data.value_range _ hr (range world) (fun v=>View.lookup_range view (.var v))
    (View.lookup_range view .unit) (View.lookup_range view .credit) _ _ ha
  · intro m x hx
    exact (closedRange_iff _ _).mp (view.closed_range hc) x hx _
  · intro k hk a b hal har
    change range world (booleanValue (constantChild (defaultValue view)).observer b)
    rw [constantChild_value _ har]
    exact defaultValue_range view hc

def Basic : CompareTy→Prop
  | .var _ | .unit | .credit => True
  | _ => False

theorem leaf_heads {Δ names shape basis world} (view : View Δ names basis world)
    (hh : ∀a∈basis.heads,Basic a) (hc : (headCoherence basis).eval world=true) :
    ∀i (hi : i<basis.heads.length),world (headAtom i)=(leafData (shape:=shape) view).value basis.heads[i] := by
  intro i hi
  have hmem := List.getElem_mem hi
  have he := (headCoherence_correct basis world).mp hc i hi
  change world (headAtom i)=headValue basis world basis.heads[i] at he
  refine he.trans ?_
  have hbasic := hh _ hmem
  generalize hv : basis.heads[i]=a at hbasic hmem ⊢
  cases a <;> first | contradiction | exact (lookup_mem hmem).symm

theorem prepared_node_realizes {shapeFuel normFuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {shape : ComparisonShape} {basis : Basis}
    {originals : List (CompareTy×CompareTy)} {pairs : List ComparisonStructuralEndpoints.Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel p solved originals=.success pairs)
    (hdeclared : ∀pair∈ComparisonStructuralEndpoints.declared p,pair∈originals)
    (hΔ : p.assumptions.TypeBoundsDefined)
    (hf : shape.subst solved.fixedShapes=shape)
    (hbasis : ComparisonStructuralBasis.basis (ComparisonSelectedBases.inputNames p)
      (ComparisonSelectedBases.inputModes p) solved.fixedShapes shape=some basis)
    {bounds : List ComparisonStructuralNode.Bound}
    (hp : ComparisonStructuralNode.prepare basis (ComparisonStructuralEndpoints.atShape pairs shape)=some bounds)
    {world : Nat→Bool} (hnode : (nodeTheory p.assumptions basis bounds).eval world=true)
    (view : View p.assumptions (ComparisonSelectedBases.inputModes p) basis world)
    (d : Data p.assumptions shape) (hc : Coherent d)
    (ht : ∀m x,d.transition.apply m x=coordinateValue view.coordinate x
      (m.complete (modes (ComparisonSelectedBases.inputModes p) world)))
    (hh : ∀i (hi : i<basis.heads.length),world (headAtom i)=d.value basis.heads[i])
    (hvalues : ∀a,Representable p.assumptions shape a→ range world (d.value a)) :
    Nonempty (Realizes p.assumptions (ComparisonSelectedBases.inputModes p) shape basis world) := by
  have hresolved := resolved_of_normalizer solved.fixedShapes
    (ComparisonShapeSolver.prepare_fixed_equivalent hs) hf
  have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ=>(ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
  have hrep : ∀a∈basis.heads,Representable p.assumptions shape a := by
    rw [(ComparisonStructuralBasis.basis_spec hbasis).1]
    exact ComparisonStructuralBasis.heads_representable _ _ _ hshapes shape
  have hm := (ComparisonStructuralBasis.basis_spec hbasis).2.1
  have hval := view.basis_value hm d.value (fun _ _=>rfl) (fun _ _=>rfl) hh (fun a m=>ht m (d.value a))
  have hbound := ComparisonStructuralEndpoints.declared_boundsHold hs d hresolved hf view.scalar ht
    hΔ hnorm hdeclared (nodeTheory_values hnode hp d.value (fun _ _=>rfl) (fun _ _=>rfl) hval)
  exact data_realizes view hm hrep d hresolved hc hbound hΔ ht hh hvalues

end ModalityInference.ComparisonStructuralRealization
