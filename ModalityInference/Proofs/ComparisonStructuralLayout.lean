import ModalityInference.ComparisonStructuralLayout
import ModalityInference.Proofs.ComparisonStructuralNode
import ModalityInference.Proofs.ComparisonSelectedBases
import ModalityInference.Proofs.Projection

/-! A selected finite structural basis generates a finite recursive observer
query. Actual lattice observers realize all active nodes simultaneously, with
whole declared endpoints, guarded scalar worlds and genuine global ranges.
No extension of arbitrary finite tables is assumed in this direction. -/
namespace ModalityInference.ComparisonStructuralLayout
open ComparisonControls ComparisonAlgebra ComparisonStructuralAlignment

namespace Constructor
def kind : Constructor → ComparisonStructuralLattice.Kind
  | .prod => .prod | .sum => .sum | .fn => .fn
@[simp] theorem kind_shape (k : Constructor) (s t) : k.kind.shape s t = k.shape s t := by cases k <;> rfl
@[simp] theorem kind_op (k : Constructor) (a b) : k.kind.op a b = k.op a b := by cases k <;> rfl
def carrier (k : Constructor) {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) : Carrier Δ (k.shape s t) :=
  represented (by simpa only [kind_op, kind_shape] using
    k.kind.op_representable ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨b.shaped,b.defined,b.shape_eq⟩)
end Constructor

/-- A shape-generated layout supplies genuine same-shape basis entries and all
Cartesian constructor ports. These properties do not invert declared bounds. -/
inductive Valid (Δ : Bounds) (modes : List ModVar) : Layout → Prop
  | leaf {s b} (heads : ∀t∈b.heads, Representable Δ s t) (modeNames : b.modes = modes) :
      Valid Δ modes (.leaf s b)
  | fork {k b left right}
      (heads : ∀t∈b.heads, Representable Δ (k.shape left.shape right.shape) t)
      (modeNames : b.modes = modes)
      (leftValid : Valid Δ modes left) (rightValid : Valid Δ modes right)
      (cells : ∀a∈left.basis.types, ∀c∈right.basis.types, k.op a c∈b.heads) :
      Valid Δ modes (.fork k b left right)

theorem Valid.heads {Δ modes layout} (h : Valid Δ modes layout) :
    ∀t∈layout.basis.heads, Representable Δ layout.shape t := by
  cases h <;> assumption

theorem Valid.modes {Δ modes layout} (h : Valid Δ modes layout) : layout.basis.modes = modes := by
  cases h <;> assumption

structure Observes {Δ : Bounds} {shape : ComparisonShape} (basis : Basis)
    (f : LatticeHom (Order Δ shape) Bool) (c : Coordinate) (η : ModVar → Mode)
    (world : Nat → Bool) : Prop where
  types : ∀i (hi : i < basis.types.length), world (basisAtom i) = booleanValue f basis.types[i]
  heads : ∀i (hi : i < basis.heads.length), world (headAtom i) = booleanValue f basis.heads[i]
  modes : ∀i, world (modeAtom i) = encodeModes η i
  first : world (choiceAtom 1) = (coordinateBits c).1
  second : world (choiceAtom 2) = (coordinateBits c).2
  falseRange : world (choiceAtom 3) = true ↔ ∃x, observer f x = false
  trueRange : world (choiceAtom 4) = true ↔ ∃x, observer f x = true

def combine (here left right : Nat → Bool) (i : Nat) : Bool :=
  if i % 3 = 0 then here (i / 3) else if i % 3 = 1 then left (i / 3) else right (i / 3)

@[simp] theorem combine_local (here left right : Nat → Bool) (i : Nat) :
    combine here left right (localAtom i) = here i := by simp [combine, localAtom]
@[simp] theorem combine_left (here left right : Nat → Bool) (i : Nat) :
    combine here left right (leftAtom i) = left i := by simp [combine, leftAtom, Nat.add_div]
@[simp] theorem combine_right (here left right : Nat → Bool) (i : Nat) :
    combine here left right (rightAtom i) = right i := by simp [combine, rightAtom, Nat.add_div]

noncomputable def localWorld {Δ : Bounds} {shape : ComparisonShape} (basis : Basis)
    (f : LatticeHom (Order Δ shape) Bool) (c : Coordinate) (η : ModVar → Mode)
    (side : Bool) (i : Nat) : Bool := by
  classical
  exact match i % 4 with
  | 0 => ((basis.types[i / 4]?).map (booleanValue f)).getD false
  | 1 => ((basis.heads[i / 4]?).map (booleanValue f)).getD false
  | 2 => encodeModes η (i / 4)
  | _ => match i / 4 with
    | 0 => side
    | 1 => (coordinateBits c).1
    | 2 => (coordinateBits c).2
    | 3 => decide (∃x, observer f x = false)
    | 4 => decide (∃x, observer f x = true)
    | _ => false

theorem combine_observes {Δ : Bounds} {shape : ComparisonShape} (basis : Basis)
    (f : LatticeHom (Order Δ shape) Bool) (c : Coordinate) (η : ModVar → Mode)
    (side : Bool) (left right : Nat → Bool) :
    Observes basis f c η (combine (localWorld basis f c η side) left right) := by
  constructor
  · intro i hi
    simp [basisAtom, localWorld, List.getElem?_eq_getElem hi]
  · intro i hi
    simp [headAtom, localWorld, Nat.add_div, List.getElem?_eq_getElem hi]
  · intro i
    simp [modeAtom, localWorld, Nat.add_div]
  · simp [choiceAtom, localWorld]
  · simp [choiceAtom, localWorld]
  · simp [choiceAtom, localWorld]
  · simp [choiceAtom, localWorld]

@[simp] theorem rename_eval (atoms : Nat → Nat) (e : BoolExpr) (world : Nat → Bool) :
    (rename atoms e).eval world = e.eval (world ∘ atoms) := by
  simp [rename, SymbolicCNF.substitute_eval, BoolExpr.eval, Function.comp_def]

private theorem all_eval (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all es).eval world = true ↔ ∀e∈es,e.eval world = true := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

private theorem any_eval (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any es).eval world = true ↔ ∃e∈es,e.eval world = true := by
  induction es <;> simp_all [BoolExpr.any, BoolExpr.eval]

theorem Observes.coordinate {Δ shape basis f c η world}
    (h : @Observes Δ shape basis f c η world) : (coordinateTest c).eval world = true := by
  simp [coordinateTest, BoolExpr.equal, BoolExpr.eval, h.first, h.second]

theorem Observes.range {Δ shape basis f c η world}
    (h : @Observes Δ shape basis f c η world)
    (hh : ∀t∈basis.heads, Representable Δ shape t) : (rangeTheory basis).eval world = true := by
  have ht := ComparisonStructuralNode.basis_representable basis hh
  have hr (t) (he : Representable Δ shape t) :
      booleanValue f t = observer f (represented he) := booleanValue_represented f t he
  have hin : (world (choiceAtom 3) || world (choiceAtom 4)) = true := by
    let x := represented (hh basis.head (by simp [Basis.heads]))
    cases hx : observer f x
    · simp [h.falseRange.mpr ⟨x,hx⟩]
    · simp [h.trueRange.mpr ⟨x,hx⟩]
  simp only [rangeTheory, BoolExpr.eval, hin, Bool.true_and]
  apply (all_eval _ _).mpr
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
  have hi := List.mem_range.mp hi
  have he := ht _ (List.getElem_mem hi)
  simp only [BoolExpr.eval]
  rw [show world (basisAtom i) = observer f (represented he) from (h.types i hi).trans (hr _ he)]
  cases hx : observer f (represented he)
  · simp [h.falseRange.mpr ⟨_,hx⟩]
  · simp [h.trueRange.mpr ⟨_,hx⟩]

private theorem cnf_eval (clauses : CNF) (world : Nat → Bool) :
    (ComparisonStructuralFamily.cnfFormula false BoolExpr.atom clauses).eval world = true ↔
      CNFHolds world clauses := by
  simp [ComparisonStructuralFamily.cnfFormula_eval, ComparisonStructuralMatrix.cnfValue,
    ComparisonStructuralMatrix.clauseValue, BoolExpr.eval, List.all_eq_true, List.any_eq_true,
    CNFHolds, ClauseHolds]

theorem nodeTheory_observer {Δ : Bounds} {shape : ComparisonShape}
    {f : LatticeHom (Order Δ shape) Bool} {labels : List (GuardedMode Δ)}
    {c : Coordinate} {η : ModVar → Mode} {basis : Basis} {world : Nat → Bool}
    (hmodel : Model f labels c η) (ho : Observes basis f c η world)
    {input : List (CompareTy × CompareTy)} {bounds : List ComparisonStructuralNode.Bound}
    (hp : ComparisonStructuralNode.prepare basis input = some bounds)
    (hheads : ∀t∈basis.heads, Representable Δ shape t)
    (hlabels : ∀p∈basis.modalPairs, ∃m∈labels, m.expression = p.2)
    (hinput : ∀pair∈input, AlgebraSubtype Δ pair.1 pair.2) :
    (nodeTheory Δ basis bounds).eval world = true := by
  obtain ⟨threshold, output, hc⟩ := ComparisonStructuralNode.compile_complete
    basis basisAtom headAtom modeAtom c bounds
  have h := ComparisonStructuralNode.compile_observer hmodel hp (hc threshold (le_refl _))
    hheads hlabels hinput ho.heads ho.types ho.modes
  obtain ⟨ht, hb⟩ := (ComparisonStructuralNode.compile_correct (hc threshold (le_refl _)) world).mp h
  have hbounds := (cnf_eval _ _).mpr ((ComparisonStructuralNode.clauses_correct _ _ _).mpr hb)
  have hg : (if c == .unaffected then BoolExpr.const true
      else rename modeAtom (boundsModeFormula Δ)).eval world = true := by
    rcases hmodel.modeModel with rfl | hη
    · rfl
    · have he : (boundsModeFormula Δ).eval (encodeModes η) = true := by
        simpa only [boundsModeFormula_correct, projectedModes_encodeModes] using hη
      have hw : world ∘ modeAtom = encodeModes η := funext ho.modes
      cases c with
      | unaffected => rfl
      | locality | affinity | uniqueness =>
        change (rename modeAtom (boundsModeFormula Δ)).eval world = true
        rw [rename_eval, hw]
        exact he
  have hcontrols : (BoolExpr.any ([Coordinate.unaffected, .locality, .affinity, .uniqueness].map fun c =>
      .and (coordinateTest c) (.and (basis.theoryAt basisAtom headAtom modeAtom c)
        (if c == .unaffected then .const true else rename modeAtom (boundsModeFormula Δ))))).eval world = true := by
    apply (any_eval _ _).mpr
    refine ⟨_, List.mem_map.mpr ⟨c, ?_, rfl⟩, ?_⟩
    · cases c <;> simp
    · simp only [BoolExpr.eval, ho.coordinate, ht, hg, Bool.and_self]
  simp only [nodeTheory, BoolExpr.eval, ho.range hheads, hcontrols, hbounds, Bool.and_self]

theorem SharedProfile.model_at {Δ shape f labels c η}
    (h : @SharedProfile Δ shape f labels c η) :
    ∃child, Model f labels child η ∧ (child = .unaffected ∨ child = c) := by
  rcases h with ⟨value, he⟩ | ⟨child, hm, hc, _⟩
  · exact ⟨.unaffected, ⟨.inl rfl, fun x m _ => (he (m.act x)).trans (he x).symm⟩, .inl rfl⟩
  · exact ⟨child, hm, hc⟩

theorem observer_model {Δ shape} (f : LatticeHom (Order Δ shape) Bool)
    (anchor : Carrier Δ shape) (labels : List (GuardedMode Δ)) : ∃c η, Model f labels c η := by
  classical
  by_cases hn : ∃a b, observer f a = false ∧ observer f b = true
  · obtain ⟨a, b, ha, hb⟩ := hn
    obtain ⟨c, η, hη, haction⟩ := observer_global_realizable f a b ha hb labels
    exact ⟨c, η, ⟨hη, haction⟩⟩
  · have he (x) : observer f x = observer f anchor := by
      cases ha : observer f anchor <;> cases hx : observer f x
      · rfl
      · exact False.elim (hn ⟨anchor,x,ha,hx⟩)
      · exact False.elim (hn ⟨x,anchor,hx,ha⟩)
      · rfl
    exact ⟨.unaffected, fun _ => Mode.identity,
      ⟨.inl rfl, fun x m _ => (he (m.act x)).trans (he x).symm⟩⟩

open ComparisonStructuralObservers in
 theorem constructor_choice {Δ s t} (k : Constructor)
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (a₀ : Carrier Δ s) (b₀ : Carrier Δ t)
    {labels : List (GuardedMode Δ)} {names : List ModVar} {c : Coordinate} {η : ModVar → Mode}
    (hmodel : Model f labels c η)
    (htests : ∀m∈tests names, ∃n∈labels, n.expression = m)
    (hsupport : ∀m∈labels, ∀v∈m.expression.freeVariables, v∈names) :
    (∃g : LatticeHom (Order Δ s) Bool, ∃child θ, Model g labels child θ ∧
      (k.dual = true ∨ θ = η ∧ (child = .unaffected ∨ child = c)) ∧
      ∀a b, observer f (k.carrier a b) = leftSign k.kind (observer g a)) ∨
    (∃g : LatticeHom (Order Δ t) Bool, ∃child θ, Model g labels child θ ∧
      (k.dual = true ∨ θ = η ∧ (child = .unaffected ∨ child = c)) ∧
      ∀a b, observer f (k.carrier a b) = observer g b) := by
  cases k with
  | prod =>
    rcases pair_shared_profile false f a₀ b₀ hmodel htests hsupport with hl | hr
    · obtain ⟨child, hm, hc⟩ := SharedProfile.model_at hl.2
      exact .inl ⟨_, child, η, hm, .inr ⟨rfl,hc⟩, hl.1⟩
    · obtain ⟨child, hm, hc⟩ := SharedProfile.model_at hr.2
      exact .inr ⟨_, child, η, hm, .inr ⟨rfl,hc⟩, hr.1⟩
  | sum =>
    rcases pair_shared_profile true f a₀ b₀ hmodel htests hsupport with hl | hr
    · obtain ⟨child, hm, hc⟩ := SharedProfile.model_at hl.2
      exact .inl ⟨_, child, η, hm, .inr ⟨rfl,hc⟩, hl.1⟩
    · obtain ⟨child, hm, hc⟩ := SharedProfile.model_at hr.2
      exact .inr ⟨_, child, η, hm, .inr ⟨rfl,hc⟩, hr.1⟩
  | fn =>
    let unitMode : GuardedMode Δ := ⟨.epsilon, fun _ => Mode.identity, fun _ _ => rfl⟩
    have hi (x) : observer f (unitMode.act x) = observer f x :=
      congrArg f (Carrier.atMode_identity x)
    rcases observer_child_family .fn f a₀ b₀ with hl | hr
    · obtain ⟨child, θ, hm⟩ := observer_model (leftObserver .fn f b₀) a₀ labels
      refine .inl ⟨_, child, θ, hm, .inl rfl, ?_⟩
      simpa only [hi, actObserver_eq f unitMode hi] using hl unitMode
    · obtain ⟨child, θ, hm⟩ := observer_model (rightObserver .fn f a₀) b₀ labels
      refine .inr ⟨_, child, θ, hm, .inl rfl, ?_⟩
      simpa only [hi, actObserver_eq f unitMode hi] using hr unitMode

theorem Observes.type_mem {Δ shape basis f c η world}
    (h : @Observes Δ shape basis f c η world) {t : CompareTy} (ht : t∈basis.types) :
    world (basisAtom (basis.types.idxOf t)) = booleanValue f t := by
  have hi := List.idxOf_lt_length_of_mem ht
  have he : basis.types[basis.types.idxOf t] = t := by
    simpa only [List.idxOf, beq_iff_eq] using
      (List.findIdx_getElem (xs := basis.types) (p := (· == t)) (w := hi))
  exact (h.types _ hi).trans (congrArg (booleanValue f) he)

theorem Observes.head_mem {Δ shape basis f c η world}
    (h : @Observes Δ shape basis f c η world) {t : CompareTy} (ht : t∈basis.heads) :
    world (headAtom (basis.heads.idxOf t)) = booleanValue f t := by
  have hi := List.idxOf_lt_length_of_mem ht
  have he : basis.heads[basis.heads.idxOf t] = t := by
    simpa only [List.idxOf, beq_iff_eq] using
      (List.findIdx_getElem (xs := basis.heads) (p := (· == t)) (w := hi))
  exact (h.heads _ hi).trans (congrArg (booleanValue f) he)

theorem links_left {Δ s t} {k : Constructor} {basis left right : Basis}
    {f : LatticeHom (Order Δ (k.shape s t)) Bool} {g : LatticeHom (Order Δ s) Bool}
    {parent child : Coordinate} {η θ : ModVar → Mode} {world : Nat → Bool}
    (hp : Observes basis f parent η world) (hc : Observes left g child θ (world ∘ leftAtom))
    (hleft : ∀a∈left.types, Representable Δ s a) (hright : ∀b∈right.types, Representable Δ t b)
    (hcell : ∀a∈left.types, ∀b∈right.types, k.op a b∈basis.heads)
    (hvalue : ∀a b, observer f (k.carrier a b) =
      ComparisonStructuralObservers.leftSign k.kind (observer g a)) :
    (links k basis left right true).eval world = true := by
  apply (all_eval _ _).mpr
  intro e he
  obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
  have hv := hvalue (represented (hleft a ha)) (represented (hright b hb))
  have hv' : booleanValue f (k.op a b) =
      ComparisonStructuralObservers.leftSign k.kind (booleanValue g a) := by
    exact (booleanValue_carrier f (k.carrier (represented (hleft a ha))
      (represented (hright b hb)))).trans (hv.trans
        (congrArg (ComparisonStructuralObservers.leftSign k.kind)
          (booleanValue_carrier g (represented (hleft a ha))).symm))
  have hh := hp.head_mem (hcell a ha b hb)
  have hl := hc.type_mem ha
  simp only [Function.comp_def] at hl
  cases k <;> simp_all [Constructor.dual, Constructor.kind,
    ComparisonStructuralObservers.leftSign, BoolExpr.equal, BoolExpr.eval]

theorem links_right {Δ s t} {k : Constructor} {basis left right : Basis}
    {f : LatticeHom (Order Δ (k.shape s t)) Bool} {g : LatticeHom (Order Δ t) Bool}
    {parent child : Coordinate} {η θ : ModVar → Mode} {world : Nat → Bool}
    (hp : Observes basis f parent η world) (hc : Observes right g child θ (world ∘ rightAtom))
    (hleft : ∀a∈left.types, Representable Δ s a) (hright : ∀b∈right.types, Representable Δ t b)
    (hcell : ∀a∈left.types, ∀b∈right.types, k.op a b∈basis.heads)
    (hvalue : ∀a b, observer f (k.carrier a b) = observer g b) :
    (links k basis left right false).eval world = true := by
  apply (all_eval _ _).mpr
  intro e he
  obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
  have hv := hvalue (represented (hleft a ha)) (represented (hright b hb))
  have hv' : booleanValue f (k.op a b) = booleanValue g b := by
    exact (booleanValue_carrier f (k.carrier (represented (hleft a ha))
      (represented (hright b hb)))).trans (hv.trans
        (booleanValue_carrier g (represented (hright b hb))).symm)
  have hh := hp.head_mem (hcell a ha b hb)
  have hl := hc.type_mem hb
  simp only [Function.comp_def] at hl
  simp [BoolExpr.equal, BoolExpr.eval, hh, hl, hv']

theorem childTheory_observer {Δ ps cs} {k : Constructor} {modes : List ModVar}
    {basis childBasis : Basis} {f : LatticeHom (Order Δ ps) Bool} {g : LatticeHom (Order Δ cs) Bool}
    {parent child : Coordinate} {η θ : ModVar → Mode} {world : Nat → Bool} {atoms : Nat → Nat}
    (hp : Observes basis f parent η world) (hc : Observes childBasis g child θ (world ∘ atoms))
    (h : k.dual = true ∨ θ = η ∧ (child = .unaffected ∨ child = parent)) :
    (childTheory k modes atoms).eval world = true := by
  rcases h with h | ⟨rfl, hchild⟩
  · simp [childTheory, h, BoolExpr.eval]
  · by_cases hd : k.dual = true
    · simp [childTheory, hd, BoolExpr.eval]
    simp only [childTheory, Bool.eq_false_iff.mpr hd, Bool.false_eq_true, if_false, BoolExpr.eval, Bool.and_eq_true]
    constructor
    · simp only [childCoordinate, BoolExpr.eval, Bool.or_eq_true, rename_eval]
      rcases hchild with rfl | rfl
      · exact .inl hc.coordinate
      · right
        apply (any_eval _ _).mpr
        refine ⟨_, List.mem_map.mpr ⟨child, ?_, rfl⟩, ?_⟩
        · cases child <;> simp
        · simp only [BoolExpr.eval, rename_eval, hp.coordinate, hc.coordinate, Bool.and_self]
    · apply (all_eval _ _).mpr
      intro e he
      obtain ⟨v, _, he⟩ := List.mem_flatMap.mp he
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
      simp only [BoolExpr.equal, BoolExpr.eval, hp.modes]
      have he := hc.modes (v.atomIndex i)
      simp only [Function.comp_def] at he
      simp [he]

/-- Active nodes retain actual observers and their global ranges. Function
children may have another scalar world, but every node uses the same labels. -/
inductive Realized (Δ : Bounds) (labels : List (GuardedMode Δ)) :
    (layout : Layout) → LatticeHom (Order Δ layout.shape) Bool → Coordinate →
      (ModVar → Mode) → (Nat → Bool) → Prop
  | leaf {s b f c η world}
      (model : Model f labels c η) (observes : Observes b f c η world) :
      Realized Δ labels (.leaf s b) f c η world
  | left {k b left right f c η world child θ}
      (g : LatticeHom (Order Δ left.shape) Bool)
      (model : Model f labels c η) (observes : Observes b f c η world)
      (side : world (choiceAtom 0) = true)
      (inheritance : k.dual = true ∨ θ = η ∧ (child = .unaffected ∨ child = c))
      (values : ∀a d, observer f (k.carrier a d) =
        ComparisonStructuralObservers.leftSign k.kind (observer g a))
      (subtree : Realized Δ labels left g child θ (world ∘ leftAtom)) :
      Realized Δ labels (.fork k b left right) f c η world
  | right {k b left right f c η world child θ}
      (g : LatticeHom (Order Δ right.shape) Bool)
      (model : Model f labels c η) (observes : Observes b f c η world)
      (side : world (choiceAtom 0) = false)
      (inheritance : k.dual = true ∨ θ = η ∧ (child = .unaffected ∨ child = c))
      (values : ∀a d, observer f (k.carrier a d) = observer g d)
      (subtree : Realized Δ labels right g child θ (world ∘ rightAtom)) :
      Realized Δ labels (.fork k b left right) f c η world

/-- One actual root observer supplies all active node values, branch choices,
coordinate choices and genuine global range bits in one recursive query. -/
theorem query_realized {Δ : Bounds} {modes : List ModVar}
    {labels : List (GuardedMode Δ)}
    (htests : ∀m∈tests modes, ∃n∈labels, n.expression = m)
    (hsupport : ∀m∈labels, ∀v∈m.expression.freeVariables, v∈modes)
    (hlabels : ∀b : Basis, b.modes = modes → ∀p∈b.modalPairs, ∃m∈labels, m.expression = p.2)
    {endpoints : ComparisonShape → List (CompareTy × CompareTy)}
    (hinput : ∀s, ∀pair∈endpoints s, AlgebraSubtype Δ pair.1 pair.2)
    {layout : Layout} (hv : Valid Δ modes layout) {q : BoolExpr}
    (hq : query Δ endpoints layout = some q)
    (f : LatticeHom (Order Δ layout.shape) Bool) {c : Coordinate} {η : ModVar → Mode}
    (hmodel : Model f labels c η) :
    ∃world, Observes layout.basis f c η world ∧ q.eval world = true ∧
      Realized Δ labels layout f c η world := by
  induction hv generalizing q c η with
  | @leaf s b hheads hmodes =>
    cases hb : ComparisonStructuralNode.prepare b (endpoints s) <;> simp [query, hb] at hq
    subst q
    let world := combine (localWorld b f c η false) (fun _ => false) (fun _ => false)
    have ho := combine_observes b f c η false (fun _ => false) (fun _ => false)
    exact ⟨world, ho, nodeTheory_observer hmodel ho hb hheads (hlabels b hmodes) (hinput s), .leaf hmodel ho⟩
  | @fork k b left right hheads hmodes hlvalid hrvalid hcells ihl ihr =>
    cases hb : ComparisonStructuralNode.prepare b (endpoints (Layout.fork k b left right).shape) <;>
      simp [query, hb] at hq
    cases hql : query Δ endpoints left <;> simp [hql] at hq
    rename_i ql
    cases hqr : query Δ endpoints right <;> simp [hqr] at hq
    rename_i qr
    subst q
    let a₀ := represented (hlvalid.heads left.basis.head (by simp [Basis.heads]))
    let b₀ := represented (hrvalid.heads right.basis.head (by simp [Basis.heads]))
    have hlt := ComparisonStructuralNode.basis_representable left.basis hlvalid.heads
    have hrt := ComparisonStructuralNode.basis_representable right.basis hrvalid.heads
    rcases constructor_choice k f a₀ b₀ hmodel htests hsupport with
      ⟨g,child,θ,hg,hi,hvalue⟩ | ⟨g,child,θ,hg,hi,hvalue⟩
    · obtain ⟨wl, hol, hwl, htree⟩ := ihl hql g hg
      let world := combine (localWorld b f c η true) wl (fun _ => false)
      have ho := combine_observes b f c η true wl (fun _ => false)
      have hol' : Observes left.basis g child θ (world ∘ leftAtom) := by
        simpa only [world, Function.comp_def, combine_left] using hol
      have hn := nodeTheory_observer hmodel ho hb hheads (hlabels b hmodes) (hinput _)
      have hlink := links_left ho hol' hlt hrt hcells hvalue
      have hc := childTheory_observer (modes := b.modes) ho hol' hi
      refine ⟨world, ho, ?_, ?_⟩
      · simp only [BoolExpr.eval, rename_eval]
        simp [world, Function.comp_def, choiceAtom, localWorld, hwl, hn, hlink, hc]
      · exact .left g hmodel ho (by simp [world,choiceAtom,localWorld]) hi hvalue
          (by simpa only [world,Function.comp_def,combine_left] using htree)
    · obtain ⟨wr, hor, hwr, htree⟩ := ihr hqr g hg
      let world := combine (localWorld b f c η false) (fun _ => false) wr
      have ho := combine_observes b f c η false (fun _ => false) wr
      have hor' : Observes right.basis g child θ (world ∘ rightAtom) := by
        simpa only [world, Function.comp_def, combine_right] using hor
      have hn := nodeTheory_observer hmodel ho hb hheads (hlabels b hmodes) (hinput _)
      have hlink := links_right ho hor' hlt hrt hcells hvalue
      have hc := childTheory_observer (modes := b.modes) ho hor' hi
      refine ⟨world, ho, ?_, ?_⟩
      · simp only [BoolExpr.eval, rename_eval]
        simp [world, Function.comp_def, choiceAtom, localWorld, hwr, hn, hlink, hc]
      · exact .right g hmodel ho (by simp [world,choiceAtom,localWorld]) hi hvalue
          (by simpa only [world,Function.comp_def,combine_right] using htree)

inductive Based (names : List TypeVar) (modes : List ModVar) (fixed : TypeVar → ComparisonShape) : Layout → Prop
  | leaf {s b} (basis : ComparisonStructuralBasis.basis names modes fixed s = some b) :
      Based names modes fixed (.leaf s b)
  | fork {k b left right}
      (basis : ComparisonStructuralBasis.basis names modes fixed (k.shape left.shape right.shape) = some b)
      (leftBased : Based names modes fixed left) (rightBased : Based names modes fixed right) :
      Based names modes fixed (.fork k b left right)

theorem Based.basis {names modes fixed layout} (h : Based names modes fixed layout) :
    ComparisonStructuralBasis.basis names modes fixed layout.shape = some layout.basis := by
  cases h <;> assumption

theorem build_constructor (names modes fixed) (k : Constructor) (s t : ComparisonShape) :
    build names modes fixed (k.shape s t) = do
      let b ← ComparisonStructuralBasis.basis names modes fixed (k.shape s t)
      match ComparisonStructuralBasis.basis names modes fixed s,
          ComparisonStructuralBasis.basis names modes fixed t with
      | some _, some _ => return .fork k b (← build names modes fixed s) (← build names modes fixed t)
      | _, _ => return .leaf (k.shape s t) b := by
  cases k <;> rfl

private theorem build_constructor_complete (names modes fixed) (k : Constructor) (s t : ComparisonShape)
    (ihs : ∀b, ComparisonStructuralBasis.basis names modes fixed s = some b →
      ∃l, build names modes fixed s = some l ∧ l.shape = s ∧ l.basis = b ∧ Based names modes fixed l)
    (iht : ∀b, ComparisonStructuralBasis.basis names modes fixed t = some b →
      ∃l, build names modes fixed t = some l ∧ l.shape = t ∧ l.basis = b ∧ Based names modes fixed l)
    (b : Basis) (hb : ComparisonStructuralBasis.basis names modes fixed (k.shape s t) = some b) :
    ∃l, build names modes fixed (k.shape s t) = some l ∧
      l.shape = k.shape s t ∧ l.basis = b ∧ Based names modes fixed l := by
  cases hs : ComparisonStructuralBasis.basis names modes fixed s with
  | none =>
    exact ⟨.leaf (k.shape s t) b, by simp [build_constructor, hb, hs], rfl, rfl, .leaf hb⟩
  | some bs =>
    cases ht : ComparisonStructuralBasis.basis names modes fixed t with
    | none => exact ⟨.leaf (k.shape s t) b, by simp [build_constructor, hb, hs, ht], rfl, rfl, .leaf hb⟩
    | some bt =>
      obtain ⟨left, hl, hls, _, hleft⟩ := ihs bs hs
      obtain ⟨right, hr, hrs, _, hright⟩ := iht bt ht
      exact ⟨.fork k b left right, by simp [build_constructor, hb, hs, ht, hl, hr],
        by simp [Layout.shape, hls, hrs], rfl, .fork (by simpa only [hls, hrs] using hb) hleft hright⟩

theorem build_complete (names : List TypeVar) (modes : List ModVar) (fixed : TypeVar → ComparisonShape)
    (s : ComparisonShape) {b : Basis} (hb : ComparisonStructuralBasis.basis names modes fixed s = some b) :
    ∃l, build names modes fixed s = some l ∧ l.shape = s ∧ l.basis = b ∧ Based names modes fixed l := by
  induction s generalizing b with
  | var v => exact ⟨.leaf (.var v) b, by simp [build, hb], rfl, rfl, .leaf hb⟩
  | unit => exact ⟨.leaf .unit b, by simp [build, hb], rfl, rfl, .leaf hb⟩
  | credit => exact ⟨.leaf .credit b, by simp [build, hb], rfl, rfl, .leaf hb⟩
  | prod s t ihs iht => exact build_constructor_complete names modes fixed .prod s t (fun _ => ihs) (fun _ => iht) b hb
  | sum s t ihs iht => exact build_constructor_complete names modes fixed .sum s t (fun _ => ihs) (fun _ => iht) b hb
  | fn s t ihs iht => exact build_constructor_complete names modes fixed .fn s t (fun _ => ihs) (fun _ => iht) b hb

theorem Based.valid {Δ : Bounds} {names modes fixed layout}
    (h : Based names modes fixed layout)
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (fixed v)) : Valid Δ modes layout := by
  induction h with
  | @leaf s b hb =>
    refine .leaf ?_ (ComparisonStructuralBasis.basis_spec hb).2.1
    rw [(ComparisonStructuralBasis.basis_spec hb).1]
    exact ComparisonStructuralBasis.heads_representable names modes fixed hs s
  | @fork k b left right hb hl hr ihl ihr =>
    have hh : ∀t∈b.heads, Representable Δ (k.shape left.shape right.shape) t := by
      rw [(ComparisonStructuralBasis.basis_spec hb).1]
      exact ComparisonStructuralBasis.heads_representable names modes fixed hs _
    refine .fork hh (ComparisonStructuralBasis.basis_spec hb).2.1 ihl ihr ?_
    intro a ha c hc
    rw [(ComparisonStructuralBasis.basis_spec hb).1]
    have hal : a∈ComparisonStructuralBasis.extend modes (ComparisonStructuralBasis.heads names modes fixed left.shape) :=
      (ComparisonStructuralBasis.basis_spec hl.basis).2.2 ▸ ha
    have hcr : c∈ComparisonStructuralBasis.extend modes (ComparisonStructuralBasis.heads names modes fixed right.shape) :=
      (ComparisonStructuralBasis.basis_spec hr.basis).2.2 ▸ hc
    have hcell := ComparisonStructuralBasis.constructor_heads k.kind names modes fixed left.shape right.shape
      (k.kind.op a c) (List.mem_flatMap.mpr ⟨a,hal,List.mem_map.mpr ⟨c,hcr,rfl⟩⟩)
    simpa only [Constructor.kind_op, Constructor.kind_shape] using hcell

def labelExpressions (modes : List ModVar) : List ModExpr := .const Mode.bottom :: tests modes

theorem label_total {modes e} (he : e∈labelExpressions modes) (η : ModVar → Mode) : e.WellFormed η := by
  rcases List.mem_cons.mp he with rfl | he
  · rfl
  · exact tests_total he η

def labels (Δ : Bounds) (modes : List ModVar) : List (GuardedMode Δ) :=
  (labelExpressions modes).attach.map fun e => GuardedMode.ofDefined e.val (fun η _ => label_total e.property η)

theorem labels_mem {Δ modes e} : (∃m∈labels Δ modes, m.expression = e) ↔ e∈labelExpressions modes := by
  constructor
  · rintro ⟨m, hm, he⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
    change a.val = e at he
    exact he ▸ a.property
  · intro he
    exact ⟨GuardedMode.ofDefined e (fun η _ => label_total he η),
      List.mem_map.mpr ⟨⟨e,he⟩,List.mem_attach _ _,rfl⟩,rfl⟩

theorem labels_tests (Δ : Bounds) (modes : List ModVar) :
    ∀m∈tests modes, ∃n∈labels Δ modes, n.expression = m :=
  fun _ hm => labels_mem.mpr (List.mem_cons_of_mem _ hm)

theorem labels_support (Δ : Bounds) (modes : List ModVar) :
    ∀m∈labels Δ modes, ∀v∈m.expression.freeVariables, v∈modes := by
  intro m hm v hv
  have he := labels_mem.mp ⟨m,hm,rfl⟩
  rcases List.mem_cons.mp he with he | he
  · rw [he] at hv
    cases hv
  · exact tests_support he v hv

theorem labels_basis (Δ : Bounds) {modes : List ModVar} (b : Basis) (hm : b.modes = modes) :
    ∀p∈b.modalPairs, ∃m∈labels Δ modes, m.expression = p.2 := by
  intro p hp
  apply labels_mem.mpr
  rcases List.mem_append.mp hp with hp | hp
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp [labelExpressions, tests]
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
    apply List.mem_cons_of_mem
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨c,hm ▸ hc,rfl⟩

theorem Based.query_complete {names modes fixed layout} (hb : Based names modes fixed layout)
    (assumptions : Bounds) (endpoints : ComparisonShape → List (CompareTy × CompareTy))
    (hforms : ∀s b, ComparisonStructuralBasis.basis names modes fixed s = some b →
      ∀pair∈endpoints s, LatticeForm b.types pair.1 ∧ LatticeForm b.types pair.2) :
    ∃q, query assumptions endpoints layout = some q := by
  induction hb with
  | @leaf s b hb =>
    obtain ⟨bounds, hp⟩ := ComparisonStructuralNode.prepare_complete (hforms s b hb)
    exact ⟨nodeTheory assumptions b bounds, by simp [query,hp]⟩
  | @fork k b left right hb hl hr ihl ihr =>
    obtain ⟨bounds, hp⟩ := ComparisonStructuralNode.prepare_complete (hforms _ b hb)
    obtain ⟨ql, hql⟩ := ihl
    obtain ⟨qr, hqr⟩ := ihr
    simp [query,Layout.shape,hp,hql,hqr]

theorem run_complete {assumptions endpoints layout q}
    (hq : query assumptions endpoints layout = some q) :
    ∃threshold output, ∀fuel≥threshold, run fuel assumptions endpoints layout = .success output := by
  obtain ⟨threshold, output, he⟩ := CompactCNF.toCNF_complete q true
  exact ⟨threshold,output,fun fuel hf => by simp only [run,hq]; exact he fuel hf⟩

theorem run_correct {fuel assumptions endpoints layout output}
    (hr : run fuel assumptions endpoints layout = .success output) :
    ∃q, query assumptions endpoints layout = some q ∧
      ∀world, CNFHolds world output ↔ q.eval world = true := by
  cases hq : query assumptions endpoints layout <;> simp only [run,hq] at hr
  · cases hr
  · exact ⟨_,rfl,fun world => CompactCNF.toCNF_correct hr world⟩

theorem run_atoms {fuel assumptions endpoints layout output}
    (hr : run fuel assumptions endpoints layout = .success output) :
    ∃q, query assumptions endpoints layout = some q ∧
      ∀v∈CNFPropagation.atoms output, v∈q.atoms := by
  cases hq : query assumptions endpoints layout <;> simp only [run,hq] at hr
  · cases hr
  · exact ⟨_,rfl,fun _ hv => CompactCNF.toCNF_atoms hr (by simpa [CNFPropagation.atoms] using hv)⟩

theorem run_observer {Δ : Bounds} {names modes fixed layout}
    (hb : Based names modes fixed layout)
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (fixed v))
    {endpoints : ComparisonShape → List (CompareTy × CompareTy)}
    (hinput : ∀s,∀pair∈endpoints s, AlgebraSubtype Δ pair.1 pair.2)
    {fuel output} (hr : run fuel Δ endpoints layout = .success output)
    (f : LatticeHom (Order Δ layout.shape) Bool) :
    ∃c η world, Observes layout.basis f c η world ∧ CNFHolds world output := by
  have hv := hb.valid hs
  let anchor := represented (hv.heads layout.basis.head (by simp [Basis.heads]))
  obtain ⟨c,η,hm⟩ := observer_model f anchor (labels Δ modes)
  obtain ⟨q,hq,hqcorrect⟩ := run_correct hr
  obtain ⟨world,ho,hw,_⟩ := query_realized (labels_tests Δ modes) (labels_support Δ modes)
    (fun b => labels_basis Δ b) hinput hv hq f hm
  exact ⟨c,η,world,ho,(hqcorrect world).mpr hw⟩

theorem Realized.observes {Δ labels layout f c η world}
    (h : Realized Δ labels layout f c η world) : Observes layout.basis f c η world := by
  cases h <;> assumption

theorem Realized.model {Δ labels layout f c η world}
    (h : Realized Δ labels layout f c η world) : Model f labels c η := by
  cases h <;> assumption

theorem run_realized {Δ : Bounds} {names modes fixed layout}
    (hb : Based names modes fixed layout)
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (fixed v))
    {endpoints : ComparisonShape → List (CompareTy × CompareTy)}
    (hinput : ∀s,∀pair∈endpoints s, AlgebraSubtype Δ pair.1 pair.2)
    {fuel output} (hr : run fuel Δ endpoints layout = .success output)
    (f : LatticeHom (Order Δ layout.shape) Bool) :
    ∃c η world, CNFHolds world output ∧ Realized Δ (labels Δ modes) layout f c η world := by
  have hv := hb.valid hs
  let anchor := represented (hv.heads layout.basis.head (by simp [Basis.heads]))
  obtain ⟨c,η,hm⟩ := observer_model f anchor (labels Δ modes)
  obtain ⟨q,hq,hqcorrect⟩ := run_correct hr
  obtain ⟨world,_,hw,htree⟩ := query_realized (labels_tests Δ modes) (labels_support Δ modes)
    (fun b => labels_basis Δ b) hinput hv hq f hm
  exact ⟨c,η,world,(hqcorrect world).mpr hw,htree⟩

theorem selected_complete {shapeLayout : ComparisonShapeSelectors.Layout}
    {names modes fixed s branch}
    (hbranch : branch∈ComparisonSelectedBases.bases shapeLayout names modes fixed s) :
    ∃layout, selected names modes fixed branch = some layout ∧ layout.shape = branch.shape ∧
      layout.basis = branch.basis ∧ Based names modes fixed layout := by
  obtain ⟨_,_,_,_,hb⟩ := ComparisonSelectedBases.bases_origin hbranch
  exact build_complete names modes fixed branch.shape hb

/-- Actual selected bases compile at a common eventual fuel. Every actual root
observer supplies a coherent active subtree and one shared Boolean valuation.
The converse, extending arbitrary satisfying finite tables, is separate. -/
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
        ∃c η world, CNFHolds world output ∧ Realized Δ (labels Δ modes) layout f c η world := by
  obtain ⟨layout,hl,hshape,hbasis,hb⟩ := selected_complete hbranch
  obtain ⟨q,hq⟩ := hb.query_complete Δ endpoints hforms
  obtain ⟨threshold,output,hr⟩ := run_complete hq
  exact ⟨layout,threshold,output,hl,hshape,hbasis,hr,
    fun f => run_realized hb hs hinput (hr threshold (le_refl _)) f⟩

/-- The local and two recursive namespaces are pairwise disjoint. -/
theorem atom_namespaces (i j : Nat) :
    localAtom i ≠ leftAtom j ∧ localAtom i ≠ rightAtom j ∧ leftAtom i ≠ rightAtom j := by
  simp only [localAtom,leftAtom,rightAtom]
  omega

theorem local_namespaces (i j : Nat) :
    basisAtom i ≠ headAtom j ∧ basisAtom i ≠ modeAtom j ∧ basisAtom i ≠ choiceAtom j ∧
      headAtom i ≠ modeAtom j ∧ headAtom i ≠ choiceAtom j ∧ modeAtom i ≠ choiceAtom j := by
  simp only [basisAtom,headAtom,modeAtom,choiceAtom,localAtom]
  omega

/-- Copying a scalar world renames the evaluation of one common symbolic
substitution; it does not create a separately chosen substitution. -/
theorem shared_strategy_eval (route : Nat → Nat) (strategy : Nat → BoolExpr)
    (expression : BoolExpr) (world : Nat → Bool) :
    (rename route (rename modeAtom (SymbolicCNF.substitute strategy expression))).eval world =
      expression.eval (fun i => (strategy i).eval (fun j => world (route (modeAtom j)))) := by
  simp only [rename_eval, SymbolicCNF.substitute_eval, Function.comp_def]

end ModalityInference.ComparisonStructuralLayout
