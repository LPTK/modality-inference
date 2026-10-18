import ModalityInference.Proofs.ComparisonStructuralCoherence
import ModalityInference.Proofs.ComparisonCoordinateTransition

/-! A satisfying finite node decodes to one guarded coordinate world.
Retained scalar names determine the world; unused names receive identity.
The finite control equations reconstruct basis values and whole endpoint
implications without assuming an already valid parent observer. -/
namespace ModalityInference.ComparisonStructuralWorld
open ComparisonControls ComparisonAlgebra ComparisonStructuralLayout
  ComparisonStructuralCoherence

private theorem all_eval (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all es).eval world = true ↔ ∀e∈es,e.eval world = true := by
  induction es <;> simp_all [BoolExpr.all,BoolExpr.eval]

private theorem any_eval (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any es).eval world = true ↔ ∃e∈es,e.eval world = true := by
  induction es <;> simp_all [BoolExpr.any,BoolExpr.eval]

private theorem equal_eval (a b : BoolExpr) (world : Nat → Bool) :
    (BoolExpr.equal a b).eval world = true ↔ a.eval world = b.eval world := by
  cases ha : a.eval world <;> cases hb : b.eval world <;>
    simp_all [BoolExpr.equal,BoolExpr.eval]

def range (world : Nat → Bool) (x : Bool) : Prop :=
  world (choiceAtom (if x then 4 else 3)) = true

def modes (names : List ModVar) (world : Nat → Bool) (v : ModVar) : Mode :=
  if v∈names then projectedModes (world ∘ modeAtom) v else Mode.identity

theorem modes_fixed {names world v} (h : v∈names) :
    modes names world v = projectedModes (world ∘ modeAtom) v := by simp [modes,h]

theorem modes_model {Δ : Bounds} {names : List ModVar} {world : Nat → Bool}
    (hs : ∀v∈Δ.modVars,v∈names) (h : ModeModels Δ (projectedModes (world ∘ modeAtom))) :
    ModeModels Δ (modes names world) :=
  (ModeModels.congr Δ (fun v hv => modes_fixed (hs v hv))).mpr h

theorem coordinateTest_iff (c : Coordinate) (world : Nat → Bool) :
    (coordinateTest c).eval world = true ↔
      world (choiceAtom 1) = (coordinateBits c).1 ∧
      world (choiceAtom 2) = (coordinateBits c).2 := by
  simp [coordinateTest,BoolExpr.eval,Bool.and_eq_true,equal_eval]

theorem theoryAt_entries {b : Basis} {c : Coordinate} {world : Nat → Bool}
    (h : (b.theoryAt basisAtom headAtom modeAtom c).eval world = true)
    (i : Nat) (hi : i<b.keys.length) :
    world (basisAtom i) = (b.formula headAtom modeAtom c b.keys[i]).eval world := by
  have hmem : BoolExpr.equal (.atom (basisAtom i))
      (b.formula headAtom modeAtom c b.keys[i]) ∈
      b.keys.mapIdx (fun i k => .equal (.atom (basisAtom i)) (b.formula headAtom modeAtom c k)) :=
    List.mem_iff_getElem.mpr ⟨i,by simpa using hi,by simp⟩
  have hh := (all_eval _ _).mp h _ hmem
  exact (equal_eval _ _ world).mp hh

structure View (Δ : Bounds) (names : List ModVar) (basis : Basis)
    (world : Nat → Bool) where
  coordinate : Coordinate
  first : world (choiceAtom 1) = (coordinateBits coordinate).1
  second : world (choiceAtom 2) = (coordinateBits coordinate).2
  scalar : coordinate = .unaffected ∨ ModeModels Δ (modes names world)
  controls : (basis.theoryAt basisAtom headAtom modeAtom coordinate).eval world = true
  ranges : (rangeTheory basis).eval world = true

theorem nodeTheory_view {Δ : Bounds} {names : List ModVar} {basis : Basis}
    {bounds : List ComparisonStructuralNode.Bound} {world : Nat → Bool}
    (hs : ∀v∈Δ.modVars,v∈names)
    (h : (nodeTheory Δ basis bounds).eval world = true) :
    Nonempty (View Δ names basis world) := by
  simp only [nodeTheory,BoolExpr.eval,Bool.and_eq_true] at h
  obtain ⟨e,he,hc⟩ := (any_eval _ _).mp h.2.1
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp he
  simp only [BoolExpr.eval,Bool.and_eq_true] at hc
  have hb := (coordinateTest_iff c world).mp hc.1
  refine ⟨⟨c,hb.1,hb.2,?_,hc.2.1,h.1⟩⟩
  cases c with
  | unaffected => exact .inl rfl
  | locality | affinity | uniqueness =>
    right
    apply modes_model hs
    apply (boundsModeFormula_correct Δ _).mp
    have he := hc.2.2
    change (rename modeAtom (boundsModeFormula Δ)).eval world = true at he
    simpa only [rename_eval] using he

theorem modes_eval {names world} {m : ModExpr} (hs : ∀v∈m.vars,v∈names) :
    m.eval (some ∘ modes names world) = m.eval (some ∘ projectedModes (world ∘ modeAtom)) :=
  m.eval_congr (fun v hv => congrArg some (modes_fixed (hs v hv)))

theorem modes_complete {names world} {m : ModExpr} (hs : ∀v∈m.vars,v∈names)
    (ht : m.WellFormed (projectedModes (world ∘ modeAtom))) :
    m.complete (modes names world) = m.complete (projectedModes (world ∘ modeAtom)) := by
  obtain ⟨n,hn⟩ := Option.isSome_iff_exists.mp ht
  exact (ModExpr.complete_of_eval ((modes_eval hs).trans hn)).trans
    (ModExpr.complete_of_eval hn).symm

theorem modalWith_value {names : List ModVar} {world : Nat → Bool} (c : Coordinate)
    (e : BoolExpr) {m : ModExpr} (hs : ∀v∈m.vars,v∈names)
    (ht : m.WellFormed (projectedModes (world ∘ modeAtom))) :
    (c.modalWith modeAtom e m).eval world =
      coordinateValue c (e.eval world) (m.complete (modes names world)) := by
  rw [modes_complete hs ht]
  obtain ⟨n,hn⟩ := Option.isSome_iff_exists.mp ht
  rw [ModExpr.complete_of_eval hn]
  apply Coordinate.modalWith_eval (η := projectedModes (world ∘ modeAtom)) _ (.inr hn)
  intro i
  exact (congrFun (SchemeModeSynthesis.encodeModes_projectedModes (world ∘ modeAtom)) i).symm

theorem modalPairs_support {basis : Basis} {pair : CompareTy × ModExpr}
    (hp : pair∈basis.modalPairs) :
    (∀v∈pair.2.vars,v∈basis.modes) ∧ ∀η,pair.2.WellFormed η := by
  obtain ⟨m,hm,he⟩ := labels_basis ([] : Bounds) basis rfl pair hp
  have hl := labels_mem.mp ⟨m,hm,he⟩
  refine ⟨?_,fun η => label_total hl η⟩
  intro v hv
  exact labels_support [] basis.modes m hm v
    (he.symm ▸ (pair.2.mem_freeVariables v).mpr hv)

theorem View.basis_value {Δ names basis world} (h : View Δ names basis world)
    (hm : basis.modes=names) (value : CompareTy → Bool)
    (hj : ∀a b,value (.join a b) = (value a || value b))
    (ht : ∀a b,value (.meet a b) = (value a && value b))
    (hh : ∀i (hi : i<basis.heads.length),world (headAtom i)=value basis.heads[i])
    (ha : ∀a m,value (.modal a m)=coordinateValue h.coordinate (value a)
      (m.complete (modes names world))) :
    ∀i (hi : i<basis.types.length),world (basisAtom i)=value basis.types[i] := by
  intro i hi
  have hki : i<basis.keys.length := by simpa [Basis.types] using hi
  have he := theoryAt_entries h.controls i hki
  have hf := basis.formula_of_modal headAtom modeAtom h.coordinate world value hj ht hh
    (fun a m hp => (ha a m).trans (modalWith_value h.coordinate (.const (value a))
      (fun v hv => hm ▸ (modalPairs_support hp).1 v hv)
      ((modalPairs_support hp).2 _)).symm) _ (List.getElem_mem hki)
  simpa only [Basis.types,List.getElem_map] using he.trans hf

theorem sharedModes_equal {names : List ModVar} {world : Nat → Bool} {child : Nat → Nat}
    (h : (sharedModes names child).eval world = true) :
    modes names world = modes names (world ∘ child) := by
  funext v
  by_cases hv : v∈names
  · rw [modes_fixed hv,modes_fixed hv]
    have hi (i : Nat) (hi : i<3) :
        world (modeAtom (v.atomIndex i)) = world (child (modeAtom (v.atomIndex i))) := by
      apply (equal_eval (.atom (modeAtom (v.atomIndex i)))
        (.atom (child (modeAtom (v.atomIndex i)))) world).mp
      apply (all_eval _ _).mp h
      exact List.mem_flatMap.mpr ⟨v,hv,List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩⟩
    simp only [projectedModes,Function.comp_def]
    rw [hi 0 (by decide),hi 1 (by decide),hi 2 (by decide)]
  · simp [modes,hv]

theorem childCoordinate_correct {parent child : Coordinate} {world : Nat → Bool}
    {route : Nat → Nat}
    (hp₁ : world (choiceAtom 1) = (coordinateBits parent).1)
    (hp₂ : world (choiceAtom 2) = (coordinateBits parent).2)
    (hc₁ : world (route (choiceAtom 1)) = (coordinateBits child).1)
    (hc₂ : world (route (choiceAtom 2)) = (coordinateBits child).2) :
    (childCoordinate route).eval world = true ↔ child=.unaffected ∨ child=parent := by
  have hp := coordinateTest_correct hp₁ hp₂
  have hc := coordinateTest_correct (world := world ∘ route) hc₁ hc₂
  simp only [childCoordinate,BoolExpr.eval,Bool.or_eq_true,rename_eval,hc,any_eval]
  constructor
  · rintro (h | ⟨e,he,h⟩)
    · exact .inl h.symm
    · obtain ⟨d,_,rfl⟩ := List.mem_map.mp he
      have hh : (coordinateTest d).eval world = true ∧
          (coordinateTest d).eval (world ∘ route) = true := by
        simpa only [BoolExpr.eval,Bool.and_eq_true,rename_eval] using h
      exact .inr (((hc d).mp hh.2).symm.trans ((hp d).mp hh.1))
  · rintro (h | h)
    · exact .inl h.symm
    · right
      refine ⟨_,List.mem_map.mpr ⟨parent,?_,rfl⟩,?_⟩
      · cases parent <;> simp
      · simp only [BoolExpr.eval,Bool.and_eq_true,rename_eval]
        exact ⟨(hp parent).mpr rfl,(hc parent).mpr h.symm⟩

theorem childTheory_inherits {Δ names basis childBasis world route k}
    (hp : View Δ names basis world) (hc : View Δ names childBasis (world ∘ route))
    (hk : k.dual=false) (h : (childTheory k names route).eval world=true) :
    modes names world=modes names (world ∘ route) ∧
      (hc.coordinate=.unaffected ∨ hc.coordinate=hp.coordinate) := by
  simp only [childTheory,hk,Bool.false_eq_true,if_false,BoolExpr.eval,Bool.and_eq_true] at h
  exact ⟨sharedModes_equal h.2,
    (childCoordinate_correct hp.first hp.second hc.first hc.second).mp h.1⟩

theorem View.range_nonempty {Δ names basis world} (h : View Δ names basis world) :
    ∃x,range world x := by
  have hh := h.ranges
  simp only [rangeTheory,BoolExpr.eval,Bool.and_eq_true,Bool.or_eq_true] at hh
  rcases hh.1 with hh|hh
  · exact ⟨false,hh⟩
  · exact ⟨true,hh⟩

theorem View.basis_range {Δ names basis world} (h : View Δ names basis world)
    (i : Nat) (hi : i<basis.types.length) : range world (world (basisAtom i)) := by
  have hh := h.ranges
  simp only [rangeTheory,BoolExpr.eval,Bool.and_eq_true] at hh
  have hx := (all_eval _ _).mp hh.2 _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)
  cases he : world (basisAtom i) <;>
    simpa [range,BoolExpr.eval,he] using hx

def headValue (basis : Basis) (world : Nat → Bool) (t : CompareTy) : Bool :=
  world (headAtom (basis.heads.idxOf t))

theorem View.head_range {Δ names basis world} (h : View Δ names basis world)
    {t : CompareTy} (ht : t∈basis.heads) : range world (headValue basis world t) := by
  obtain ⟨i,hi⟩ := index_exists (b := basis) (k := .head t)
    (by simp only [Basis.keys,List.mem_append,List.mem_map]; exact .inl (.inl ⟨t,ht,rfl⟩))
  have he := theoryAt_index h.controls hi
  have hr := h.basis_range i (index_bound hi)
  change world (basisAtom i) = headValue basis world t at he
  exact he ▸ hr

theorem View.closed_range {Δ names basis world} (h : View Δ names basis world)
    (hc : rangeClosure.eval world=true) : ClosedRange h.coordinate (range world) :=
  (rangeClosure_correct h.first h.second (range world) Iff.rfl Iff.rfl).mp hc

theorem nodeTheory_values {Δ basis bounds world}
    (h : (nodeTheory Δ basis bounds).eval world=true)
    {input : List (CompareTy × CompareTy)}
    (hp : ComparisonStructuralNode.prepare basis input=some bounds)
    (value : CompareTy → Bool)
    (hj : ∀a b,value (.join a b)=(value a || value b))
    (hm : ∀a b,value (.meet a b)=(value a && value b))
    (hb : ∀i (hi : i<basis.types.length),world (basisAtom i)=value basis.types[i]) :
    ∀pair∈input,value pair.1≤value pair.2 := by
  simp only [nodeTheory,BoolExpr.eval,Bool.and_eq_true] at h
  have he := h.2.2
  rw [ComparisonStructuralFamily.cnfFormula_eval] at he
  have hh := (ComparisonStructuralMatrix.cnfValue_correct world _).mp he
  have hpairs := (ComparisonStructuralNode.prepare_value hp value hj hm hb).mp
    ((ComparisonStructuralNode.clauses_correct basisAtom bounds world).mp hh)
  exact fun pair hpair => Bool.le_iff_imp.mpr (hpairs pair hpair)

end ModalityInference.ComparisonStructuralWorld
