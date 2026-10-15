import ModalityInference.Proofs.ComparisonJointGroupInvariance
import ModalityInference.Proofs.ComparisonJointAxes
import ModalityInference.Proofs.ComparisonOpaqueSlice
import ModalityInference.Proofs.SchemeModeWitness
import ModalityInference.Proofs.ComparisonGroupExtraction
import ModalityInference.Proofs.ComparisonEliminationSupport

/-! An admissible algebraic witness supplies compatible observations for the
actual joint group compiler. Scalar projections extend guarded images without
changing their value under the declared assumptions. -/
namespace ModalityInference.ComparisonJointGroup

open ComparisonControls ComparisonOpaqueObserver

/-- Raw scalar coordinates retain their axis dependencies outside the domain
where the original partial scalar expressions are defined. -/
def rawValue (c : Coordinate) (inputs : Nat → Bool) (heads : TypeVar → Bool) : CompareTy → Bool
  | .var v => heads v
  | .modal a m => apply c inputs (rawValue c inputs heads a) m
  | .join a b => rawValue c inputs heads a || rawValue c inputs heads b
  | .meet a b => rawValue c inputs heads a && rawValue c inputs heads b
  | _ => false

theorem apply_unaffected (inputs : Nat → Bool) (a : Bool) (m : ModExpr) :
    apply .unaffected inputs a m = a := rfl

theorem apply_value (c : Coordinate) (inputs : Nat → Bool) (a : Bool) (m : ModExpr)
    (hm : m.WellFormed (projectedModes inputs)) :
    apply c inputs a m = applyMode c a (m.complete (projectedModes inputs)) := by
  simpa only [apply, Coordinate.modal, Function.comp_id, BoolExpr.eval] using
    modalWith_value c id inputs (.const a) m hm

theorem rawValue_unaffected (inputs other : Nat → Bool) (heads : TypeVar → Bool) (a : CompareTy) :
    rawValue .unaffected inputs heads a = rawValue .unaffected other heads a := by
  induction a <;> simp_all only [rawValue, apply_unaffected]

theorem rawValue_value {a : CompareTy} {c : Coordinate} {inputs : Nat → Bool}
    (heads : TypeVar → Bool)
    (hd : c = .unaffected ∨ ModeModels a.wellFormedBounds (projectedModes inputs)) :
    rawValue c inputs heads a = value c (projectedModes inputs) heads a := by
  induction a with
  | var | unit | credit | prod | sum | fn => rfl
  | modal a m ih =>
    rcases hd with rfl | hd
    · exact ih (.inl rfl)
    · have ha : ModeModels a.wellFormedBounds (projectedModes inputs) :=
        fun c hc => hd c (List.mem_append_left _ hc)
      have hm : m.WellFormed (projectedModes inputs) :=
        hd (.defined m) (List.mem_append_right _ (by simp))
      simp only [rawValue, value, apply_value c inputs _ m hm, ih (.inr ha)]
  | join a b iha ihb | meet a b iha ihb =>
    have ha : c = .unaffected ∨ ModeModels a.wellFormedBounds (projectedModes inputs) :=
      hd.imp_right (fun h d hd => h d (List.mem_append_left _ hd))
    have hb : c = .unaffected ∨ ModeModels b.wellFormedBounds (projectedModes inputs) :=
      hd.imp_right (fun h d hd => h d (List.mem_append_right _ hd))
    simp only [rawValue, value, iha ha, ihb hb]

theorem projection_subst (m : ModExpr) (images : ModVar → ModExpr) (inputs : Nat → Bool) :
    (m.subst images).project.locality.eval inputs =
        m.project.locality.eval (SchemeModeSynthesis.strategy images inputs) ∧
    (m.subst images).project.affinity.eval inputs =
        m.project.affinity.eval (SchemeModeSynthesis.strategy images inputs) ∧
    (m.subst images).project.uniqueness.eval inputs =
        m.project.uniqueness.eval (SchemeModeSynthesis.strategy images inputs) := by
  induction m <;> simp_all [ModExpr.subst, ModExpr.project, BoolExpr.eval]
  case var v =>
    simp [SchemeModeSynthesis.strategy_coordinate, SchemeModeSynthesis.coordinate]

theorem apply_subst (c : Coordinate) (m : ModExpr) (images : ModVar → ModExpr)
    (inputs : Nat → Bool) (a : Bool) :
    apply c inputs a (m.subst images) = apply c (SchemeModeSynthesis.strategy images inputs) a m := by
  obtain ⟨hl, hf, hu⟩ := projection_subst m images inputs
  cases c <;> simp only [apply, Coordinate.modal, Coordinate.modalWith,
    SymbolicCNF.substitute_eval, BoolExpr.eval, id_eq, hl, hf, hu]

theorem apply_fixed (c : Coordinate) (m : ModExpr) (images : ModVar → ModExpr)
    (inputs : Nat → Bool) (a : Bool) (hf : ∀ v ∈ m.vars, images v = .var v) :
    apply c (SchemeModeSynthesis.strategy images inputs) a m = apply c inputs a m := by
  rw [← apply_subst]
  rw [(m.subst_congr hf).trans m.subst_id]

theorem apply_uniform (c : Coordinate) (m : ModExpr) (a : Bool) {inputs other : Nat → Bool}
    (h : ∀ i, ModalSynthesis.locality i = (c == .locality) → inputs i = other i) :
    apply c inputs a m = apply c other a m := by
  have hl := ComparisonControls.project_support m
  cases c with
  | unaffected => rfl
  | locality =>
    have he := SymbolicModes.eval_congr m.project.locality (fun i hi => h i (by
      simpa only [ModalSynthesis.locality, show (Coordinate.locality == .locality) = true from rfl,
        beq_iff_eq] using (hl.1 i hi).1))
    simpa only [apply, Coordinate.modal, Coordinate.modalWith, SymbolicCNF.substitute_eval,
      BoolExpr.eval, id_eq] using congrArg (fun b => a && b) he
  | affinity =>
    have he := SymbolicModes.eval_congr m.project.affinity (fun i hi => h i (by
      simpa only [ModalSynthesis.locality, show (Coordinate.affinity == .locality) = false from rfl,
        beq_eq_false_iff_ne] using (hl.2.1 i hi).1))
    simpa only [apply, Coordinate.modal, Coordinate.modalWith, SymbolicCNF.substitute_eval,
      BoolExpr.eval, id_eq] using congrArg (fun b => a && b) he
  | uniqueness =>
    have he := SymbolicModes.eval_congr m.project.uniqueness (fun i hi => h i (by
      simpa only [ModalSynthesis.locality, show (Coordinate.uniqueness == .locality) = false from rfl,
        beq_eq_false_iff_ne] using (hl.2.2 i hi).1))
    simpa only [apply, Coordinate.modal, Coordinate.modalWith, SymbolicCNF.substitute_eval,
      BoolExpr.eval, id_eq, Bool.or_false] using congrArg (fun b => a || !b) he

theorem rawValue_uniform (c : Coordinate) (a : CompareTy) (heads : TypeVar → Bool)
    {inputs other : Nat → Bool}
    (h : ∀ i, ModalSynthesis.locality i = (c == .locality) → inputs i = other i) :
    rawValue c inputs heads a = rawValue c other heads a := by
  induction a <;> simp_all only [rawValue]
  case modal a m ih => exact apply_uniform c m _ h

theorem rawValue_compatible (a : CompareTy) (heads : TypeVar → Bool) (inputs : Nat → Bool) :
    Below (rawValue .locality inputs heads a) (rawValue .unaffected inputs heads a) ∧
    Below (rawValue .affinity inputs heads a) (rawValue .unaffected inputs heads a) ∧
    Below (rawValue .unaffected inputs heads a) (rawValue .uniqueness inputs heads a) := by
  induction a <;> simp_all only [rawValue, apply, Coordinate.modal, Coordinate.modalWith,
    SymbolicCNF.substitute_eval, BoolExpr.eval, id_eq, Below, Bool.and_eq_true, Bool.or_eq_true,
    Bool.false_eq_true, and_self]
  all_goals tauto

theorem rawValue_nominal_constant {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (hφ : ComparisonShape.Models Δ φ) {s : TypeVar} {a : CompareTy}
    (hs : a.WellShaped Δ) (ha : a.shape.subst φ = .var s) (inputs : Nat → Bool) (b : Bool) :
    rawValue .unaffected inputs (fun _ => b) a = b := by
  induction a with
  | var v => rfl
  | unit | credit | prod | sum | fn => simp [CompareTy.shape, ComparisonShape.subst] at ha
  | modal a m ih => exact ih hs ha
  | join a d iha ihd | meet a d iha ihd =>
    have he := ihd hs.2.1 ((hs.2.2 φ hφ).symm.trans ha)
    simp only [rawValue, iha hs.1 ha, he, Bool.or_self, Bool.and_self]

theorem apply_epsilon (c : Coordinate) (inputs : Nat → Bool) (a : Bool) :
    apply c inputs a .epsilon = a := by
  cases c <;> simp [apply, Coordinate.modal, Coordinate.modalWith, ModExpr.project,
    ModExpr.epsilon, Mode.identity, SymbolicCNF.substitute_eval, BoolExpr.eval]

theorem apply_compose (c : Coordinate) (inputs : Nat → Bool) (a : Bool) (m n : ModExpr) :
    apply c inputs (apply c inputs a m) n = apply c inputs a (.compose m n) := by
  cases c <;> simp [apply, Coordinate.modal, Coordinate.modalWith, ModExpr.project,
    SymbolicCNF.substitute_eval, BoolExpr.eval, Bool.and_assoc, Bool.or_assoc]

theorem rawValue_outer (c : Coordinate) (inputs : Nat → Bool) (heads : TypeVar → Bool) (a : Ty) :
    rawValue c inputs heads (.ofTy a) =
      apply c inputs (rawValue c inputs heads (.ofTy a.outer.1)) a.outer.2 := by
  induction a with
  | var | unit | credit | prod | sum | fn => simp only [TypeExpr.outer, apply_epsilon]
  | modal a m ih =>
    simp only [CompareTy.ofTy, rawValue, TypeExpr.outer]
    rw [ih, apply_compose]

theorem rawValue_atom {a : Ty} {atom : ComparisonGroups.Atom}
    (h : ComparisonGroups.atom a = some atom)
    (c : Coordinate) (inputs : Nat → Bool) (heads : TypeVar → Bool) :
    rawValue c inputs heads (.ofTy a) = apply c inputs (heads atom.head) atom.mode := by
  simpa only [ComparisonGroups.atom_spec h, CompareTy.ofTy, rawValue] using rawValue_outer c inputs heads a

theorem atom_of_shape {φ : TypeVar → ComparisonShape} {s : TypeVar} {a : Ty}
    (h : (ComparisonShape.ofTy a).subst φ = .var s) :
    ∃ atom, ComparisonGroups.atom a = some atom ∧ φ atom.head = .var s ∧ atom.head ∈ a.typeVars := by
  induction a with
  | var v => exact ⟨⟨v, .epsilon⟩, rfl, h, by simp [TypeExpr.typeVars]⟩
  | unit | credit | prod | sum | fn => simp [ComparisonShape.ofTy, ComparisonShape.subst] at h
  | modal a m ih =>
    obtain ⟨atom, ha, hs, hv⟩ := ih h
    refine ⟨⟨atom.head, .compose atom.mode m⟩, ?_, hs, hv⟩
    simp only [ComparisonGroups.atom, TypeExpr.outer, ComparisonGroups.atom_spec ha]

theorem collect_assumption_coverage {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (h : ComparisonGroups.collect p shapes templates reduced = .success groups)
    {g : ComparisonGroups.Group} (hg : g ∈ groups) {a b : Ty}
    (hb : .sub a b ∈ p.assumptions) {pair : ComparisonGroups.Inequality}
    (hi : ComparisonGroups.inequality a b = some pair)
    (hc : ComparisonGroups.shapeClass shapes templates pair.1.head = some g.shapeClass) :
    pair ∈ g.assumptions := by
  unfold ComparisonGroups.collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    obtain ⟨c, hclass, rfl⟩ := List.mem_map.mp hg
    apply List.mem_filter.mpr
    refine ⟨List.mem_filterMap.mpr ⟨.sub a b, hb, hi⟩, ?_⟩
    exact beq_iff_eq.mpr hc
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List ComparisonGroups.Group)) PUnit => r.fst = none)
      (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

def parameterValue (heads : Nat) (headWorld modeWorld : Nat → Bool) (i : Nat) : Bool :=
  if i < heads then headWorld i else modeWorld (i - heads)

@[simp] theorem parameterValue_head (headWorld modeWorld : Nat → Bool) {i heads : Nat} (hi : i < heads) :
    parameterValue heads headWorld modeWorld i = headWorld i := by simp [parameterValue, hi]

@[simp] theorem modes_parameterValue (heads : Nat) (headWorld modeWorld : Nat → Bool) :
    modes heads (parameterValue heads headWorld modeWorld) = modeWorld := by
  funext i
  simp [modes, parameterValue]

def coordinateValue (values : Coordinate → Fin count → Bool) (i : Fin (4 * count)) : Bool :=
  if h : i.val < count then values .unaffected ⟨i.val, h⟩
  else if h : i.val < 2 * count then values .locality ⟨i.val - count, by omega⟩
  else if h : i.val < 3 * count then values .affinity ⟨i.val - 2 * count, by omega⟩
  else values .uniqueness ⟨i.val - 3 * count, by have := i.isLt; omega⟩

@[simp] theorem coordinateValue_state (values : Coordinate → Fin count → Bool)
    (c : Coordinate) (i : Fin count) : coordinateValue values (state c i) = values c i := by
  have hi := i.isLt
  cases c <;> simp only [coordinateValue, state, coordinateNumber]
  all_goals split_ifs <;> try omega
  all_goals (congr 1; ext; simp only; omega)

def witnessValues (g : ComparisonGroups.Group) (σ : CompareSubstitution)
    (headWorld inputs : Nat → Bool) : Fin (4 * g.leaves.length) → Bool :=
  coordinateValue fun c i => rawValue c inputs (fun v => headWorld (g.heads.idxOf v))
    (σ.type (.flex g.leaves[i]))

@[simp] theorem witnessValues_state (g : ComparisonGroups.Group) (σ : CompareSubstitution)
    (headWorld inputs : Nat → Bool) (c : Coordinate) (i : Fin g.leaves.length) :
    witnessValues g σ headWorld inputs (state c i) =
      rawValue c inputs (fun v => headWorld (g.heads.idxOf v)) (σ.type (.flex g.leaves[i])) :=
  coordinateValue_state _ _ _

theorem witnessValues_compatible (g : ComparisonGroups.Group) (σ : CompareSubstitution)
    (headWorld inputs : Nat → Bool) : Compatible (witnessValues g σ headWorld inputs) := by
  refine ⟨?_, ?_, ?_⟩
  all_goals intro i; simp only [witnessValues_state]
  · exact (rawValue_compatible _ _ _).1
  · exact (rawValue_compatible _ _ _).2.1
  · exact (rawValue_compatible _ _ _).2.2

theorem index_names_get {names : List Nat} {n : Nat} {i : Fin names.length}
    (h : index names n = some i) : names[i] = n := by
  unfold index at h
  dsimp only at h
  split at h
  · cases h
    exact List.getElem_idxOf _
  · cases h

theorem leafValue_witness {g : ComparisonGroups.Group} {σ : CompareSubstitution}
    (hf : ∀ v ∈ g.heads, σ.type v = .var v) {v : TypeVar}
    (hv : HeadCovered g.heads g.leaves v) (headWorld inputs : Nat → Bool) :
    leafValue g.heads g.leaves c
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs))
      (witnessValues g σ headWorld inputs) v =
      rawValue c inputs (fun v => headWorld (g.heads.idxOf v)) (σ.type v) := by
  cases v with
  | rigid n =>
    have hh : .rigid n ∈ g.heads := hv.resolve_right (by rintro ⟨_, _, he⟩; cases he)
    rw [hf _ hh]
    exact parameterValue_head _ _ (List.idxOf_lt_length_of_mem hh)
  | flex n =>
    cases hn : index g.leaves n with
    | some i => simp only [leafValue, hn, witnessValues_state, index_names_get hn]
    | none =>
      have hh : .flex n ∈ g.heads := by
        rcases hv with hv | ⟨k, hk, he⟩
        · exact hv
        · cases TypeVar.flex.inj he
          obtain ⟨i, hi⟩ := index_exists hk
          rw [hn] at hi
          cases hi
      rw [hf _ hh]
      simp only [leafValue, hn, rawValue]
      exact parameterValue_head _ _ (List.idxOf_lt_length_of_mem hh)

theorem atomValue_witness {g : ComparisonGroups.Group} {σ : CompareSubstitution}
    (hf : ∀ v ∈ g.heads, σ.type v = .var v) {a : ComparisonGroups.Atom}
    (hv : HeadCovered g.heads g.leaves a.head) (headWorld inputs : Nat → Bool) (c : Coordinate) :
    atomValue g.heads g.leaves c
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs))
      (witnessValues g σ headWorld inputs) a =
      rawValue c inputs (fun v => headWorld (g.heads.idxOf v)) (a.interpret σ) := by
  simp only [atomValue, modes_parameterValue, leafValue_witness hf hv,
    ComparisonGroups.Atom.interpret, rawValue, apply_subst]


theorem strategy_fixed_names {Δ : Bounds} {σ : CompareSubstitution}
    (hf : ∀ v ∈ Δ.modVars, σ.mode v = .var v) (inputs : Nat → Bool) :
    ∀ v ∈ Δ.modVars,
      projectedModes (SchemeModeSynthesis.strategy σ.mode inputs) v = projectedModes inputs v := by
  intro v hv
  simp only [projectedModes, SchemeModeSynthesis.strategy_coordinate σ.mode inputs v 0 (by decide),
    SchemeModeSynthesis.strategy_coordinate σ.mode inputs v 1 (by decide),
    SchemeModeSynthesis.strategy_coordinate σ.mode inputs v 2 (by decide), hf v hv,
    SchemeModeSynthesis.coordinate, ModExpr.project, BoolExpr.eval]

theorem strategy_models {Δ : Bounds} {σ : CompareSubstitution}
    (hf : ∀ v ∈ Δ.modVars, σ.mode v = .var v) (inputs : Nat → Bool) :
    ModeModels Δ (projectedModes (SchemeModeSynthesis.strategy σ.mode inputs)) ↔
      ModeModels Δ (projectedModes inputs) :=
  ModeModels.congr Δ (strategy_fixed_names hf inputs)

theorem scalar_witness {Δ required : Bounds} {σ : CompareSubstitution}
    (hf : ∀ v ∈ Δ.modVars, σ.mode v = .var v) (hw : σ.WellFormedUnder Δ)
    (hr : AlgebraEntailsAll Δ (σ.bounds required)) (inputs : Nat → Bool) :
    (boundsModeFormula Δ).eval (SchemeModeSynthesis.strategy σ.mode inputs) = true →
      (boundsModeFormula required).eval (SchemeModeSynthesis.strategy σ.mode inputs) = true := by
  intro hΔ
  have hη := (strategy_models hf inputs).mp ((boundsModeFormula_correct Δ _).mp hΔ)
  apply (boundsModeFormula_correct required _).mpr
  intro c hc
  apply (ModeSatisfies.subst_functions c TypeExpr.var σ.mode
    (fun v => SchemeModeSynthesis.strategy_eval σ.mode inputs v (hw.modes v _ hη))).mp
  have he := hr (σ.constraint c) (List.mem_map.mpr ⟨c, hc, rfl⟩)
  cases c with
  | sub | equal | equiv => trivial
  | mode a b => exact he.denote hη
  | defined m => exact he _ hη

theorem index_mem [BEq α] [LawfulBEq α] {names : List α} {v : α} {i : Fin names.length}
    (h : index names v = some i) : v ∈ names :=
  List.idxOf_lt_length_iff.mp ((index_value h) ▸ i.isLt)

private theorem mapM_success_forall {α β : Type} {f : α → RunResult β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .success ys) :
    ∀ x ∈ xs, ∃ y, f x = .success y := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hx : f x <;> simp only [hx] at h <;> try contradiction
    next y =>
      cases hxs : xs.mapM f <;> simp only [hxs] at h <;> try contradiction
      next rest =>
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨y, hx⟩
        · exact ih hxs z hz

private theorem fixed_mem {heads : List TypeVar} {c : Coordinate} {a : ComparisonGroups.Atom}
    {e : BoolExpr} (h : fixed heads c a = .success e) : a.head ∈ heads := by
  unfold fixed at h
  split at h <;> try contradiction
  exact index_mem (by assumption)

private theorem leaf_covered {heads : List TypeVar} {names : List Nat} {c : Coordinate}
    {v : TypeVar} {result : ComparisonPropagation.Leaf (4 * names.length)}
    (h : leaf heads names c v = .success result) : HeadCovered heads names v := by
  unfold leaf at h
  cases v with
  | rigid n =>
    cases hi : index heads (.rigid n) <;> simp only [hi] at h <;> try contradiction
    exact .inl (index_mem hi)
  | flex n =>
    cases hn : index names n with
    | some i => exact .inr ⟨n, index_mem hn, rfl⟩
    | none =>
      cases hi : index heads (.flex n) <;> simp only [hn, hi] at h <;> try contradiction
      exact .inl (index_mem hi)

theorem coordinate_covered {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {c : Coordinate} {result : CNF} (h : coordinate fuel assumptions required g c = .success result) :
    Covered g := by
  unfold coordinate at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i declared hd
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i goals hg
  constructor
  · intro pair hp
    obtain ⟨output, he⟩ := mapM_success_forall hd pair hp
    unfold fixedBound at he
    simp only [bind, pure, RunResult.bind] at he
    split at he <;> try contradiction
    rename_i _ hl
    split at he <;> try contradiction
    rename_i _ hr
    exact ⟨fixed_mem hl, fixed_mem hr⟩
  · intro pair hp
    obtain ⟨output, he⟩ := mapM_success_forall hg pair hp
    unfold bound at he
    simp only [bind, pure, RunResult.bind] at he
    split at he <;> try contradiction
    rename_i _ hl
    split at he <;> try contradiction
    rename_i _ hr
    exact ⟨leaf_covered hl, leaf_covered hr⟩

theorem prepare_covered {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (h : prepare fuel assumptions required g = .success result) : Covered g := by
  obtain ⟨_, _, _, hn, _⟩ := prepare_coordinates h
  exact coordinate_covered hn


theorem fixedValue_raw {g : ComparisonGroups.Group} {σ : CompareSubstitution}
    {a : Ty} {atom : ComparisonGroups.Atom} (ha : ComparisonGroups.atom a = some atom)
    (hh : atom.head ∈ g.heads) (hm : ∀ v ∈ a.modVars, σ.mode v = .var v)
    (headWorld inputs : Nat → Bool) (c : Coordinate) :
    fixedValue g.heads c
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs)) atom =
      rawValue c inputs (fun v => headWorld (g.heads.idxOf v)) (.ofTy a) := by
  rw [rawValue_atom ha]
  simp only [fixedValue, modes_parameterValue,
    parameterValue_head _ _ (List.idxOf_lt_length_of_mem hh)]
  apply apply_fixed
  intro v hv
  exact hm v (a.outer_modeVars_subset (by simpa only [ComparisonGroups.atom_spec ha] using hv))

/-- Actual collected assumptions cover every declared inequality visible at
the selected opaque shape. No consistency assumption is needed. -/
theorem collected_observer_assumptions {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hφ : ComparisonShape.Models p.assumptions shapes.fixedShapes)
    (hcollect : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hfresh : ∀ leaf ∈ templates.leaves, ∀ v ∈ p.assumptions.typeVars, v ≠ .flex leaf.name)
    (hd : p.assumptions.TypeBoundsDefined) {σ : CompareSubstitution}
    (hfixed : ∀ v ∈ p.assumptions.modVars, σ.mode v = .var v)
    {g : ComparisonGroups.Group} (hg : g ∈ groups) (hc : Covered g)
    (headWorld inputs : Nat → Bool) (c : Coordinate)
    (ht : TheoryHolds p.assumptions reduced.modes g c
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs))) :
    Assumptions p.assumptions shapes.fixedShapes g.shapeClass c (projectedModes inputs)
      (fun v => headWorld (g.heads.idxOf v)) := by
  have hη : c = .unaffected ∨ ModeModels p.assumptions (projectedModes inputs) := by
    rcases ht.2 with he | he
    · exact .inl he
    · simp only [modes_parameterValue, guards, BoolExpr.eval, Bool.and_eq_true] at he
      have he := he.1
      exact .inr ((strategy_models hfixed inputs).mp ((boundsModeFormula_correct _ _).mp he))
  intro a b hab ha
  have hb : (ComparisonShape.ofTy b).subst shapes.fixedShapes = .var g.shapeClass := by
    have he := hφ (ComparisonShape.ofTy a, ComparisonShape.ofTy b)
      (List.mem_flatMap.mpr ⟨.sub a b, hab, by simp⟩)
    exact he.symm.trans ha
  obtain ⟨left, hl, hls, hlv⟩ := atom_of_shape ha
  obtain ⟨right, hr, _, _⟩ := atom_of_shape hb
  have hi : ComparisonGroups.inequality a b = some (left, right) := by
    simp only [ComparisonGroups.inequality, hl, hr, bind, pure, Option.bind]
  have hclass := ComparisonGroups.shapeClass_fixed_of (fun leaf hleaf => hfresh leaf hleaf left.head
    ((p.assumptions.mem_typeVars_iff _).mpr ⟨.sub a b, hab, by simp [Constraint.typeVars, hlv]⟩)) hls
  have hpair := collect_assumption_coverage hcollect hg hab hi hclass
  have hh := hc.1 (left, right) hpair
  have hfa : ∀ v ∈ a.modVars, σ.mode v = .var v := fun v hv =>
    hfixed v ((p.assumptions.mem_modVars_iff _).mpr ⟨.sub a b, hab, by simp [Constraint.modVars, hv]⟩)
  have hfb : ∀ v ∈ b.modVars, σ.mode v = .var v := fun v hv =>
    hfixed v ((p.assumptions.mem_modVars_iff _).mpr ⟨.sub a b, hab, by simp [Constraint.modVars, hv]⟩)
  have he := ht.1 (left, right) hpair
  rw [fixedValue_raw hl hh.1 hfa, fixedValue_raw hr hh.2 hfb] at he
  rw [rawValue_value _ (hη.imp_right (fun h => (CompareTy.definedUnder_ofTy _ _).mpr (hd a b hab).1 _ h)),
    rawValue_value _ (hη.imp_right (fun h => (CompareTy.definedUnder_ofTy _ _).mpr (hd a b hab).2 _ h))] at he
  exact he


theorem collected_class_fixed {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hshape : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (hcollect : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    {g : ComparisonGroups.Group} (hg : g ∈ groups) {head : TypeVar} (hh : head ∈ g.heads) :
    shapes.fixedShapes g.shapeClass = .var g.shapeClass := by
  obtain ⟨hv, _, hc⟩ := ComparisonGroups.collect_head_origin hcollect g hg head hh
  have he := ComparisonGroups.shapeClass_fixed (fun leaf hl => hfresh leaf hl head hv) hc
  have hf := (ComparisonShapeSolver.prepare_solved_iff.mp hshape).1
  have hi := ComparisonShapeSolver.unify_factor hf (ComparisonShapeSolver.unify_sound hf) head
  change (shapes.fixedShapes head).subst shapes.fixedShapes = shapes.fixedShapes head at hi
  rw [he] at hi
  exact hi

theorem collected_image_shape {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hφ : ComparisonShape.Models p.assumptions shapes.fixedShapes)
    (hcollect : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    {σ : CompareSubstitution}
    (hleaf : ∀ leaf ∈ templates.leaves,
      ComparisonShape.Equivalent p.assumptions (σ.type (.flex leaf.name)).shape (.var leaf.shapeClass))
    {g : ComparisonGroups.Group} (hg : g ∈ groups)
    (hclass : shapes.fixedShapes g.shapeClass = .var g.shapeClass)
    (hfixed : ∀ v ∈ g.heads, σ.type v = .var v) {v : TypeVar}
    (hv : HeadCovered g.heads g.leaves v) :
    (σ.type v).shape.subst shapes.fixedShapes = .var g.shapeClass := by
  rcases hv with hv | ⟨n, hn, rfl⟩
  · rw [hfixed v hv]
    obtain ⟨hm, _, hc⟩ := ComparisonGroups.collect_head_origin hcollect g hg v hv
    exact ComparisonGroups.shapeClass_fixed (fun leaf hl => hfresh leaf hl v hm) hc
  · obtain ⟨leaf, hl, hn, hc⟩ := ComparisonGroups.collect_leaf_origin hcollect g hg n hn
    subst n
    exact (hleaf leaf hl _ hφ).trans (by simpa only [ComparisonShape.subst, hc] using hclass)

/-- The same admissible substitution satisfies all four observations of an
actual group. The raw coordinate extension is only compared with complete
scalar values at valuations satisfying the original guards. -/
theorem collected_group_witness {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hφ : ComparisonShape.Models p.assumptions shapes.fixedShapes)
    (hcollect : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (hd : p.assumptions.TypeBoundsDefined) {σ : CompareSubstitution}
    (hσ : σ.WellShaped p.assumptions) (hw : σ.WellFormedUnder p.assumptions)
    (hmfixed : ∀ v ∈ p.assumptions.modVars, σ.mode v = .var v)
    (hleaf : ∀ leaf ∈ templates.leaves,
      ComparisonShape.Equivalent p.assumptions (σ.type (.flex leaf.name)).shape (.var leaf.shapeClass))
    (hguards : ComparisonReduction.OpaqueGuards reduced)
    (hmodes : AlgebraEntailsAll p.assumptions (σ.bounds reduced.modes))
    (hgoals : ∀ pair ∈ reduced.inequalities, ComparisonReduction.PairHolds p.assumptions σ pair)
    {g : ComparisonGroups.Group} (hg : g ∈ groups) (hc : Covered g)
    (hclass : shapes.fixedShapes g.shapeClass = .var g.shapeClass)
    (htfixed : ∀ v ∈ g.heads, σ.type v = .var v) (headWorld inputs : Nat → Bool) :
    GroupHolds p.assumptions reduced.modes g
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs))
      (witnessValues g σ headWorld inputs) := by
  refine ⟨?_, witnessValues_compatible g σ headWorld inputs, ?_⟩
  · intro c ht pair hp
    have hη : c = .unaffected ∨ ModeModels p.assumptions (projectedModes inputs) := by
      rcases ht.2 with he | he
      · exact .inl he
      · simp only [modes_parameterValue, guards, BoolExpr.eval, Bool.and_eq_true] at he
        exact .inr ((strategy_models hmfixed inputs).mp ((boundsModeFormula_correct _ _).mp he.1))
    have ha := collected_observer_assumptions hφ hcollect
      (fun leaf hl v hv => hfresh leaf hl v (by simp [Bounds.mem_typeVariables, hv]))
      hd hmfixed hg hc headWorld inputs c ht
    obtain ⟨goal, hgoal, hi, _⟩ := ComparisonGroups.collect_goal_origin hcollect g hg pair hp
    obtain ⟨hgl, hgr⟩ := ComparisonGroups.collect_goal_guards hcollect hguards g hg pair hp
    have hml : Entails p.assumptions (.defined (pair.1.mode.subst σ.mode)) :=
      hmodes _ (List.mem_map.mpr ⟨.defined pair.1.mode, hgl, rfl⟩)
    have hmr : Entails p.assumptions (.defined (pair.2.mode.subst σ.mode)) :=
      hmodes _ (List.mem_map.mpr ⟨.defined pair.2.mode, hgr, rfl⟩)
    have hsub := (ComparisonGroups.inequality_algebra_iff hσ hi hml hmr).mp (hgoals goal hgoal)
    have hdl : pair.1.interpret σ |>.DefinedUnder p.assumptions :=
      CompareTy.definedUnder_modal_iff.mpr ⟨hw.types _, hml⟩
    have hdr : pair.2.interpret σ |>.DefinedUnder p.assumptions :=
      CompareTy.definedUnder_modal_iff.mpr ⟨hw.types _, hmr⟩
    have hshape := collected_image_shape hφ hcollect hfresh hleaf hg hclass htfixed (hc.2 pair hp).1
    have he := ComparisonOpaqueObserver.algebra hφ hη ha hsub hshape
    rw [← rawValue_value _ (hη.imp_right (hdl _)),
      ← rawValue_value _ (hη.imp_right (hdr _))] at he
    rw [atomValue_witness htfixed (hc.2 pair hp).1,
      atomValue_witness htfixed (hc.2 pair hp).2]
    exact he
  · simpa only [modes_parameterValue] using scalar_witness hmfixed hw hmodes inputs

/-- Successful compilation accepts the coordinate strategy induced by the
same guarded algebraic witness for the collected comparison obligations. -/
theorem prepare_witness {fuel shapeFuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hshape : ComparisonShapeSolver.prepare shapeFuel p = .success (.solved shapes))
    (hcollect : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    (hd : p.assumptions.TypeBoundsDefined) {σ : CompareSubstitution}
    (hσ : σ.WellShaped p.assumptions) (hw : σ.WellFormedUnder p.assumptions)
    (hmfixed : ∀ v ∈ p.assumptions.modVars, σ.mode v = .var v)
    (hleaf : ∀ leaf ∈ templates.leaves,
      ComparisonShape.Equivalent p.assumptions (σ.type (.flex leaf.name)).shape (.var leaf.shapeClass))
    (hguards : ComparisonReduction.OpaqueGuards reduced)
    (hmodes : AlgebraEntailsAll p.assumptions (σ.bounds reduced.modes))
    (hgoals : ∀ pair ∈ reduced.inequalities, ComparisonReduction.PairHolds p.assumptions σ pair)
    {g : ComparisonGroups.Group} (hg : g ∈ groups) {head : TypeVar} (hh : head ∈ g.heads)
    (htfixed : ∀ v ∈ g.heads, σ.type v = .var v) {result : Input}
    (hprepare : prepare fuel p.assumptions reduced.modes g = .success result)
    (headWorld inputs : Nat → Bool) :
    result.Holds g.heads.length
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs))
      (witnessValues g σ headWorld inputs) := by
  apply (prepare_correct hprepare _ _).mpr
  exact collected_group_witness
    (ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hshape).1)
    hcollect hfresh hd hσ hw hmfixed hleaf hguards hmodes hgoals hg (prepare_covered hprepare)
    (collected_class_fixed hshape hcollect hfresh hg hh) htfixed headWorld inputs


/-- Each axis problem retains its nominal state and fills unused observation
slots with a constant. This realizes the compiler's state-independence facts. -/
def axisValues (component : Bool) (g : ComparisonGroups.Group) (σ : CompareSubstitution)
    (headWorld inputs : Nat → Bool) : Fin (4 * g.leaves.length) → Bool :=
  coordinateValue fun c i =>
    match c with
    | .unaffected => rawValue c inputs (fun v => headWorld (g.heads.idxOf v)) (σ.type (.flex g.leaves[i]))
    | .locality => if component then
        rawValue c inputs (fun v => headWorld (g.heads.idxOf v)) (σ.type (.flex g.leaves[i])) else false
    | .affinity | .uniqueness => if component then false else
        rawValue c inputs (fun v => headWorld (g.heads.idxOf v)) (σ.type (.flex g.leaves[i]))

theorem coordinateValue_congr {left right : Coordinate → Fin count → Bool}
    (h : ∀ c i, left c i = right c i) : coordinateValue left = coordinateValue right := by
  exact congrArg coordinateValue (funext fun c => funext (h c))

@[simp] theorem axisValues_nominal (component : Bool) (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) (headWorld inputs : Nat → Bool) (i : Fin g.leaves.length) :
    axisValues component g σ headWorld inputs (state .unaffected i) =
      witnessValues g σ headWorld inputs (state .unaffected i) := by
  simp only [axisValues, coordinateValue_state, witnessValues_state]

@[simp] theorem axisValues_locality (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) (headWorld inputs : Nat → Bool) (i : Fin g.leaves.length) :
    axisValues true g σ headWorld inputs (state .locality i) =
      witnessValues g σ headWorld inputs (state .locality i) := by
  simp only [axisValues, coordinateValue_state, witnessValues_state, ↓reduceIte]

@[simp] theorem axisValues_affinity (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) (headWorld inputs : Nat → Bool) (i : Fin g.leaves.length) :
    axisValues false g σ headWorld inputs (state .affinity i) =
      witnessValues g σ headWorld inputs (state .affinity i) := by
  simp only [axisValues, coordinateValue_state, witnessValues_state, Bool.false_eq_true, ↓reduceIte]

@[simp] theorem axisValues_uniqueness (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) (headWorld inputs : Nat → Bool) (i : Fin g.leaves.length) :
    axisValues false g σ headWorld inputs (state .uniqueness i) =
      witnessValues g σ headWorld inputs (state .uniqueness i) := by
  simp only [axisValues, coordinateValue_state, witnessValues_state, Bool.false_eq_true, ↓reduceIte]

theorem axisValues_uniform (component : Bool) (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) :
    ComparisonJointAxes.StateUniform ModalSynthesis.locality component (axisValues component g σ) := by
  intro heads left right hh i
  apply congrFun (coordinateValue_congr ?_) i
  intro c j
  cases c with
  | unaffected => exact rawValue_unaffected left right _ _
  | locality =>
    cases component with
    | false => rfl
    | true => exact rawValue_uniform .locality _ _ hh
  | affinity =>
    cases component with
    | false => exact rawValue_uniform .affinity _ _ hh
    | true => rfl
  | uniqueness =>
    cases component with
    | false => exact rawValue_uniform .uniqueness _ _ hh
    | true => rfl

theorem parameterValue_valuation (g : ComparisonGroups.Group)
    (values : ComparisonJointAxes.State (4 * g.leaves.length))
    (strategy : (Nat → Bool) → Nat → Bool) (headWorld inputs : Nat → Bool) :
    ComparisonJointEncoding.valuation (values headWorld inputs)
        (parameterValue g.heads.length headWorld (strategy inputs)) =
      ComparisonJointAxes.valuation g.heads.length values strategy headWorld inputs := by
  funext v
  simp only [ComparisonJointEncoding.valuation, ComparisonJointAxes.valuation]
  split
  · rfl
  · rename_i h
    simp only [parameterValue]
    split_ifs <;> try omega
    · rfl
    · congr 1
      omega

/-- The nominal image is independent of every scalar input. -/
theorem witnessValues_nominal_independent (g : ComparisonGroups.Group) (σ : CompareSubstitution)
    (headWorld left right : Nat → Bool) (i : Fin g.leaves.length) :
    witnessValues g σ headWorld left (state .unaffected i) =
      witnessValues g σ headWorld right (state .unaffected i) := by
  simp only [witnessValues_state]
  exact rawValue_unaffected left right _ _

/-- Actual input validity is preserved when unused coordinate slots are removed
for the two independent axis solvers. -/
theorem prepare_axis_witness {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (hprepare : prepare fuel assumptions required g = .success result)
    {σ : CompareSubstitution} {headWorld inputs : Nat → Bool}
    (h : result.Holds g.heads.length
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs))
      (witnessValues g σ headWorld inputs)) :
    CNFHolds (ComparisonJointAxes.valuation g.heads.length (axisValues true g σ)
      (SchemeModeSynthesis.strategy σ.mode) headWorld inputs) result.locality ∧
    CNFHolds (ComparisonJointAxes.valuation g.heads.length (axisValues false g σ)
      (SchemeModeSynthesis.strategy σ.mode) headWorld inputs) result.other := by
  constructor
  · rw [← parameterValue_valuation]
    exact (prepare_locality_congr hprepare (by simp) (by simp)).mpr h.2.1
  · rw [← parameterValue_valuation]
    exact (prepare_other_congr hprepare (by simp) (by simp) (by simp)).mpr h.2.2.1

/-- Shape-compatible opaque images have genuine positive nominal boundaries,
including when their modality annotations have only conditional guards. -/
theorem witnessValues_nominal_constant {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hφ : ComparisonShape.Models p.assumptions shapes.fixedShapes)
    (hcollect : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    {σ : CompareSubstitution} (hσ : σ.WellShaped p.assumptions)
    (hleaf : ∀ leaf ∈ templates.leaves,
      ComparisonShape.Equivalent p.assumptions (σ.type (.flex leaf.name)).shape (.var leaf.shapeClass))
    {g : ComparisonGroups.Group} (hg : g ∈ groups)
    (hclass : shapes.fixedShapes g.shapeClass = .var g.shapeClass)
    (hfixed : ∀ v ∈ g.heads, σ.type v = .var v) (inputs : Nat → Bool)
    (b : Bool) (i : Fin g.leaves.length) :
    witnessValues g σ (fun _ => b) inputs (state .unaffected i) = b := by
  have hs := collected_image_shape hφ hcollect hfresh hleaf hg hclass hfixed
    (.inr ⟨g.leaves[i], List.getElem_mem _, rfl⟩)
  simpa only [witnessValues_state] using rawValue_nominal_constant hφ (hσ.type _) hs inputs b


/-- Nominal observations are extracted directly as positive head CNFs. -/
def nominalFormula (heads : List TypeVar) : CompareTy → CNF
  | .var v => [[(heads.idxOf v, true)]]
  | .modal a _ => nominalFormula heads a
  | .join a b => ComparisonPropagation.join (nominalFormula heads a) (nominalFormula heads b)
  | .meet a b => ComparisonPropagation.meet (nominalFormula heads a) (nominalFormula heads b)
  | _ => [[]]

theorem nominalFormula_correct (heads : List TypeVar) (a : CompareTy)
    (headWorld inputs : Nat → Bool) :
    CNFHolds headWorld (nominalFormula heads a) ↔
      rawValue .unaffected inputs (fun v => headWorld (heads.idxOf v)) a = true := by
  induction a <;> simp_all only [nominalFormula, rawValue, apply_unaffected,
    ComparisonPropagation.join_correct, ComparisonPropagation.meet_correct,
    Bool.or_eq_true, Bool.and_eq_true]
  all_goals simp [CNFHolds, ClauseHolds]

theorem nominalFormula_positive (heads : List TypeVar) (a : CompareTy) :
    ComparisonPropagation.Positive (nominalFormula heads a) := by
  induction a <;> simp only [nominalFormula]
  case var v => simp [ComparisonPropagation.Positive]
  case unit | credit | prod | sum | fn => simp [ComparisonPropagation.Positive]
  case modal a m ih => exact ih
  case join a b iha ihb => exact ComparisonPropagation.join_positive iha ihb
  case meet a b iha ihb =>
    intro clause hc literal hl
    obtain ⟨d, hd, hl⟩ := CompactCNF.clean_literal hc hl
    exact (List.mem_append.mp hd).elim (fun h => iha d h literal hl) (fun h => ihb d h literal hl)

theorem nominalFormula_supported {heads : List TypeVar} {a : CompareTy}
    (hs : ComparisonInterpolation.Supports (· ∈ heads) (fun _ => True) a) :
    ComparisonPropagation.Supported (List.range heads.length) (nominalFormula heads a) := by
  induction a <;> simp only [ComparisonInterpolation.Supports] at hs
  case var v =>
    intro w hw
    have he : w = heads.idxOf v := by simpa [nominalFormula, CNFPropagation.atoms] using hw
    subst w
    exact List.mem_range.mpr (List.idxOf_lt_length_of_mem hs)
  case unit | credit | prod | sum | fn => simp [ComparisonPropagation.Supported, nominalFormula, CNFPropagation.atoms]
  case modal a m ih => exact ih hs.1
  case join a b iha ihb => exact ComparisonPropagation.join_supported (iha hs.1) (ihb hs.2)
  case meet a b iha ihb =>
    intro v hv
    obtain ⟨clause, hc, polarity, hl⟩ := CNFPropagation.mem_atoms.mp (CompactCNF.clean_atoms hv)
    exact (List.mem_append.mp hc).elim
      (fun h => iha hs.1 v (CNFPropagation.mem_atoms.mpr ⟨clause, h, polarity, hl⟩))
      (fun h => ihb hs.2 v (CNFPropagation.mem_atoms.mpr ⟨clause, h, polarity, hl⟩))

theorem opaque_head_support {Δ : Bounds} {φ : TypeVar → ComparisonShape}
    (hφ : ComparisonShape.Models Δ φ) {s : TypeVar} {heads : List TypeVar} {a : CompareTy}
    (hs : a.WellShaped Δ) (ha : a.shape.subst φ = .var s)
    (hh : ∀ v, φ v = .var s → v ∈ heads) :
    ComparisonInterpolation.Supports (· ∈ heads) (fun _ => True) a := by
  induction a with
  | var v => exact hh v ha
  | unit | credit | prod | sum | fn => simp [CompareTy.shape, ComparisonShape.subst] at ha
  | modal a m ih => exact ⟨ih hs ha, by simp⟩
  | join a b iha ihb | meet a b iha ihb =>
    exact ⟨iha hs.1 ha, ihb hs.2.1 ((hs.2.2 φ hφ).symm.trans ha)⟩

def nominalStore (g : ComparisonGroups.Group) (σ : CompareSubstitution) :
    ComparisonPropagation.Store g.leaves.length :=
  Vector.ofFn fun i => nominalFormula g.heads (σ.type (.flex g.leaves[i]))

theorem nominalStore_correct (g : ComparisonGroups.Group) (σ : CompareSubstitution)
    (headWorld inputs : Nat → Bool) (i : Fin g.leaves.length) :
    CNFHolds headWorld (nominalStore g σ)[i] ↔
      witnessValues g σ headWorld inputs (state .unaffected i) = true := by
  simpa only [nominalStore, Fin.getElem_fin, Vector.getElem_ofFn, witnessValues_state] using
    nominalFormula_correct g.heads (σ.type (.flex g.leaves[i])) headWorld inputs

/-- Every admissible opaque image gives an actual finite positive nominal
store over the retained heads, with both normalized boundary values. -/
theorem nominalStore_polynomial {fuel : Nat} {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    (hshape : ComparisonShapeSolver.prepare fuel p = .success (.solved shapes))
    (hcollect : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hscope : ∀ v ∈ p.assumptions.typeVars, ComparisonShapeSolver.sourceAllowed p v = false)
    (hfresh : ∀ leaf ∈ templates.leaves,
      ∀ v ∈ p.assumptions.typeVariables ++ p.targetType.typeVariables ++
        p.sourceType.typeVariables ++ p.sourceBounds.typeVariables, v ≠ .flex leaf.name)
    {σ : CompareSubstitution} (hσ : σ.WellShaped p.assumptions)
    (hleaf : ∀ leaf ∈ templates.leaves,
      ComparisonShape.Equivalent p.assumptions (σ.type (.flex leaf.name)).shape (.var leaf.shapeClass))
    {g : ComparisonGroups.Group} (hg : g ∈ groups) {head : TypeVar} (hh : head ∈ g.heads)
    (hfixed : ∀ v ∈ g.heads, σ.type v = .var v) :
    (nominalStore g σ).Polynomial g.heads.length := by
  have hφ := ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hshape).1
  have hclass := collected_class_fixed hshape hcollect hfresh hg hh
  have hbound := witnessValues_nominal_constant hφ hcollect hfresh hσ hleaf hg hclass hfixed
    (fun _ => false)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [nominalStore, Fin.getElem_fin, Vector.getElem_ofFn] using
      nominalFormula_positive g.heads (σ.type (.flex g.leaves[i]))
  · intro i
    simp only [nominalStore, Fin.getElem_fin, Vector.getElem_ofFn]
    apply nominalFormula_supported
    apply opaque_head_support hφ (hσ.type _)
      (collected_image_shape hφ hcollect hfresh hleaf hg hclass hfixed
        (.inr ⟨g.leaves[i], List.getElem_mem _, rfl⟩))
    exact ComparisonGroups.collect_class_heads hshape hcollect hscope hfresh hg hh
  · intro i
    exact (nominalStore_correct g σ (fun _ => true) (fun _ => false) i).mpr (hbound true i)
  · intro i hi
    have he := (nominalStore_correct g σ (fun _ => false) (fun _ => false) i).mp hi
    rw [hbound false i] at he
    cases he

end ModalityInference.ComparisonJointGroup
