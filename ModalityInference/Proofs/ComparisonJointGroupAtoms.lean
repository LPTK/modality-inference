import ModalityInference.Proofs.ComparisonJointGroupReflection
import ModalityInference.Proofs.ComparisonJointAssemblyModes
import ModalityInference.Proofs.ComparisonJointGroupWitness

/-! Finite reconstructed leaf images and the common scalar action realize the
original opaque atoms, including their guarded outer annotations. -/

namespace ModalityInference.ComparisonJointGroupAtoms

open ComparisonControls ComparisonTupleReification ComparisonJointGroup
  ComparisonJointAssemblyReification ComparisonPropagation

def head (b : Basis) (v : TypeVar) : ComparisonControls.Generated b :=
  if h : CompareTy.var v ∈ b.heads then .head (.var v) h
  else .head b.head List.mem_cons_self

def base (b : Basis) (g : ComparisonGroups.Group)
    (images : Fin g.leaves.length → ComparisonControls.Generated b) : TypeVar → ComparisonControls.Generated b
  | .flex n => match index g.leaves n with
      | some i => images i
      | none => head b (.flex n)
  | .rigid n => head b (.rigid n)

def atom (b : Basis) (g : ComparisonGroups.Group)
    (images : Fin g.leaves.length → ComparisonControls.Generated b) (modes : ModVar → ModExpr)
    (a : ComparisonGroups.Atom) : ComparisonControls.Generated b :=
  if h : ∀v∈(a.mode.subst modes).freeVariables, v ∈ b.modes then
    .modal (base b g images a.head) (a.mode.subst modes) h
  else .head b.head List.mem_cons_self

theorem head_term {b : Basis} {v : TypeVar} (hv : CompareTy.var v ∈ b.heads) :
    (head b v).term = .var v := by simp [head, hv, ComparisonControls.Generated.term]

theorem head_observe {b : Basis} {v : TypeVar} (hv : CompareTy.var v ∈ b.heads)
    (c : Coordinate) (heads : CompareTy → Bool) (η : ModVar → Mode) :
    observe c heads η (head b v) = heads (.var v) := by simp [head, hv, observe]

theorem base_term {b : Basis} {g : ComparisonGroups.Group}
    {images : Fin g.leaves.length → ComparisonControls.Generated b} {σ : CompareSubstitution}
    (hb : b.heads = g.heads.map CompareTy.var)
    (hf : ∀v∈g.heads, σ.type v = .var v)
    (hi : ∀i, σ.type (.flex g.leaves[i]) = (images i).term)
    {v : TypeVar} (hv : HeadCovered g.heads g.leaves v) :
    (base b g images v).term = σ.type v := by
  have hh {v : TypeVar} (hv : v ∈ g.heads) : CompareTy.var v ∈ b.heads := by
    rw [hb]
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  cases v with
  | rigid n =>
    have hv : TypeVar.rigid n ∈ g.heads := hv.resolve_right (by rintro ⟨_, _, he⟩; cases he)
    exact (head_term (hh hv)).trans (hf _ hv).symm
  | flex n =>
    cases hn : index g.leaves n with
    | some i => simpa only [base, hn, index_names_get hn] using (hi i).symm
    | none =>
      have hv : TypeVar.flex n ∈ g.heads := by
        rcases hv with hv | ⟨k, hk, he⟩
        · exact hv
        · cases TypeVar.flex.inj he
          obtain ⟨i, hi⟩ := index_exists hk
          rw [hn] at hi
          cases hi
      simp only [base, hn]
      exact (head_term (hh hv)).trans (hf _ hv).symm

theorem getElem?_idxOf_mem {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {a : α}
    (ha : a ∈ xs) : xs[xs.idxOf a]? = some a := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    by_cases hb : b = a
    · subst b
      simp
    · have hx : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hb)
      have he : (b == a) = false := beq_eq_false_iff_ne.mpr hb
      simpa [List.idxOf_cons, he] using ih hx

theorem basisValue_head {b : Basis} {g : ComparisonGroups.Group}
    (hb : b.heads = g.heads.map CompareTy.var) {v : TypeVar} (hv : v ∈ g.heads)
    (heads : CompareTy → Bool) : basisValue b.heads heads (g.heads.idxOf v) = heads (.var v) := by
  simp only [basisValue, hb, List.getElem?_map, getElem?_idxOf_mem hv,
    Option.map_some, Option.getD_some]

def parameters (b : Basis) (g : ComparisonGroups.Group)
    (world : (ModVar → Mode) → Nat → Bool) (heads : CompareTy → Bool) (η : ModVar → Mode) : Nat → Bool :=
  ComparisonJointAssembly.parameters g.heads.length (basisValue b.heads heads) (world η)

theorem parameters_head {b : Basis} {g : ComparisonGroups.Group}
    (hb : b.heads = g.heads.map CompareTy.var) {v : TypeVar} (hv : v ∈ g.heads)
    (world : (ModVar → Mode) → Nat → Bool) (heads : CompareTy → Bool) (η : ModVar → Mode) :
    parameters b g world heads η (g.heads.idxOf v) = heads (.var v) := by
  simp only [parameters, ComparisonJointAssembly.parameters,
    List.idxOf_lt_length_of_mem hv, ↓reduceIte]
  exact basisValue_head hb hv heads

@[simp] theorem parameters_modes (b : Basis) (g : ComparisonGroups.Group)
    (world : (ModVar → Mode) → Nat → Bool) (heads : CompareTy → Bool) (η : ModVar → Mode) :
    ComparisonJointGroup.modes g.heads.length (parameters b g world heads η) = world η :=
  ComparisonJointAssembly.modes_parameters ..

theorem base_observe {b : Basis} {g : ComparisonGroups.Group}
    {images : Fin g.leaves.length → ComparisonControls.Generated b}
    (hb : b.heads = g.heads.map CompareTy.var)
    (world : (ModVar → Mode) → Nat → Bool)
    (values : (CompareTy → Bool) → (ModVar → Mode) → Fin (4 * g.leaves.length) → Bool)
    (hi : ∀i c heads η, observe c heads η (images i) = values heads η (state c i))
    {v : TypeVar} (hv : HeadCovered g.heads g.leaves v)
    (c : Coordinate) (heads : CompareTy → Bool) (η : ModVar → Mode) :
    observe c heads η (base b g images v) =
      leafValue g.heads g.leaves c (parameters b g world heads η) (values heads η) v := by
  have hh {v : TypeVar} (hv : v ∈ g.heads) : CompareTy.var v ∈ b.heads := by
    rw [hb]
    exact List.mem_map.mpr ⟨v, hv, rfl⟩
  cases v with
  | rigid n =>
    have hv : TypeVar.rigid n ∈ g.heads := hv.resolve_right (by rintro ⟨_, _, he⟩; cases he)
    simp only [base, leafValue, head_observe (hh hv)]
    exact (parameters_head hb hv world heads η).symm
  | flex n =>
    cases hn : index g.leaves n with
    | some i => simp only [base, leafValue, hn, hi]
    | none =>
      have hv : TypeVar.flex n ∈ g.heads := by
        rcases hv with hv | ⟨k, hk, he⟩
        · exact hv
        · cases TypeVar.flex.inj he
          obtain ⟨i, hi⟩ := index_exists hk
          rw [hn] at hi
          cases hi
      simp only [base, leafValue, hn, head_observe (hh hv)]
      exact (parameters_head hb hv world heads η).symm

theorem restored_apply {m original : ModExpr} {η : ModVar → Mode} {world : Nat → Bool}
    (he : m.eval (some ∘ η) = original.eval (some ∘ projectedModes world))
    (hd : m.WellFormed η) (c : Coordinate) (value : Bool) :
    ComparisonOpaqueObserver.applyMode c value (m.complete η) =
      ComparisonJointGroup.apply c world value original := by
  have ho : original.WellFormed (projectedModes world) := by
    simpa only [ModExpr.WellFormed, he] using hd
  rw [ComparisonJointGroup.apply_value c world value original ho]
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hd
  rw [ModExpr.complete_of_eval hn, ModExpr.complete_of_eval (he.symm.trans hn)]

theorem atom_term {b : Basis} {g : ComparisonGroups.Group}
    {images : Fin g.leaves.length → ComparisonControls.Generated b} {σ : CompareSubstitution}
    (hb : b.heads = g.heads.map CompareTy.var)
    (hf : ∀v∈g.heads, σ.type v = .var v)
    (hi : ∀i, σ.type (.flex g.leaves[i]) = (images i).term)
    {a : ComparisonGroups.Atom} (hv : HeadCovered g.heads g.leaves a.head)
    (hm : ∀v∈(a.mode.subst σ.mode).vars, v ∈ b.modes) :
    (atom b g images σ.mode a).term = a.interpret σ := by
  have hm' : ∀v∈(a.mode.subst σ.mode).freeVariables, v ∈ b.modes :=
    fun v hv => hm v (((a.mode.subst σ.mode).mem_freeVariables v).mp hv)
  rw [atom, dif_pos hm']
  simp only [ComparisonControls.Generated.term,
    ComparisonGroups.Atom.interpret, base_term hb hf hi hv]

theorem atom_observe {Δ : Bounds} {b : Basis} {g : ComparisonGroups.Group}
    {images : Fin g.leaves.length → ComparisonControls.Generated b} {σ : CompareSubstitution}
    (hb : b.heads = g.heads.map CompareTy.var)
    (world : (ModVar → Mode) → Nat → Bool)
    (values : (CompareTy → Bool) → (ModVar → Mode) → Fin (4 * g.leaves.length) → Bool)
    (hi : ∀i c heads η, observe c heads η (images i) = values heads η (state c i))
    {a : ComparisonGroups.Atom} (hv : HeadCovered g.heads g.leaves a.head)
    (hm : ∀v∈(a.mode.subst σ.mode).vars, v ∈ b.modes)
    (hd : Entails Δ (.defined (a.mode.subst σ.mode)))
    (he : ∀η, (a.mode.subst σ.mode).eval (some ∘ η) = a.mode.eval (some ∘ projectedModes (world η)))
    (c : Coordinate) (heads : CompareTy → Bool) (η : ModVar → Mode)
    (hη : c = .unaffected ∨ ModeModels Δ η) :
    observe c heads η (atom b g images σ.mode a) =
      atomValue g.heads g.leaves c (parameters b g world heads η) (values heads η) a := by
  have hm' : ∀v∈(a.mode.subst σ.mode).freeVariables, v ∈ b.modes :=
    fun v hv => hm v (((a.mode.subst σ.mode).mem_freeVariables v).mp hv)
  rw [atom, dif_pos hm']
  simp only [observe, atomValue, parameters_modes]
  rw [base_observe hb world values hi hv]
  rcases hη with rfl | hη
  · rfl
  · exact restored_apply (he η) (hd η hη) c _

theorem head_total (b : Basis) (v : TypeVar) : Total (head b v) := by
  unfold head
  split <;> trivial

theorem base_total {b : Basis} {g : ComparisonGroups.Group}
    {images : Fin g.leaves.length → ComparisonControls.Generated b}
    (hi : ∀i, Total (images i)) (v : TypeVar) : Total (base b g images v) := by
  cases v with
  | rigid => exact head_total ..
  | flex n =>
    cases hn : index g.leaves n with
    | some i => simpa only [base, hn] using hi i
    | none => simpa only [base, hn] using head_total b (.flex n)

theorem atom_defined {Δ : Bounds} {b : Basis} {g : ComparisonGroups.Group}
    {images : Fin g.leaves.length → ComparisonControls.Generated b} {modes : ModVar → ModExpr}
    (hh : ∀t∈b.heads, t.DefinedUnder Δ) (hi : ∀i, Total (images i))
    {a : ComparisonGroups.Atom}
    (hd : Entails Δ (.defined (a.mode.subst modes))) :
    (atom b g images modes a).term.DefinedUnder Δ := by
  unfold atom
  split
  · exact CompareTy.definedUnder_modal_iff.mpr ⟨(base_total hi a.head).definedUnder hh, hd⟩
  · exact hh b.head List.mem_cons_self

theorem leafValue_fixed {heads : List TypeVar} {names : List Nat} {v : TypeVar}
    (hf : ∀ n ∈ names, v ≠ .flex n)
    (c : Coordinate) (parameters : Nat → Bool) (values : Fin (4 * names.length) → Bool) :
    leafValue heads names c parameters values v = parameters (heads.idxOf v) := by
  cases v with
  | rigid => rfl
  | flex n =>
    cases hn : index names n with
    | none => simp only [leafValue, hn]
    | some i => exact (hf n (index_mem hn) rfl).elim

theorem atomValue_fixed {heads : List TypeVar} {names : List Nat} {a : ComparisonGroups.Atom}
    (hf : ∀ n ∈ names, a.head ≠ .flex n)
    (c : Coordinate) (parameters : Nat → Bool) (values : Fin (4 * names.length) → Bool) :
    atomValue heads names c parameters values a = fixedValue heads c parameters a := by
  simp only [atomValue, fixedValue, leafValue_fixed hf]

theorem pair_labels {g : ComparisonGroups.Group} {pair : ComparisonGroups.Inequality}
    (hp : pair ∈ g.assumptions ++ g.goals) :
    pair.1.mode ∈ ComparisonElimination.groupLabels g ∧
      pair.2.mode ∈ ComparisonElimination.groupLabels g := by
  constructor <;> exact List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨pair, hp, by simp⟩)

/-- Reflection uses one finite family of reconstructed leaves and one common
mode action. Outer labels need only be defined under the declared assumptions. -/
theorem group_sound {Δ assumptions required : Bounds} {shape : ComparisonShape}
    {b : Basis} {g : ComparisonGroups.Group} {σ : CompareSubstitution}
    (images : Fin g.leaves.length → ComparisonControls.Generated b)
    (world : (ModVar → Mode) → Nat → Bool)
    (values : (CompareTy → Bool) → (ModVar → Mode) → Fin (4 * g.leaves.length) → Bool)
    (hb : b.heads = g.heads.map CompareTy.var)
    (hc : Covered g)
    (hdisjoint : ∀ v ∈ g.heads, ∀ n ∈ g.leaves, v ≠ .flex n)
    (hh : ∀ t ∈ b.heads, ComparisonAlgebra.Representable Δ shape t)
    (hf : ∀ v ∈ g.heads, σ.type v = .var v)
    (hi : ∀ i, σ.type (.flex g.leaves[i]) = (images i).term)
    (ht : ∀ i, Total (images i))
    (hobs : ∀ i c heads η, observe c heads η (images i) = values heads η (state c i))
    (hscope : ∀ m ∈ ComparisonElimination.groupLabels g,
      ∀ v ∈ (m.subst σ.mode).vars, v ∈ b.modes)
    (hd : ∀ m ∈ ComparisonElimination.groupLabels g,
      Entails Δ (.defined (m.subst σ.mode)))
    (heval : ∀ m ∈ ComparisonElimination.groupLabels g, ∀ η,
      (m.subst σ.mode).eval (some ∘ η) = m.eval (some ∘ projectedModes (world η)))
    (ha : ∀ pair ∈ g.assumptions,
      AlgebraSubtype Δ (pair.1.interpret σ) (pair.2.interpret σ))
    (hgroup : ∀ heads η, GroupHolds assumptions required g
      (parameters b g world heads η) (values heads η))
    (hguards : ∀ η, ModeModels Δ η →
      ModeModels assumptions (projectedModes (world η)) ∧
        ModeModels required (projectedModes (world η))) :
    ∀ pair ∈ g.goals, AlgebraSubtype Δ (pair.1.interpret σ) (pair.2.interpret σ) := by
  have hterm {pair : ComparisonGroups.Inequality} (hp : pair ∈ g.assumptions ++ g.goals) :
      (atom b g images σ.mode pair.1).term = pair.1.interpret σ ∧
        (atom b g images σ.mode pair.2).term = pair.2.interpret σ := by
    have hv : HeadCovered g.heads g.leaves pair.1.head ∧
        HeadCovered g.heads g.leaves pair.2.head := by
      rcases List.mem_append.mp hp with hp | hp
      · exact ⟨.inl (hc.1 pair hp).1, .inl (hc.1 pair hp).2⟩
      · exact hc.2 pair hp
    have hl := pair_labels hp
    exact ⟨atom_term hb hf hi hv.1 (hscope _ hl.1),
      atom_term hb hf hi hv.2 (hscope _ hl.2)⟩
  have hsound := generated_sound (assumptions := assumptions) (required := required)
    (atom b g images σ.mode)
    (parameters b g world) values hh
  have hg : ∀ pair ∈ g.goals, AlgebraSubtype Δ
      (atom b g images σ.mode pair.1).term (atom b g images σ.mode pair.2).term := by
    apply hsound
    · intro pair hp
      have hl := pair_labels hp
      exact ⟨atom_defined (fun t ht => (hh t ht).2.1) ht (hd _ hl.1),
        atom_defined (fun t ht => (hh t ht).2.1) ht (hd _ hl.2)⟩
    · intro pair hp
      have he := hterm (List.mem_append_left _ hp)
      rw [he.1, he.2]
      exact ha pair hp
    · exact hgroup
    · intro heads η c hη
      rcases hη with hη | hη
      · exact .inl hη
      · have hm := hguards η hη
        apply Or.inr
        simp only [guards, BoolExpr.eval, parameters_modes, Bool.and_eq_true]
        exact ⟨(boundsModeFormula_correct assumptions _).mpr hm.1,
          (boundsModeFormula_correct required _).mpr hm.2⟩
    · intro heads η c hη pair hp
      have hl := pair_labels (List.mem_append_left _ hp)
      have hv := hc.1 pair hp
      exact ⟨(atom_observe hb world values hobs (.inl hv.1) (hscope _ hl.1)
          (hd _ hl.1) (heval _ hl.1) c heads η hη).trans
          (atomValue_fixed (hdisjoint _ hv.1) c _ _),
        (atom_observe hb world values hobs (.inl hv.2) (hscope _ hl.2)
          (hd _ hl.2) (heval _ hl.2) c heads η hη).trans
          (atomValue_fixed (hdisjoint _ hv.2) c _ _)⟩
    · intro heads η c hη pair hp
      have hl := pair_labels (List.mem_append_right _ hp)
      have hv := hc.2 pair hp
      exact ⟨atom_observe hb world values hobs hv.1 (hscope _ hl.1)
          (hd _ hl.1) (heval _ hl.1) c heads η hη,
        atom_observe hb world values hobs hv.2 (hscope _ hl.2)
          (hd _ hl.2) (heval _ hl.2) c heads η hη⟩
  intro pair hp
  have he := hterm (List.mem_append_right _ hp)
  simpa only [he.1, he.2] using hg pair hp

theorem collected_assumption_labels_fixed {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    {σ : CompareSubstitution}
    (hc : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hf : ∀ v ∈ p.assumptions.modVars, σ.mode v = .var v)
    {g : ComparisonGroups.Group} (hg : g ∈ groups)
    {pair : ComparisonGroups.Inequality} (hp : pair ∈ g.assumptions) :
    pair.1.mode.subst σ.mode = pair.1.mode ∧ pair.2.mode.subst σ.mode = pair.2.mode := by
  obtain ⟨left, right, hbound, hi⟩ := ComparisonGroups.collect_assumption_origin hc g hg pair hp
  obtain ⟨hl, hr⟩ := ComparisonGroups.inequality_spec hi
  constructor
  · apply (pair.1.mode.subst_congr ?_).trans pair.1.mode.subst_id
    intro v hv
    exact hf v ((p.assumptions.mem_modVars_iff v).mpr ⟨.sub left right, hbound,
      Finset.mem_union_left _ (ComparisonGroups.atom_modeVars_subset hl hv)⟩)
  · apply (pair.2.mode.subst_congr ?_).trans pair.2.mode.subst_id
    intro v hv
    exact hf v ((p.assumptions.mem_modVars_iff v).mpr ⟨.sub left right, hbound,
      Finset.mem_union_right _ (ComparisonGroups.atom_modeVars_subset hr hv)⟩)

theorem collected_labels_defined {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    {σ : CompareSubstitution}
    (hc : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (hf : ∀ v ∈ p.assumptions.modVars, σ.mode v = .var v)
    (hd : p.assumptions.TypeBoundsDefined)
    (hguards : ComparisonReduction.OpaqueGuards reduced)
    (hmodes : AlgebraEntailsAll p.assumptions (σ.bounds reduced.modes)) :
    ∀ g ∈ groups, ∀ m ∈ ComparisonElimination.groupLabels g,
      Entails p.assumptions (.defined (m.subst σ.mode)) := by
  intro g hg m hm
  obtain ⟨pair, hp, hm⟩ := List.mem_flatMap.mp (List.mem_dedup.mp hm)
  rcases List.mem_append.mp hp with hp | hp
  · have hl := ComparisonGroups.collect_assumption_modes hd hc g hg pair hp
    have he := collected_assumption_labels_fixed hc hf hg hp
    rcases List.mem_cons.mp hm with rfl | hm
    · simpa only [he.1] using hl.1
    · obtain rfl := List.mem_singleton.mp hm
      simpa only [he.2] using hl.2
  · have hl := ComparisonGroups.collect_goal_guards hc hguards g hg pair hp
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hmodes _ (List.mem_map.mpr ⟨.defined pair.1.mode, hl.1, rfl⟩)
    · obtain rfl := List.mem_singleton.mp hm
      exact hmodes _ (List.mem_map.mpr ⟨.defined pair.2.mode, hl.2, rfl⟩)

theorem collected_assumptions {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List ComparisonGroups.Group}
    {σ : CompareSubstitution}
    (hc : ComparisonGroups.collect p shapes templates reduced = .success groups)
    (ht : ∀ v ∈ p.assumptions.typeVars, σ.type v = .var v)
    (hf : ∀ v ∈ p.assumptions.modVars, σ.mode v = .var v)
    (hd : ∀ g ∈ groups, ∀ m ∈ ComparisonElimination.groupLabels g,
      Entails p.assumptions (.defined (m.subst σ.mode)))
    (hshape : σ.WellShaped p.assumptions) :
    ∀ g ∈ groups, ∀ pair ∈ g.assumptions,
      AlgebraSubtype p.assumptions (pair.1.interpret σ) (pair.2.interpret σ) := by
  intro g hg pair hp
  obtain ⟨left, right, hbound, hi⟩ := ComparisonGroups.collect_assumption_origin hc g hg pair hp
  have hl := pair_labels (List.mem_append_left _ hp)
  exact (ComparisonGroups.inequality_algebra_iff hshape hi (hd g hg _ hl.1)
    (hd g hg _ hl.2)).mp (CompareSubstitution.declared_subtype ht hf hbound)

theorem projected_assemble_variable_supported {allowed : List ModVar} {modeIds : List Nat}
    {solution : SymbolicModes.Elimination (SchemeModeSynthesis.atoms modeIds)}
    {action : Substitution}
    (ha : SymbolicSchemeModes.assemble (projectElimination allowed solution)
      (SchemeModeSynthesis.parameters modeIds) = some action) {v : ModVar}
    (hv : v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n) :
    ∀ w ∈ (action.mode v).vars, w ∈ allowed := by
  cases v with
  | rigid n =>
    have hv : ModVar.rigid n ∈ allowed :=
      hv.resolve_right (by rintro ⟨_, _, he⟩; cases he)
    simpa only [Substitution.mode, ModExpr.vars, Finset.mem_singleton] using
      (fun w (he : w = ModVar.rigid n) => he ▸ hv)
  | flex n =>
    by_cases hn : n ∈ modeIds
    · exact projected_mode_allowed
        (fun a ha => (SchemeModeSynthesis.mem_atoms_flex ha).mpr hn)
        (SymbolicSchemeModes.assemble_action ha (SchemeModeSynthesis.parameters_lookup hn))
    · rw [SymbolicSchemeModes.assemble_fixed ha (SchemeModeSynthesis.parameters_lookup_none hn)]
      have hv : ModVar.flex n ∈ allowed := hv.resolve_right (by
        rintro ⟨k, hk, he⟩
        exact hn ((ModVar.flex.inj he).symm ▸ hk))
      simpa only [ModExpr.vars, Finset.mem_singleton] using
        (fun w (he : w = ModVar.flex n) => he ▸ hv)

theorem projected_assemble_supported {allowed : List ModVar} {modeIds : List Nat}
    {solution : SymbolicModes.Elimination (SchemeModeSynthesis.atoms modeIds)}
    {action : Substitution}
    (ha : SymbolicSchemeModes.assemble (projectElimination allowed solution)
      (SchemeModeSynthesis.parameters modeIds) = some action) {m : ModExpr}
    (hs : ∀ v ∈ m.vars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n) :
    ∀ w ∈ (m.subst action.mode).vars, w ∈ allowed :=
  m.support_subst action.mode (fun v hv => projected_assemble_variable_supported ha (hs v hv))

end ModalityInference.ComparisonJointGroupAtoms
