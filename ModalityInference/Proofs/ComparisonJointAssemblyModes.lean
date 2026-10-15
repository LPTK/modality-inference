import ModalityInference.Proofs.ComparisonJointAssemblyReification

namespace ModalityInference.ComparisonJointAssemblyReification

open ComparisonPropagation ComparisonJointAssembly ComparisonControls SymbolicModes

/-- Projecting unused inputs preserves the scalar reifier's permitted axes. -/
theorem projected_modes_reify_of_axes {flex : List Nat} {original : Elimination flex}
    (haxes : ∀ v w, w ∈ (original.substitute v).atoms →
      ModalSynthesis.locality w = ModalSynthesis.locality v)
    (allowed : List ModVar) (v : ModVar) :
    ∃ m, (projectElimination allowed original).mode v = some m := by
  let solution := projectElimination allowed original
  have hlocal : ∀ w ∈ (solution.substitute (v.atomIndex 0)).atoms, Axis.Supports .locality w := by
    intro w hw
    have hs := haxes _ _ (projectElimination_atoms hw)
    rw [ModalSynthesis.locality_atom_zero] at hs
    simpa [ModalSynthesis.locality, Axis.Supports] using hs
  have haffinity : ∀ w ∈ (solution.substitute (v.atomIndex 1)).atoms, Axis.Supports .affinity w := by
    intro w hw
    have hs := haxes _ _ (projectElimination_atoms hw)
    rw [ModalSynthesis.locality_atom_one] at hs
    simpa [ModalSynthesis.locality, Axis.Supports] using hs
  have hunique : ∀ w ∈ (solution.substitute (v.atomIndex 2)).atoms, Axis.Supports .uniqueness w := by
    intro w hw
    have hs := haxes _ _ (projectElimination_atoms hw)
    rw [ModalSynthesis.locality_atom_two] at hs
    simpa [ModalSynthesis.locality, Axis.Supports] using hs
  obtain ⟨l, hl⟩ := (reify_supported _ _).mpr hlocal
  obtain ⟨a, ha⟩ := (reify_supported _ _).mpr haffinity
  obtain ⟨u, hu⟩ := (reify_supported _ _).mpr hunique
  refine ⟨.compose l (.compose a u), ?_⟩
  change solution.mode v = _
  simp [Elimination.mode, hl, ha, hu]

theorem projected_modes_reify {fuel minimumModes : Nat} {flex : List Nat}
    {count heads : Nat} {input : ComparisonJointGroup.Input} {result : Result input count flex}
    (hr : ComparisonJointAssembly.run fuel ModalSynthesis.locality flex count heads input minimumModes = .success result)
    (allowed : List ModVar) (v : ModVar) :
    ∃ m, (projectElimination allowed result.solution.modes).mode v = some m :=
  projected_modes_reify_of_axes (fun _ _ hw => (run_modes_atoms hr hw).1) allowed v

theorem projected_modes_assemble_of_axes {flex : List Nat} {solution : Elimination flex}
    (haxes : ∀ v w, w ∈ (solution.substitute v).atoms →
      ModalSynthesis.locality w = ModalSynthesis.locality v)
    (allowed : List ModVar) (parameters : List (Nat × ModVar)) :
    ∃ action, SymbolicSchemeModes.assemble (projectElimination allowed solution) parameters = some action := by
  apply (SymbolicSchemeModes.assemble_iff _ _).mpr
  intro p _
  obtain ⟨m, hm⟩ := projected_modes_reify_of_axes haxes allowed p.2
  exact Option.isSome_iff_exists.mpr ⟨m, hm⟩

theorem projected_modes_assemble {fuel minimumModes : Nat} {flex : List Nat}
    {count heads : Nat} {input : ComparisonJointGroup.Input} {result : Result input count flex}
    (hr : ComparisonJointAssembly.run fuel ModalSynthesis.locality flex count heads input minimumModes = .success result)
    (allowed : List ModVar) (parameters : List (Nat × ModVar)) :
    ∃ action, SymbolicSchemeModes.assemble (projectElimination allowed result.solution.modes) parameters = some action :=
  projected_modes_assemble_of_axes (fun _ _ hw => (run_modes_atoms hr hw).1) allowed parameters

theorem projectWorld_fixed {allowed : List ModVar} {v : Nat} (hv : atomVariable v ∈ allowed)
    (world : Nat → Bool) : projectWorld allowed world v = world v := by
  simp [projectWorld, hv]

theorem projected_expression_fixed {allowed : List ModVar} {e : BoolExpr}
    (hs : ∀ v ∈ e.atoms, atomVariable v ∈ allowed) (world : Nat → Bool) :
    e.eval (projectWorld allowed world) = e.eval world :=
  SymbolicModes.eval_congr e (fun v hv => projectWorld_fixed (hs v hv) world)

theorem projected_coordinate_eval {allowed : List ModVar} {solution : Elimination flex}
    {v : ModVar} (hv : v ∈ allowed ∨ ∀ a < 3, v.atomIndex a ∈ flex)
    (η : ModVar → Mode) {a : Nat} (ha : a < 3) :
    ((projectElimination allowed solution).substitute (v.atomIndex a)).eval (encodeModes η) =
      (solution.substitute (v.atomIndex a)).eval (projectWorld allowed (encodeModes η)) := by
  rcases hv with hv | hv
  · exact projectElimination_allowed (by simpa only [atomVariable_atomIndex v a ha] using hv) _
  · exact projectElimination_flexible (hv a ha) _

theorem projected_mode_eval {allowed : List ModVar} {solution : Elimination flex}
    {v : ModVar} {m : ModExpr}
    (hm : (projectElimination allowed solution).mode v = some m)
    (hv : v ∈ allowed ∨ ∀ a < 3, v.atomIndex a ∈ flex) (η : ModVar → Mode) :
    m.eval (some ∘ η) = some (projectedModes
      (fun i => (solution.substitute i).eval (projectWorld allowed (encodeModes η))) v) := by
  rw [Elimination.mode_eval hm]
  simp only [projectedModes, projected_coordinate_eval hv η (by decide : 0 < 3),
    projected_coordinate_eval hv η (by decide : 1 < 3),
    projected_coordinate_eval hv η (by decide : 2 < 3)]

theorem projected_reify_allowed {allowed : List ModVar} {solution : Elimination flex}
    {v : Nat} (hv : v ∈ flex) {axis : Axis} {m : ModExpr}
    (hm : reify axis ((projectElimination allowed solution).substitute v) = some m)
    {w : ModVar} (hw : w ∈ m.vars) : w ∈ allowed := by
  obtain ⟨i, hi, rfl⟩ := reify_variables hm w hw
  rw [projectElimination_substitute, if_pos hv] at hi
  exact (projectExpression_atoms hi).2

theorem projected_mode_allowed {allowed : List ModVar} {solution : Elimination flex}
    {v : ModVar} (hv : ∀ a < 3, v.atomIndex a ∈ flex) {m : ModExpr}
    (hm : (projectElimination allowed solution).mode v = some m) :
    ∀ w ∈ m.vars, w ∈ allowed := by
  let s := projectElimination allowed solution
  change s.mode v = some m at hm
  cases hl : reify .locality (s.substitute (v.atomIndex 0)) <;>
    cases ha : reify .affinity (s.substitute (v.atomIndex 1)) <;>
    cases hu : reify .uniqueness (s.substitute (v.atomIndex 2)) <;>
    simp [Elimination.mode, hl, ha, hu] at hm
  cases hm
  intro w hw
  simp only [ModExpr.vars, Finset.mem_union] at hw
  exact hw.elim (projected_reify_allowed (hv 0 (by decide)) hl)
    (fun hw => hw.elim (projected_reify_allowed (hv 1 (by decide)) ha)
      (projected_reify_allowed (hv 2 (by decide)) hu))

theorem projected_assemble_eval {allowed : List ModVar} {modeIds : List Nat}
    {solution : Elimination (SchemeModeSynthesis.atoms modeIds)} {action : Substitution}
    (ha : SymbolicSchemeModes.assemble (projectElimination allowed solution)
      (SchemeModeSynthesis.parameters modeIds) = some action)
    (η : ModVar → Mode) (v : ModVar)
    (hv : v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n) :
    (action.mode v).eval (some ∘ η) = some (projectedModes
      (fun i => (solution.substitute i).eval (projectWorld allowed (encodeModes η))) v) := by
  have hv' : v ∈ allowed ∨ ∀ a < 3, v.atomIndex a ∈ SchemeModeSynthesis.atoms modeIds := by
    rcases hv with hv | ⟨n, hn, rfl⟩
    · exact .inl hv
    · exact .inr fun a ha => (SchemeModeSynthesis.mem_atoms_flex ha).mpr hn
  rw [SchemeModeSynthesis.assemble_eval ha]
  simp only [projectedModes, projected_coordinate_eval hv' η (by decide : 0 < 3),
    projected_coordinate_eval hv' η (by decide : 1 < 3),
    projected_coordinate_eval hv' η (by decide : 2 < 3)]

theorem projected_strategy_fixed {allowed : List ModVar} {solution : Elimination flex}
    {v : ModVar} (hv : v ∈ allowed) (hf : ∀ a < 3, v.atomIndex a ∉ flex)
    (η : ModVar → Mode) :
    projectedModes (fun i => (solution.substitute i).eval
      (projectWorld allowed (encodeModes η))) v = η v := by
  have hp (a : Nat) (ha : a < 3) :
      projectWorld allowed (encodeModes η) (v.atomIndex a) = encodeModes η (v.atomIndex a) :=
    projectWorld_fixed (by simpa only [atomVariable_atomIndex v a ha] using hv) _
  simpa only [projectedModes, SchemeModeSynthesis.images_fixed solution (hf 0 (by decide)),
    SchemeModeSynthesis.images_fixed solution (hf 1 (by decide)),
    SchemeModeSynthesis.images_fixed solution (hf 2 (by decide)), BoolExpr.eval,
    hp 0 (by decide), hp 1 (by decide), hp 2 (by decide)] using
    congrFun (projectedModes_encodeModes η) v

/-- Ambient guards retain their original valuation: their names are permitted
inputs and none is a synthesized output. -/
theorem projected_fixed_models {allowed : List ModVar} {solution : Elimination flex}
    {bounds : Bounds}
    (hf : ∀ v ∈ bounds.modVars, v ∈ allowed ∧ ∀ a < 3, v.atomIndex a ∉ flex)
    (η : ModVar → Mode) :
    ModeModels bounds (projectedModes (fun i => (solution.substitute i).eval
      (projectWorld allowed (encodeModes η)))) ↔ ModeModels bounds η :=
  ModeModels.congr bounds (fun v hv => projected_strategy_fixed (hf v hv).1 (hf v hv).2 η)

theorem projected_fixed_expression {allowed : List ModVar} {solution : Elimination flex}
    {m : ModExpr}
    (hf : ∀ v ∈ m.vars, v ∈ allowed ∧ ∀ a < 3, v.atomIndex a ∉ flex)
    (η : ModVar → Mode) :
    m.eval (some ∘ projectedModes (fun i => (solution.substitute i).eval
      (projectWorld allowed (encodeModes η)))) = m.eval (some ∘ η) :=
  ModExpr.eval_congr m (fun v hv => congrArg some
    (projected_strategy_fixed (hf v hv).1 (hf v hv).2 η))

theorem projected_assemble_expression {allowed : List ModVar} {modeIds : List Nat}
    {solution : Elimination (SchemeModeSynthesis.atoms modeIds)} {action : Substitution}
    (ha : SymbolicSchemeModes.assemble (projectElimination allowed solution)
      (SchemeModeSynthesis.parameters modeIds) = some action) {m : ModExpr}
    (hs : ∀ v ∈ m.vars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n)
    (η : ModVar → Mode) :
    (m.subst action.mode).eval (some ∘ η) =
      m.eval (some ∘ projectedModes (fun i => (solution.substitute i).eval
        (projectWorld allowed (encodeModes η)))) := by
  rw [ModExpr.eval_subst]
  exact ModExpr.eval_congr m (fun v hv => projected_assemble_eval ha η v (hs v hv))

theorem constraint_mode_transport (c : Constraint) (action : Substitution)
    {η ξ : ModVar → Mode}
    (hv : ∀ v ∈ c.modVars, (action.mode v).eval (some ∘ η) = some (ξ v)) :
    ModeSatisfies η (action.constraint c) ↔ ModeSatisfies ξ c := by
  cases c with
  | sub a b => rfl
  | equiv a b => rfl
  | equal v t =>
    cases v with
    | rigid n => rfl
    | flex n => cases hl : action.types.lookup n <;> simp [Substitution.constraint, hl, ModeSatisfies]
  | mode a b =>
    have ha := ModExpr.eval_congr a (fun v hv' => hv v (Finset.mem_union_left _ hv'))
    have hb := ModExpr.eval_congr b (fun v hv' => hv v (Finset.mem_union_right _ hv'))
    simp only [Substitution.constraint, Constraint.subst, ModeSatisfies, ModExpr.Below,
      ModExpr.eval_subst, ha, hb]
    rfl
  | defined a =>
    have ha := ModExpr.eval_congr a hv
    simp only [Substitution.constraint, Constraint.subst, ModeSatisfies, ModExpr.WellFormed,
      ModExpr.eval_subst, ha]
    rfl

theorem projected_assemble_models {allowed : List ModVar} {modeIds : List Nat}
    {solution : Elimination (SchemeModeSynthesis.atoms modeIds)} {action : Substitution}
    (ha : SymbolicSchemeModes.assemble (projectElimination allowed solution)
      (SchemeModeSynthesis.parameters modeIds) = some action) {bounds : Bounds}
    (hs : ∀ v ∈ bounds.modVars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n)
    (η : ModVar → Mode) :
    ModeModels (action.bounds bounds) η ↔
      ModeModels bounds (projectedModes (fun i => (solution.substitute i).eval
        (projectWorld allowed (encodeModes η)))) := by
  simp only [ModeModels, Substitution.bounds, List.forall_mem_map]
  apply forall_congr' fun c => forall_congr' fun hc => ?_
  exact constraint_mode_transport c action fun v hv =>
    projected_assemble_eval ha η v (hs v ((bounds.mem_modVars_iff v).mpr ⟨c, hc, hv⟩))

/-- A shared scalar strategy discharges the original guards after finite
modality assembly; only input names actually used by the guards are needed. -/
theorem projected_scalar_guards {allowed : List ModVar} {modeIds : List Nat}
    {solution : Elimination (SchemeModeSynthesis.atoms modeIds)} {action : Substitution}
    {assumptions required : Bounds}
    (ha : SymbolicSchemeModes.assemble (projectElimination allowed solution)
      (SchemeModeSynthesis.parameters modeIds) = some action)
    (hfixed : ∀ v ∈ assumptions.modVars,
      v ∈ allowed ∧ ∀ a < 3, v.atomIndex a ∉ SchemeModeSynthesis.atoms modeIds)
    (hrequired : ∀ v ∈ required.modVars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n)
    (hguard : ∀ world,
      (boundsModeFormula assumptions).eval (fun i => (solution.substitute i).eval world) = true →
      (boundsModeFormula required).eval (fun i => (solution.substitute i).eval world) = true) :
    ∀ η, ModeModels assumptions η → ModeModels (action.bounds required) η := by
  intro η hη
  apply (projected_assemble_models ha hrequired η).mpr
  apply (boundsModeFormula_correct required _).mp
  apply hguard (projectWorld allowed (encodeModes η))
  exact (boundsModeFormula_correct assumptions _).mpr ((projected_fixed_models hfixed η).mpr hη)

theorem run_projected_scalar_guards {prepareFuel fuel minimumModes : Nat} {allowed : List ModVar}
    {modeIds : List Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {input : ComparisonJointGroup.Input}
    {result : Result input g.leaves.length (SchemeModeSynthesis.atoms modeIds)} {action : Substitution}
    (hp : ComparisonJointGroup.prepare prepareFuel assumptions required g = .success input)
    (hr : ComparisonJointAssembly.run fuel ModalSynthesis.locality
      (SchemeModeSynthesis.atoms modeIds) g.leaves.length g.heads.length input minimumModes = .success result)
    (ha : SymbolicSchemeModes.assemble (projectElimination allowed result.solution.modes)
      (SchemeModeSynthesis.parameters modeIds) = some action)
    (hfixed : ∀ v ∈ assumptions.modVars,
      v ∈ allowed ∧ ∀ a < 3, v.atomIndex a ∉ SchemeModeSynthesis.atoms modeIds)
    (hrequired : ∀ v ∈ required.modVars, v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n) :
    ∀ η, ModeModels assumptions η → ModeModels (action.bounds required) η := by
  apply projected_scalar_guards ha hfixed hrequired
  intro world
  simpa only [modes_parameters, Result.strategy] using
    (run_group_sound hp hr (fun _ => false) world).2.2

/-- The executable scalar assembler returns a finite action on the exact source
domain. All its images use permitted names, and all original relevant outputs
agree with the same projected strategy used by the reconstructed type leaves. -/
theorem projected_modes_finite_of_axes {modeIds : List Nat}
    {solution : Elimination (SchemeModeSynthesis.atoms modeIds)}
    (haxes : ∀ v w, w ∈ (solution.substitute v).atoms →
      ModalSynthesis.locality w = ModalSynthesis.locality v)
    (allowed : List ModVar) :
    ∃ action, SymbolicSchemeModes.assemble (projectElimination allowed solution)
        (SchemeModeSynthesis.parameters modeIds) = some action ∧
      action.types = [] ∧ action.modes.map Prod.fst = modeIds ∧
      (∀ η v, (action.mode v).WellFormed η) ∧
      (∀ n ∈ modeIds, ∀ w ∈ (action.mode (.flex n)).vars, w ∈ allowed) ∧
      ∀ η v, (v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n) →
        (action.mode v).eval (some ∘ η) = some
          (projectedModes (fun i => (solution.substitute i).eval
            (projectWorld allowed (encodeModes η))) v) := by
  obtain ⟨action, ha⟩ := projected_modes_assemble_of_axes haxes allowed (SchemeModeSynthesis.parameters modeIds)
  have hd := SymbolicSchemeModes.assemble_domain ha
  refine ⟨action, ha, hd.1, ?_, SymbolicSchemeModes.assemble_wellFormed ha, ?_, ?_⟩
  · simpa [SchemeModeSynthesis.parameters, List.map_map, Function.comp_def] using hd.2
  · intro n hn
    exact projected_mode_allowed (fun a ha => (SchemeModeSynthesis.mem_atoms_flex ha).mpr hn)
      (SymbolicSchemeModes.assemble_action ha (SchemeModeSynthesis.parameters_lookup hn))
  · intro η v hv
    exact projected_assemble_eval ha η v hv

theorem projected_modes_finite {fuel minimumModes : Nat} {modeIds : List Nat}
    {count heads : Nat} {input : ComparisonJointGroup.Input}
    {result : Result input count (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointAssembly.run fuel ModalSynthesis.locality
      (SchemeModeSynthesis.atoms modeIds) count heads input minimumModes = .success result)
    (allowed : List ModVar) :
    ∃ action, SymbolicSchemeModes.assemble (projectElimination allowed result.solution.modes)
        (SchemeModeSynthesis.parameters modeIds) = some action ∧
      action.types = [] ∧ action.modes.map Prod.fst = modeIds ∧
      (∀ η v, (action.mode v).WellFormed η) ∧
      (∀ n ∈ modeIds, ∀ w ∈ (action.mode (.flex n)).vars, w ∈ allowed) ∧
      ∀ η v, (v ∈ allowed ∨ ∃ n ∈ modeIds, v = .flex n) →
        (action.mode v).eval (some ∘ η) = some
          (projectedModes (result.strategy (projectWorld allowed (encodeModes η))) v) :=
  projected_modes_finite_of_axes (fun _ _ hw => (run_modes_atoms hr hw).1) allowed

end ModalityInference.ComparisonJointAssemblyReification
