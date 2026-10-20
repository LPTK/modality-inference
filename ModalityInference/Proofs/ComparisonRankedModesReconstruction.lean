import ModalityInference.Proofs.ComparisonRankedModes
import ModalityInference.Proofs.ComparisonRankedModeRepresentation
import ModalityInference.Proofs.ComparisonJointAssemblyModes

namespace ModalityInference.ComparisonRankedModes

open ComparisonObserverMachineFormula ComparisonSignedEndpoints
  ComparisonStructuralLayout ComparisonSignedObservation
  ComparisonJointAssemblyReification

theorem assemble_exists (names : List ModVar) (modeIds : List Nat)
    (input : ComparisonSignedSynthesis.Input)
    (sources : List ComparisonSignedEndpointQueries.Source) (selectors : Nat → Bool) :
    ∃ assembled, assemble names modeIds input sources selectors = some assembled := by
  apply projected_modes_assemble_of_axes
  intro v w hw
  exact (ComparisonJointModes.witness_atoms
    (ComparisonWorldModes.component_supported _ true _)
    (ComparisonWorldModes.component_supported _ false _) hw).1

theorem assemble_domain {names modeIds input sources selectors assembled}
    (h : assemble names modeIds input sources selectors = some assembled) :
    assembled.types = [] ∧ assembled.modes.map Prod.fst = modeIds := by
  have hh := SymbolicSchemeModes.assemble_domain h
  exact ⟨hh.1, by simpa [SchemeModeSynthesis.parameters, List.map_map, Function.comp_def] using hh.2⟩

theorem assemble_fixed {names modeIds input sources selectors assembled}
    (h : assemble names modeIds input sources selectors = some assembled)
    {v : ModVar} (hv : ∀ n ∈ modeIds, v ≠ .flex n) : assembled.mode v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    exact SymbolicSchemeModes.assemble_fixed h
      (SchemeModeSynthesis.parameters_lookup_none (fun hn => hv n hn rfl))

theorem assemble_total {names modeIds input sources selectors assembled}
    (h : assemble names modeIds input sources selectors = some assembled)
    (η : ModVar → Mode) (v : ModVar) : (assembled.mode v).WellFormed η :=
  SymbolicSchemeModes.assemble_wellFormed h η v

theorem assemble_images {names modeIds input sources selectors assembled}
    (h : assemble names modeIds input sources selectors = some assembled)
    {v : ModVar} (hv : v ∈ extended names modeIds) :
    ∀ w ∈ (assembled.mode v).vars, w ∈ names := by
  by_cases hvar : ∃ n ∈ modeIds, v = .flex n
  · obtain ⟨n, hn, rfl⟩ := hvar
    exact projected_mode_allowed
      (fun axis haxis => (SchemeModeSynthesis.mem_atoms_flex haxis).mpr hn)
      (SymbolicSchemeModes.assemble_action h (SchemeModeSynthesis.parameters_lookup hn))
  · have hf : ∀ n ∈ modeIds, v ≠ .flex n := by simpa using hvar
    rw [assemble_fixed h hf]
    have hn : v ∈ names := by
      rcases List.mem_append.mp hv with hn | hn
      · exact hn
      · obtain ⟨n, hn, he⟩ := List.mem_map.mp hn
        exact (hf n hn he.symm).elim
    simpa only [ModExpr.vars, Finset.mem_singleton, forall_eq] using hn

theorem assemble_local_strategy {names modeIds input sources selectors assembled}
    (h : assemble names modeIds input sources selectors = some assembled)
    (ρ : Nat → Bool) (hp : projectWorld names ρ = ρ)
    {v : ModVar} (hv : v ∈ extended names modeIds) :
    projectedModes (fun u =>
      ((ComparisonSignedEndpointQueries.modes ModalSynthesis.locality
        (SchemeModeSynthesis.atoms modeIds) input sources selectors).substitute u).eval ρ) v =
      projectedModes (SchemeModeSynthesis.strategy assembled.mode ρ) v := by
  have hv' : v ∈ names ∨ ∃ n ∈ modeIds, v = .flex n := by
    rcases List.mem_append.mp hv with hn | hn
    · exact .inl hn
    · obtain ⟨n, hn, he⟩ := List.mem_map.mp hn
      exact .inr ⟨n, hn, he.symm⟩
  have he := projected_assemble_eval h (projectedModes ρ) v hv'
  rw [SchemeModeSynthesis.encodeModes_projectedModes, hp] at he
  exact Option.some.inj (he.symm.trans
    (SchemeModeSynthesis.strategy_eval assembled.mode ρ v (assemble_total h _ _)))

theorem run_spec {fuel Δ keys types names modeIds count basis endpoints scalar result}
    (h : run fuel Δ keys types names modeIds count basis endpoints scalar = .success result) :
    ∃ q, prepare fuel Δ keys types names modeIds count basis endpoints = .success q ∧
      ComparisonSignedEndpointQueries.run fuel (input keys basis) ModalSynthesis.locality
        (SchemeModeSynthesis.atoms modeIds) (q :: scalar) = .success result := by
  cases hp : prepare fuel Δ keys types names modeIds count basis endpoints <;>
    simp [run, hp, bind, RunResult.bind] at h
  exact ⟨_, rfl, h⟩

theorem synthesize_eventual {Δ keys types names modeIds count basis endpoints scalar}
    (h : ∃ threshold result, ∀ fuel ≥ threshold,
      run fuel Δ keys types names modeIds count basis endpoints scalar = .success result) :
    ∃ threshold result, ∀ fuel ≥ threshold,
      synthesize fuel Δ keys types names modeIds count basis endpoints scalar = .success result := by
  obtain ⟨n, result, hr⟩ := h
  obtain ⟨k, q, hq⟩ := prepare_complete Δ keys types names modeIds count basis endpoints
  obtain ⟨assembled, ha⟩ := assemble_exists names modeIds (input keys basis) (q :: scalar)
    (CNFPropagation.valuation result.selectors)
  refine ⟨max n k, { types := result.images, modes := assembled.modes }, ?_⟩
  intro fuel hf
  have hp := hq fuel ((le_max_right _ _).trans hf)
  have hh := hr fuel ((le_max_left _ _).trans hf)
  simp only [run, hp, bind, RunResult.bind] at hh
  simp only [synthesize, hp, hh, bind, RunResult.bind, ha]

theorem synthesize_spec {fuel Δ keys types names modeIds count basis endpoints scalar result}
    (h : synthesize fuel Δ keys types names modeIds count basis endpoints scalar = .success result) :
    ∃ q solution assembled,
      prepare fuel Δ keys types names modeIds count basis endpoints = .success q ∧
      ComparisonSignedEndpointQueries.run fuel (input keys basis) ModalSynthesis.locality
        (SchemeModeSynthesis.atoms modeIds) (q :: scalar) = .success solution ∧
      assemble names modeIds (input keys basis) (q :: scalar)
        (CNFPropagation.valuation solution.selectors) = some assembled ∧
      result = { types := solution.images, modes := assembled.modes } := by
  cases hp : prepare fuel Δ keys types names modeIds count basis endpoints <;>
    simp [synthesize, hp, bind, RunResult.bind] at h
  rename_i q
  cases hs : ComparisonSignedEndpointQueries.run fuel (input keys basis) ModalSynthesis.locality
      (SchemeModeSynthesis.atoms modeIds) (q :: scalar) <;> simp [hs] at h
  rename_i solution
  cases ha : assemble names modeIds (input keys basis) (q :: scalar)
      (CNFPropagation.valuation solution.selectors) <;> simp [ha] at h
  exact ⟨q, solution, _, rfl, hs, ha, h.symm⟩

theorem prepare_machine_of_assembled
    {fuel Δ keys types names modeIds count basis endpoints q}
    (hp : prepare fuel Δ keys types names modeIds count basis endpoints = .success q)
    {sources : List ComparisonSignedEndpointQueries.Source} {selectors : Nat → Bool}
    {assembled : Substitution}
    (ha : assemble names modeIds (input keys basis) sources selectors = some assembled)
    (hdisjoint : ∀ v ∈ names, ∀ n ∈ modeIds, v ≠ .flex n)
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (he : ∀ pair ∈ endpoints,
      (∀ v ∈ pair.1.modVars, v ∈ extended names modeIds) ∧
      (∀ v ∈ pair.2.modVars, v ∈ extended names modeIds))
    {family : Nat → (Nat → Bool) → Bool} {images : Nat → CompareTy}
    (hf : ComparisonSignedSynthesis.Family (input keys basis) family)
    (hr : ComparisonRankedDecision.Realizes (input keys basis) family images)
    (hv : q.Valid (fun _ => basis.types.length) family (fun world v =>
      ((ComparisonSignedEndpointQueries.modes ModalSynthesis.locality
        (SchemeModeSynthesis.atoms modeIds) (input keys basis) sources selectors).substitute v).eval world)) :
    ComparisonRankedDecision.MachineValid Δ keys types names count assembled.mode endpoints images := by
  let elimination := ComparisonSignedEndpointQueries.modes ModalSynthesis.locality
    (SchemeModeSynthesis.atoms modeIds) (input keys basis) sources selectors
  let strategy := fun world v => (elimination.substitute v).eval world
  intro original hq pair hpair i
  let data := decode
    (ComparisonObserverMachineEncoding.allocate types.length names.length count) original
  obtain ⟨world, hnodes, hquery, haliases, houtside⟩ := machine_world Δ types names basis data
  have hproject (j : Fin count) : projectWorld names (localWorld world j) = localWorld world j := by
    funext u
    by_cases hu : SymbolicModes.atomVariable u ∈ names
    · simp [projectWorld, hu]
    · simp [projectWorld, hu, houtside j u hu]
  have hsame (j : Fin count) (v : ModVar) (hv : v ∈ extended names modeIds) :
      projectedModes (strategy (localWorld world j)) v =
        projectedModes (SchemeModeSynthesis.strategy assembled.mode (localWorld world j)) v :=
    assemble_local_strategy ha _ (hproject j) hv
  have hfixed (j : Fin count) (v : ModVar) (hv : v ∈ names) :
      projectedModes (strategy (localWorld world j)) v =
        projectedModes (localWorld world j) v := by
    have hn (axis : Nat) (haxis : axis < 3) :
        v.atomIndex axis ∉ SchemeModeSynthesis.atoms modeIds := by
      intro hm
      obtain ⟨n, hn, heq⟩ := (SchemeModeSynthesis.mem_atoms_iff haxis).mp hm
      exact hdisjoint v hv n hn heq
    simpa only [SchemeModeSynthesis.encodeModes_projectedModes] using
      SchemeModeSynthesis.projected_images_fixed elimination
        (projectedModes (localWorld world j)) hn
  have hcore := fields_decode_congr strategy id world hfixed (types := types)
  have hqcore : (query Δ types names (fields types names count)).eval (raw id world) = true := by
    rw [hquery]
    exact (query_eval Δ types names _ original).symm.trans hq
  have hs (j : Fin count) :
      (scalarOK Δ names (fields types names count j)).eval (raw id world) = true := by
    rw [scalarOK_eval]
    exact (ComparisonObserverMachineCheck.check_correct.mp
      ((query_eval Δ types names _ _).symm.trans hqcore) j).scalar
  have haliases' : (aliases types names count basis).eval (raw strategy world) = true := by
    apply (aliases_correct types names count basis _).mpr
    intro j index hindex
    have hh := (aliases_correct types names count basis _).mp haliases j index hindex
    rw [value_eval, hcore, ← value_eval]
    simpa only [raw, ComparisonSignedPoints.raw, ComparisonLayoutWorlds.rawValue_basis,
      id_eq] using hh
  have htheory : (theory Δ types names count basis).eval (raw strategy world) = true := by
    apply Bool.and_eq_true_iff.mpr
    exact ⟨by simpa only [query_eval, hcore] using hqcore, haliases'⟩
  have hreads (name : Nat) (hn : name ∈ keys) (j : Fin count) :
      ComparisonSignedPoints.basisImages (fun _ => basis.types.length) family (raw strategy world)
        (ComparisonRankedDecision.call name j) =
      (value types names (fields types names count) (images name) j).eval (raw id world) := by
    rw [aliases_reads hf hr haliases' hn, value_eval, hcore, ← value_eval]
  have hclauses := (prepare_valid hp family strategy).mp hv world htheory
  simp only [clauses, ComparisonRankedDecision.clauses, List.forall_mem_flatMap,
    List.mem_finRange, forall_const] at hclauses
  have horder := (compile_reads assembled.mode hscope (fun _ => assemble_images ha)
    (fun η _ v => assemble_total ha η v) world strategy hsame hs images _ hreads
    pair.1 pair.2 (he pair hpair).1 (he pair hpair).2 i).mp (hclauses pair hpair i)
  simpa only [value_eval, hnodes, data] using horder

/-- Actual returned finite images and the actual reified shared mode action
satisfy every bounded machine endpoint. No endpoint guard is assumed here. -/
theorem synthesize_sound {fuel Δ keys types names modeIds count basis endpoints scalar result}
    (h : synthesize fuel Δ keys types names modeIds count basis endpoints scalar = .success result)
    (hallowed : ∀ source ∈ scalar, source.Allowed keys)
    (hdisjoint : ∀ v ∈ names, ∀ n ∈ modeIds, v ≠ .flex n)
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (he : ∀ pair ∈ endpoints,
      (∀ v ∈ pair.1.modVars, v ∈ extended names modeIds) ∧
      (∀ v ∈ pair.2.modVars, v ∈ extended names modeIds)) :
    result.types.map Prod.fst = keys ∧
      (∀ entry ∈ result.types, ComparisonControls.LatticeForm basis.types entry.2) ∧
      ComparisonRankedDecision.MachineValid Δ keys types names count result.mode endpoints
        (ComparisonRankedDecision.selected result.types) := by
  obtain ⟨q, solution, assembled, hp, hs, ha, rfl⟩ := synthesize_spec h
  obtain ⟨_, r, _, _, hreconstruct, hkeys, hf, hv⟩ :=
    ComparisonSignedEndpointQueries.run_sound
      (by simpa [input] using And.intro (prepare_allowed hp) hallowed) hs
  have hr : ComparisonRankedDecision.Realizes (input keys basis)
      ((input keys basis).imageValue r (CNFPropagation.valuation solution.selectors))
      (ComparisonRankedDecision.selected solution.images) := by
    intro name hn v hj hm
    exact ((input keys basis).reconstruct_value hreconstruct
      (ComparisonRankedDecision.selected_mem (hkeys.symm ▸ hn)) v hj hm).symm
  refine ⟨hkeys, ?_, ?_⟩
  · intro entry he
    exact ComparisonSignedPolynomials.reconstruct_property
      (((input keys basis).reconstruct_spec hreconstruct).2 entry he)
      (ComparisonControls.LatticeForm basis.types)
      (fun _ => ComparisonControls.LatticeForm.atom)
      (fun _ _ => ComparisonControls.LatticeForm.join)
      (fun _ _ => ComparisonControls.LatticeForm.meet)
  · exact prepare_machine_of_assembled hp ha hdisjoint hscope he hf hr (hv q (by simp))

theorem synthesize_modes {fuel Δ keys types names modeIds count basis endpoints scalar result}
    (h : synthesize fuel Δ keys types names modeIds count basis endpoints scalar = .success result) :
    result.modes.map Prod.fst = modeIds ∧
      (∀ η v, (result.mode v).WellFormed η) ∧
      (∀ v, (∀ n ∈ modeIds, v ≠ .flex n) → result.mode v = .var v) ∧
      (∀ v ∈ extended names modeIds, ∀ w ∈ (result.mode v).vars, w ∈ names) := by
  obtain ⟨q, solution, assembled, _, _, ha, rfl⟩ := synthesize_spec h
  exact ⟨(assemble_domain ha).2, assemble_total ha,
    fun _ => assemble_fixed ha, fun _ => assemble_images ha⟩

end ModalityInference.ComparisonRankedModes
