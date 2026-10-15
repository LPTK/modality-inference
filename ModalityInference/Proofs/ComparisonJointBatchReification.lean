import ModalityInference.ComparisonJointBatchReification
import ModalityInference.Proofs.ComparisonJointBatch
import ModalityInference.Proofs.ComparisonJointAssemblyModes
import ModalityInference.Proofs.ComparisonDefinedSubstitution

namespace ModalityInference.ComparisonJointBatchReification

open ComparisonPropagation ComparisonControls ComparisonTupleReification
  ComparisonJointAssemblyReification

@[simp] theorem entries_length (groups : List Compiled) : (entries groups).length = groups.length :=
  List.length_map ..

@[simp] theorem entries_get (groups : List Compiled) (i : Fin groups.length) :
    (entries groups)[entryIndex groups i] = groups[i].entry := by
  simp [entries, entryIndex]

theorem basis_spec {allowed : List ModVar} {group : ComparisonGroups.Group} {b : Basis}
    (h : basis allowed group = some b) : b.heads = group.heads.map CompareTy.var ∧ b.modes = allowed := by
  cases hh : group.heads with
  | nil => simp [basis, hh] at h
  | cons first rest =>
    simp only [basis, hh, Option.some.injEq] at h
    cases h
    exact ⟨rfl, rfl⟩

theorem basis_complete (allowed : List ModVar) {group : ComparisonGroups.Group}
    (hne : group.heads ≠ []) : ∃ b, basis allowed group = some b := by
  cases hh : group.heads with
  | nil => exact False.elim (hne hh)
  | cons first rest => exact ⟨⟨.var first, rest.map CompareTy.var, allowed⟩, by simp [basis, hh]⟩

theorem recastSolution_correct {minimumModes : Nat} {side : Nat → Bool}
    (compiled : Compiled) (entry : ComparisonJointBatch.Entry) (he : entry = compiled.entry)
    (solution : ComparisonJointGuarded.Result entry.count (ComparisonJointBatch.constants entry) flex)
    (h : ComparisonJointAssembly.SolutionCorrect side entry.count entry.heads entry.input
      minimumModes solution) :
    ComparisonJointAssembly.SolutionCorrect side compiled.group.leaves.length compiled.group.heads.length
      compiled.input minimumModes (recastSolution compiled entry he solution) := by
  subst entry
  exact h

@[simp] theorem recastSolution_modes (compiled : Compiled) (entry : ComparisonJointBatch.Entry)
    (he : entry = compiled.entry)
    (solution : ComparisonJointGuarded.Result entry.count (ComparisonJointBatch.constants entry) flex) :
    (recastSolution compiled entry he solution).modes = solution.modes := by
  subst entry
  rfl

theorem local_correct {fuel minimumModes : Nat} {flex : List Nat}
    {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) flex}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality flex
      (entries groups) minimumModes scalar = .success batch)
    (i : Fin groups.length) (hne : groups[i].group.heads ≠ []) :
    ComparisonJointAssembly.SolutionCorrect ModalSynthesis.locality groups[i].group.leaves.length
      groups[i].group.heads.length groups[i].input minimumModes
      (localResult groups batch i minimumModes).solution := by
  have hn : 0 < (entries groups)[entryIndex groups i].heads := by
    simpa only [entries_get, Compiled.entry, List.length_pos_iff] using hne
  exact recastSolution_correct groups[i] _ (entries_get groups i) _
    (ComparisonJointBatch.run_local_correct hr (entryIndex groups i) hn)

@[simp] theorem local_modes (groups : List Compiled)
    (batch : ComparisonJointBatch.Result (entries groups) flex)
    (i : Fin groups.length) (minimumModes : Nat) :
    (localResult groups batch i minimumModes).solution.modes = batch.solution.modes := by
  exact recastSolution_modes _ _ (entries_get groups i) _

theorem local_reconstruct (groups : List Compiled)
    (batch : ComparisonJointBatch.Result (entries groups) flex)
    (i : Fin groups.length) (minimumModes : Nat) :
    localResult groups batch i minimumModes =
      ComparisonJointAssembly.reconstruct ModalSynthesis.locality groups[i].group.leaves.length
        groups[i].group.heads.length groups[i].input
        (localResult groups batch i minimumModes).solution minimumModes := by
  rfl

theorem basis_nonempty {allowed : List ModVar} {group : ComparisonGroups.Group} {b : Basis}
    (h : basis allowed group = some b) : group.heads ≠ [] := by
  intro he
  simp [basis, he] at h

theorem local_group_sound {prepareFuel fuel minimumModes : Nat} {flex : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) flex}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality flex (entries groups)
      minimumModes scalar = .success batch)
    (i : Fin groups.length)
    (hp : ComparisonJointGroup.prepare prepareFuel assumptions required groups[i].group =
      .success groups[i].input) (hne : groups[i].group.heads ≠ []) :
    ∀ headWorld inputWorld,
      ComparisonJointGroup.GroupHolds assumptions required groups[i].group
        (ComparisonJointAssembly.parameters groups[i].group.heads.length headWorld
          ((localResult groups batch i minimumModes).strategy inputWorld))
        ((localResult groups batch i minimumModes).state groups[i].group.heads.length headWorld inputWorld) :=
  ComparisonJointAssembly.reconstruct_group_sound hp (local_correct hr i hne)

theorem leaf_complete {prepareFuel fuel minimumModes : Nat} {flex : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) flex}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality flex (entries groups)
      minimumModes scalar = .success batch)
    (i : Fin groups.length)
    (hp : ComparisonJointGroup.prepare prepareFuel assumptions required groups[i].group =
      .success groups[i].input) {allowed : List ModVar} {b : Basis}
    (hb : basis allowed groups[i].group = some b) (j : Fin groups[i].group.leaves.length) :
    ∃ generated : ComparisonControls.Generated b,
      leaf b (localResult groups batch i minimumModes) j = some generated.term ∧ Total generated ∧
      ∀ heads η coordinate, observe coordinate heads η generated =
        (localResult groups batch i minimumModes).state groups[i].group.heads.length
          (basisValue b.heads heads) (projectWorld allowed (encodeModes η))
          (ComparisonJointGroup.state coordinate j) := by
  have hn := basis_nonempty hb
  have hh : b.heads.length = groups[i].group.heads.length := by
    rw [(basis_spec hb).1, List.length_map]
  have hs := local_correct hr i hn
  have hl := ComparisonJointGroup.prepare_linear hp
  have hc := ComparisonJointAssembly.reconstruct_coordinates hl.2.1 hl.2.2 hs
  obtain ⟨generated, hg, ht, he⟩ := leaf_complete_of_properties
    (b := b) (result := localResult groups batch i minimumModes)
    (by simpa only [hh] using hs.1)
    (fun v w hw => (ComparisonJointBatch.run_mode_atoms hr (by simpa only [local_modes] using hw)).1)
    hc.1.1 (by simpa only [hh] using hc.1.2.2.1)
    hc.2.1 (by simpa only [hh] using hc.2.2.2.1) j
  refine ⟨generated, hg, ht, ?_⟩
  intro heads η coordinate
  have hcompatible := (local_group_sound hr i hp hn (basisValue b.heads heads)
    (projectWorld b.modes (encodeModes η))).2.1
  simpa only [hh, (basis_spec hb).2] using
    he heads η (by simpa only [hh] using hcompatible) coordinate

private theorem mapM_some {α β : Type} {f : α → Option β} {xs : List α}
    (h : ∀x∈xs, ∃y, f x = some y) : ∃ys, xs.mapM f = some ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    exact ⟨y :: ys, by simp [hy, hys]⟩

theorem groupImages_some {prepareFuel fuel minimumModes : Nat} {flex : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) flex}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality flex (entries groups)
      minimumModes scalar = .success batch) (allowed : List ModVar) (i : Fin groups.length)
    (hp : ComparisonJointGroup.prepare prepareFuel assumptions required groups[i].group =
      .success groups[i].input) (hne : groups[i].group.heads ≠ []) :
    ∃images, groupImages allowed groups[i] (localResult groups batch i minimumModes) = some images := by
  obtain ⟨b, hb⟩ := basis_complete allowed hne
  obtain ⟨images, hi⟩ := mapM_some (xs := List.finRange groups[i].group.leaves.length)
    (f := fun j => do return (groups[i].group.leaves[j], ← leaf b (localResult groups batch i minimumModes) j))
    (fun j _ => by
      obtain ⟨generated, hg, _⟩ := leaf_complete hr i hp hb j
      exact ⟨(groups[i].group.leaves[j], generated.term), by simp only [hg]; rfl⟩)
  exact ⟨images, by simpa only [groupImages, hb, Option.bind_some] using hi⟩

theorem typeImages_some {prepareFuel fuel minimumModes : Nat} {flex : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) flex}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality flex (entries groups)
      minimumModes scalar = .success batch) (allowed : List ModVar)
    (hp : ∀i : Fin groups.length, ComparisonJointGroup.prepare prepareFuel assumptions required
      groups[i].group = .success groups[i].input)
    (hne : ∀i : Fin groups.length, groups[i].group.heads ≠ []) :
    ∃images, typeImages allowed groups batch minimumModes = some images := by
  obtain ⟨images, hi⟩ := mapM_some (xs := List.finRange groups.length)
    (f := fun i => groupImages allowed groups[i] (localResult groups batch i minimumModes))
    (fun i _ => groupImages_some hr allowed i (hp i) (hne i))
  exact ⟨images.flatten, by simp only [typeImages, hi]; rfl⟩

theorem assemble_some {prepareFuel fuel minimumModes : Nat} {modeIds : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (entries groups) minimumModes scalar = .success batch) (allowed : List ModVar)
    (hp : ∀i : Fin groups.length, ComparisonJointGroup.prepare prepareFuel assumptions required
      groups[i].group = .success groups[i].input)
    (hne : ∀i : Fin groups.length, groups[i].group.heads ≠ []) :
    ∃output, assemble allowed modeIds groups batch minimumModes = some output := by
  obtain ⟨modeAction, hm, _⟩ := projected_modes_finite_of_axes
    (fun _ _ hw => (ComparisonJointBatch.run_mode_atoms hr hw).1) allowed
  obtain ⟨images, hi⟩ := typeImages_some hr allowed hp hne
  exact ⟨⟨modeAction, images⟩, by simp [assemble, hm, hi]⟩

private theorem mapM_map {α β γ : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) (left : α → γ) (right : β → γ)
    (he : ∀x y, f x = some y → right y = left x) : ys.map right = xs.map left := by
  induction xs generalizing ys with
  | nil => simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst ys; rfl
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨y, hy, rest, hr, rfl⟩ := h
    simp only [List.map_cons, he x y hy, ih hr]

private theorem mapM_mem {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {y : β} (hy : y ∈ ys) : ∃x∈xs, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at h; subst ys; simp at hy
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, rest, hr, rfl⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨x, by simp, ha⟩
    · obtain ⟨z, hz, he⟩ := ih hr hy
      exact ⟨z, List.mem_cons_of_mem _ hz, he⟩

private theorem mapM_mem_input {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {x : α} (hx : x ∈ xs) : ∃y∈ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mapM_cons, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨b, hb, rest, hr, rfl⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, by simp, hb⟩
    · obtain ⟨z, hz, he⟩ := ih hr hx
      exact ⟨z, List.mem_cons_of_mem _ hz, he⟩

theorem groupImages_spec {allowed : List ModVar} {compiled : Compiled}
    {result : ComparisonJointAssembly.Result compiled.input compiled.group.leaves.length flex}
    {images : List (Nat × CompareTy)} (h : groupImages allowed compiled result = some images) :
    ∃b, basis allowed compiled.group = some b ∧
      (List.finRange compiled.group.leaves.length).mapM
        (fun j => do return (compiled.group.leaves[j], ← leaf b result j)) = some images := by
  simpa only [groupImages, bind, Option.bind_eq_some_iff] using h

theorem groupImages_domain {allowed : List ModVar} {compiled : Compiled}
    {result : ComparisonJointAssembly.Result compiled.input compiled.group.leaves.length flex}
    {images : List (Nat × CompareTy)} (h : groupImages allowed compiled result = some images) :
    images.map Prod.fst = compiled.group.leaves := by
  obtain ⟨b, hb, hm⟩ := groupImages_spec h
  have he := mapM_map hm (fun j => compiled.group.leaves[j]) Prod.fst (fun j image hj => by
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hj
    obtain ⟨t, _, rfl⟩ := hj
    rfl)
  simpa using he

theorem groupImages_origin {allowed : List ModVar} {compiled : Compiled}
    {result : ComparisonJointAssembly.Result compiled.input compiled.group.leaves.length flex}
    {images : List (Nat × CompareTy)} (h : groupImages allowed compiled result = some images)
    {entry : Nat × CompareTy} (he : entry ∈ images) :
    ∃b, basis allowed compiled.group = some b ∧ ∃j : Fin compiled.group.leaves.length,
      entry.1 = compiled.group.leaves[j] ∧ leaf b result j = some entry.2 := by
  obtain ⟨b, hb, hm⟩ := groupImages_spec h
  obtain ⟨j, _, hj⟩ := mapM_mem hm he
  simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hj
  obtain ⟨t, ht, rfl⟩ := hj
  exact ⟨b, hb, j, rfl, ht⟩

theorem groupImages_covers {allowed : List ModVar} {compiled : Compiled}
    {result : ComparisonJointAssembly.Result compiled.input compiled.group.leaves.length flex}
    {images : List (Nat × CompareTy)} (h : groupImages allowed compiled result = some images)
    (j : Fin compiled.group.leaves.length) :
    ∃b, basis allowed compiled.group = some b ∧ ∃t,
      (compiled.group.leaves[j], t) ∈ images ∧ leaf b result j = some t := by
  obtain ⟨b, hb, hm⟩ := groupImages_spec h
  obtain ⟨entry, he, hj⟩ := mapM_mem_input hm (List.mem_finRange j)
  simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at hj
  obtain ⟨t, ht, rfl⟩ := hj
  exact ⟨b, hb, t, he, ht⟩

theorem typeImages_spec {allowed : List ModVar} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) flex} {minimumModes : Nat}
    {images : List (Nat × CompareTy)} (h : typeImages allowed groups batch minimumModes = some images) :
    ∃pieces, (List.finRange groups.length).mapM
      (fun i => groupImages allowed groups[i] (localResult groups batch i minimumModes)) = some pieces ∧
      pieces.flatten = images := by
  simpa only [typeImages, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using h

theorem typeImages_domain {allowed : List ModVar} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) flex} {minimumModes : Nat}
    {images : List (Nat × CompareTy)} (h : typeImages allowed groups batch minimumModes = some images) :
    images.map Prod.fst = groups.flatMap (fun c => c.group.leaves) := by
  obtain ⟨pieces, hp, rfl⟩ := typeImages_spec h
  have he := mapM_map hp (fun i => groups[i].group.leaves) (List.map Prod.fst)
    (fun i _ hi => groupImages_domain hi)
  have hf := congrArg (List.map fun c : Compiled => c.group.leaves) (List.finRange_map_getElem groups)
  simp only [List.map_map, Function.comp_def] at hf
  simp only [List.map_flatten, he, Fin.getElem_fin, hf, List.flatMap_def]

theorem typeImages_origin {allowed : List ModVar} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) flex} {minimumModes : Nat}
    {images : List (Nat × CompareTy)} (h : typeImages allowed groups batch minimumModes = some images)
    {entry : Nat × CompareTy} (he : entry ∈ images) :
    ∃i : Fin groups.length, ∃b, basis allowed groups[i].group = some b ∧
      ∃j : Fin groups[i].group.leaves.length, entry.1 = groups[i].group.leaves[j] ∧
        leaf b (localResult groups batch i minimumModes) j = some entry.2 := by
  obtain ⟨pieces, hp, rfl⟩ := typeImages_spec h
  obtain ⟨piece, hm, he⟩ := List.mem_flatten.mp he
  obtain ⟨i, _, hi⟩ := mapM_mem hp hm
  exact ⟨i, groupImages_origin hi he⟩

theorem typeImages_covers {allowed : List ModVar} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) flex} {minimumModes : Nat}
    {images : List (Nat × CompareTy)} (h : typeImages allowed groups batch minimumModes = some images)
    (i : Fin groups.length) (j : Fin groups[i].group.leaves.length) :
    ∃b, basis allowed groups[i].group = some b ∧ ∃t,
      (groups[i].group.leaves[j], t) ∈ images ∧
        leaf b (localResult groups batch i minimumModes) j = some t := by
  obtain ⟨pieces, hp, rfl⟩ := typeImages_spec h
  obtain ⟨piece, hm, hi⟩ := mapM_mem_input hp (List.mem_finRange i)
  obtain ⟨b, hb, t, ht, he⟩ := groupImages_covers hi j
  exact ⟨b, hb, t, List.mem_flatten.mpr ⟨piece, hm, ht⟩, he⟩

theorem assemble_spec {allowed : List ModVar} {modeIds : List Nat} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    {minimumModes : Nat} {output : Output}
    (h : assemble allowed modeIds groups batch minimumModes = some output) :
    SymbolicSchemeModes.assemble (projectElimination allowed batch.solution.modes)
        (SchemeModeSynthesis.parameters modeIds) = some output.modeAction ∧
      typeImages allowed groups batch minimumModes = some output.types := by
  simp only [assemble, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨modeAction, hm, types, ht, he⟩ := h
  cases he
  exact ⟨hm, ht⟩

theorem assemble_domains {allowed : List ModVar} {modeIds : List Nat} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    {minimumModes : Nat} {output : Output}
    (h : assemble allowed modeIds groups batch minimumModes = some output) :
    output.types.map Prod.fst = groups.flatMap (fun c => c.group.leaves) ∧
      output.modeAction.types = [] ∧ output.modeAction.modes.map Prod.fst = modeIds := by
  have hs := assemble_spec h
  have hm := SymbolicSchemeModes.assemble_domain hs.1
  refine ⟨typeImages_domain hs.2, hm.1, ?_⟩
  simpa [SchemeModeSynthesis.parameters, List.map_map, Function.comp_def] using hm.2

end ModalityInference.ComparisonJointBatchReification
