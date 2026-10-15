import ModalityInference.Proofs.ComparisonJointBatchReification

/-! Finite batch outputs preserve the shared mode action, the exact leaf domain,
and the generated coordinate witnesses used in algebraic reflection. -/
namespace ModalityInference.ComparisonJointBatchReification

open ComparisonPropagation ComparisonControls ComparisonTupleReification
  ComparisonJointAssemblyReification

private theorem lookup_mem_nodup {α : Type} {xs : List (Nat × α)}
    (hn : (xs.map Prod.fst).Nodup) {n : Nat} {a : α} (ha : (n, a) ∈ xs) :
    xs.lookup n = some a := by
  induction xs with
  | nil => simp at ha
  | cons entry xs ih =>
    rcases entry with ⟨key, value⟩
    have hh := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with he | he
    · cases he
      simp
    · have hne : n ≠ key := by
        intro heq
        exact hh.1 (heq ▸ List.mem_map.mpr ⟨(n, a), he, rfl⟩)
      have hb : (n == key) = false := by simp [hne]
      simpa only [List.lookup_cons, hb] using ih hh.2 he

@[simp] theorem Output.substitution_mode (output : Output) (v : ModVar) :
    output.substitution.mode v = output.modeAction.mode v := by
  cases v <;> rfl

theorem assemble_origin {prepareFuel fuel minimumModes : Nat} {modeIds : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (entries groups) minimumModes scalar = .success batch)
    (hp : ∀i : Fin groups.length, ComparisonJointGroup.prepare prepareFuel assumptions required
      groups[i].group = .success groups[i].input)
    {allowed : List ModVar} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output)
    {entry : Nat × CompareTy} (hm : entry ∈ output.types) :
    ∃i : Fin groups.length, ∃b, basis allowed groups[i].group = some b ∧
      ∃j : Fin groups[i].group.leaves.length, entry.1 = groups[i].group.leaves[j] ∧
      ∃generated : ComparisonControls.Generated b,
        generated.term = entry.2 ∧ Total generated ∧
        ∀heads η coordinate, observe coordinate heads η generated =
          (localResult groups batch i minimumModes).state groups[i].group.heads.length
            (basisValue b.heads heads) (projectWorld allowed (encodeModes η))
            (ComparisonJointGroup.state coordinate j) := by
  obtain ⟨i, b, hb, j, hj, ht⟩ := typeImages_origin (assemble_spec ha).2 hm
  obtain ⟨generated, hg, htotal, he⟩ := leaf_complete hr i (hp i) hb j
  exact ⟨i, b, hb, j, hj, generated, Option.some.inj (hg.symm.trans ht), htotal, he⟩

theorem assemble_leaf {prepareFuel fuel minimumModes : Nat} {modeIds : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (entries groups) minimumModes scalar = .success batch)
    {allowed : List ModVar} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output)
    (hn : (groups.flatMap (fun c => c.group.leaves)).Nodup)
    (i : Fin groups.length)
    (hp : ComparisonJointGroup.prepare prepareFuel assumptions required groups[i].group =
      .success groups[i].input) (j : Fin groups[i].group.leaves.length) :
    ∃b, basis allowed groups[i].group = some b ∧ ∃generated : ComparisonControls.Generated b,
      output.substitution.type (.flex groups[i].group.leaves[j]) = generated.term ∧ Total generated ∧
      ∀heads η coordinate, observe coordinate heads η generated =
        (localResult groups batch i minimumModes).state groups[i].group.heads.length
          (basisValue b.heads heads) (projectWorld allowed (encodeModes η))
          (ComparisonJointGroup.state coordinate j) := by
  obtain ⟨b, hb, t, ht, hf⟩ := typeImages_covers (assemble_spec ha).2 i j
  obtain ⟨generated, hg, htotal, he⟩ := leaf_complete hr i hp hb j
  have hlookup := lookup_mem_nodup (by simpa only [(assemble_domains ha).1] using hn) ht
  have ht' : t = generated.term := Option.some.inj (hf.symm.trans hg)
  refine ⟨b, hb, generated, ?_, htotal, he⟩
  simp only [Output.substitution, CompareSubstitution.type, hlookup, Option.getD_some, ht']

theorem generated_defined {allowed : List ModVar} {group : ComparisonGroups.Group} {b : Basis}
    (hb : basis allowed group = some b) {generated : ComparisonControls.Generated b}
    (ht : Total generated) (Δ : Bounds) : generated.term.DefinedUnder Δ := by
  apply ht.definedUnder
  intro a ha
  rw [(basis_spec hb).1] at ha
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp ha
  simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]

theorem generated_support {allowed : List ModVar} {group : ComparisonGroups.Group} {b : Basis}
    (hb : basis allowed group = some b) (generated : ComparisonControls.Generated b) :
    ComparisonInterpolation.Supports (· ∈ group.heads) (· ∈ allowed) generated.term := by
  apply supports generated (· ∈ group.heads) (· ∈ allowed)
  · intro a ha
    rw [(basis_spec hb).1] at ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact hv
  · simpa only [(basis_spec hb).2] using fun v (hv : v ∈ allowed) => hv

theorem generated_shape {allowed : List ModVar} {group : ComparisonGroups.Group} {b : Basis}
    (hb : basis allowed group = some b) (generated : ComparisonControls.Generated b)
    {Δ : Bounds} {shape : ComparisonShape}
    (hshape : ∀v∈group.heads, ComparisonShape.Equivalent Δ (.var v) shape) :
    generated.term.WellShaped Δ ∧ ComparisonShape.Equivalent Δ generated.term.shape shape := by
  apply shaped generated
  intro a ha
  rw [(basis_spec hb).1] at ha
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
  exact ⟨True.intro, hshape v hv⟩

theorem assemble_types_defined {prepareFuel fuel minimumModes : Nat} {modeIds : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (entries groups) minimumModes scalar = .success batch)
    (hp : ∀i : Fin groups.length, ComparisonJointGroup.prepare prepareFuel assumptions required
      groups[i].group = .success groups[i].input)
    {allowed : List ModVar} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output) (Δ : Bounds) :
    ∀entry∈output.types, entry.2.DefinedUnder Δ := by
  intro entry he
  obtain ⟨i, b, hb, j, hj, generated, hg, ht, _⟩ := assemble_origin hr hp ha he
  rw [←hg]
  exact generated_defined hb ht Δ

theorem assemble_types_support {prepareFuel fuel minimumModes : Nat} {modeIds : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (entries groups) minimumModes scalar = .success batch)
    (hp : ∀i : Fin groups.length, ComparisonJointGroup.prepare prepareFuel assumptions required
      groups[i].group = .success groups[i].input)
    {allowed : List ModVar} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output) :
    ∀entry∈output.types, ∃i : Fin groups.length,
      ComparisonInterpolation.Supports (· ∈ groups[i].group.heads) (· ∈ allowed) entry.2 := by
  intro entry he
  obtain ⟨i, b, hb, j, hj, generated, hg, _⟩ := assemble_origin hr hp ha he
  exact ⟨i, hg ▸ generated_support hb generated⟩

theorem assemble_wellShaped {prepareFuel fuel minimumModes : Nat} {modeIds : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (entries groups) minimumModes scalar = .success batch)
    (hp : ∀i : Fin groups.length, ComparisonJointGroup.prepare prepareFuel assumptions required
      groups[i].group = .success groups[i].input)
    {allowed : List ModVar} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output) {Δ : Bounds}
    (hshape : ∀i : Fin groups.length, ∀v∈groups[i].group.heads,
      ComparisonShape.Equivalent Δ (.var v) (.var groups[i].group.shapeClass)) :
    output.substitution.WellShaped Δ := by
  intro entry he
  obtain ⟨i, b, hb, j, hj, generated, hg, _⟩ := assemble_origin hr hp ha he
  exact hg ▸ (generated_shape hb generated (hshape i)).1

theorem assemble_wellFormed {prepareFuel fuel minimumModes : Nat} {modeIds : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (entries groups) minimumModes scalar = .success batch)
    (hp : ∀i : Fin groups.length, ComparisonJointGroup.prepare prepareFuel assumptions required
      groups[i].group = .success groups[i].input)
    {allowed : List ModVar} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output) (Δ : Bounds) :
    output.substitution.WellFormedUnder Δ := by
  have ht := assemble_types_defined hr hp ha Δ
  constructor
  · rintro (n | n)
    · cases he : output.types.lookup n with
      | none => simp [Output.substitution, CompareSubstitution.type, he,
          CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
      | some a =>
        obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp he
        simpa only [Output.substitution, CompareSubstitution.type, he, Option.getD_some] using
          ht (n, a) (by simp [hx])
    · simp [CompareSubstitution.type,
        CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]
  · intro v η _
    exact SymbolicSchemeModes.assemble_wellFormed (assemble_spec ha).1 η v

theorem assemble_mode_fixed {allowed : List ModVar} {modeIds : List Nat} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    {minimumModes : Nat} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output) {v : ModVar}
    (hv : ∀n∈modeIds, v ≠ .flex n) : output.substitution.mode v = .var v := by
  rw [Output.substitution_mode]
  cases v with
  | rigid n => rfl
  | flex n =>
    exact SymbolicSchemeModes.assemble_fixed (assemble_spec ha).1
      (SchemeModeSynthesis.parameters_lookup_none (fun hn => hv n hn rfl))

theorem assemble_type_fixed {allowed : List ModVar} {modeIds : List Nat} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    {minimumModes : Nat} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output) {v : TypeVar}
    (hv : ∀n∈groups.flatMap (fun c => c.group.leaves), v ≠ .flex n) :
    output.substitution.type v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    have hl : output.types.lookup n = none := List.lookup_eq_none_iff.mpr (by
      intro entry he
      have hm : entry.1 ∈ groups.flatMap (fun c => c.group.leaves) := by
        rw [← (assemble_domains ha).1]
        exact List.mem_map.mpr ⟨entry, he, rfl⟩
      exact bne_iff_ne.mpr (fun h => hv entry.1 hm (congrArg TypeVar.flex h)))
    simp [Output.substitution, CompareSubstitution.type, hl]

theorem assemble_mode_support {allowed : List ModVar} {modeIds : List Nat} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    {minimumModes : Nat} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output) {n : Nat} (hn : n ∈ modeIds) :
    ∀v∈(output.substitution.mode (.flex n)).vars, v ∈ allowed := by
  rw [Output.substitution_mode]
  exact projected_mode_allowed (fun a ha => (SchemeModeSynthesis.mem_atoms_flex ha).mpr hn)
    (SymbolicSchemeModes.assemble_action (assemble_spec ha).1 (SchemeModeSynthesis.parameters_lookup hn))

theorem assemble_mode_eval {allowed : List ModVar} {modeIds : List Nat} {groups : List Compiled}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    {minimumModes : Nat} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output)
    (η : ModVar → Mode) (v : ModVar) (hv : v ∈ allowed ∨ ∃n∈modeIds, v = .flex n) :
    (output.substitution.mode v).eval (some ∘ η) = some
      (projectedModes (fun k => (batch.solution.modes.substitute k).eval
        (projectWorld allowed (encodeModes η))) v) := by
  exact projected_assemble_eval (assemble_spec ha).1 η v hv

private theorem supports_mode_fixed {P : TypeVar → Prop} {Q : ModVar → Prop}
    {a : CompareTy} (h : ComparisonInterpolation.Supports P Q a) {ms : ModVar → ModExpr}
    (hm : ∀v, Q v → ms v = .var v) : a.subst .var ms = a := by
  induction a <;> simp only [ComparisonInterpolation.Supports] at h <;> simp only [CompareTy.subst]
  case modal a m ih =>
    rw [ih h.1]
    exact congrArg (CompareTy.modal _) ((m.subst_congr (fun v hv => hm v (h.2 v hv))).trans m.subst_id)
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb |
      join a b iha ihb | meet a b iha ihb => rw [iha h.1, ihb h.2]

/-- The finite type leaves already contain the synthesized modal expressions.
The surrounding substitution fixes every name in those expressions. -/
theorem assemble_type_modes_fixed {prepareFuel fuel minimumModes : Nat} {modeIds : List Nat}
    {assumptions required : Bounds} {groups : List Compiled} {scalar : CNF}
    {batch : ComparisonJointBatch.Result (entries groups) (SchemeModeSynthesis.atoms modeIds)}
    (hr : ComparisonJointBatch.run fuel ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (entries groups) minimumModes scalar = .success batch)
    (hp : ∀i : Fin groups.length, ComparisonJointGroup.prepare prepareFuel assumptions required
      groups[i].group = .success groups[i].input)
    {allowed : List ModVar} {output : Output}
    (ha : assemble allowed modeIds groups batch minimumModes = some output)
    (hfixed : ∀v∈allowed, ∀n∈modeIds, v ≠ .flex n) :
    ∀entry∈output.types, entry.2.subst .var output.substitution.mode = entry.2 := by
  intro entry he
  obtain ⟨i, hs⟩ := assemble_types_support hr hp ha entry he
  exact supports_mode_fixed hs (fun v hv => assemble_mode_fixed ha (hfixed v hv))

end ModalityInference.ComparisonJointBatchReification
