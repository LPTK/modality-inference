import ModalityInference.Proofs.ComparisonJointElimination
import ModalityInference.Proofs.ComparisonJointBatchOutput
import ModalityInference.ComparisonSetup
import ModalityInference.Proofs.ComparisonCheckerScope
import ModalityInference.Proofs.ComparisonWitnessProperties
import ModalityInference.Proofs.ComparisonPreparedBounds

/-! Joint elimination changes only freshly allocated leaves and selected source
mode variables; fixed assumptions and declared target identifiers are preserved. -/
namespace ModalityInference.ComparisonJointElimination

open ComparisonJointBatchReification

private instance : LawfulMonad RunResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

theorem prepare_mem {fuel : Nat} {assumptions required : Bounds}
    {groups : List ComparisonGroups.Group} {compiled : List Compiled}
    (h : prepare fuel assumptions required groups = .success compiled) :
    ∀c∈compiled, c.group ∈ groups ∧
      ComparisonJointGroup.prepare fuel assumptions required c.group = .success c.input := by
  induction groups generalizing compiled with
  | nil => cases h; simp
  | cons group groups ih =>
    simp only [prepare, List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hg : ComparisonJointGroup.prepare fuel assumptions required group <;>
      simp only [hg] at h <;> try contradiction
    next input =>
      change (do
        let rest ← prepare fuel assumptions required groups
        pure (Compiled.mk group input :: rest)) = .success compiled at h
      cases hs : prepare fuel assumptions required groups <;>
        simp only [hs, bind, RunResult.bind, pure] at h <;> try contradiction
      next rest =>
        cases h
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨by simp, hg⟩
        · exact ⟨List.mem_cons_of_mem _ (ih hs c hc).1, (ih hs c hc).2⟩

theorem Trace.type_origin {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    {entry : Nat × CompareTy} (he : entry ∈ output.types) :
    ∃leaf∈templates.leaves, leaf.name = entry.1 := by
  have hk : entry.1 ∈ t.compiled.flatMap (fun c => c.group.leaves) := by
    rw [← (assemble_domains t.assembly).1]
    exact List.mem_map.mpr ⟨entry, he, rfl⟩
  obtain ⟨c, hc, hn⟩ := List.mem_flatMap.mp hk
  have hg := (prepare_mem t.preparation c hc).1
  obtain ⟨leaf, hl, he, _⟩ := ComparisonGroups.collect_leaf_origin t.collection c.group hg entry.1 hn
  exact ⟨leaf, hl, he⟩

theorem Trace.domainsAbove {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (t : Trace fuel p shapes templates reduced allowed modeIds minimumModes output)
    {nt nm : Nat} (ht : ∀leaf∈templates.leaves, nt ≤ leaf.name)
    (hm : ∀n∈modeIds, nm ≤ n) : output.substitution.DomainsAbove nt nm := by
  constructor
  · intro entry he
    obtain ⟨leaf, hl, heq⟩ := t.type_origin he
    exact heq ▸ ht leaf hl
  · intro entry he
    apply hm entry.1
    rw [← (assemble_domains t.assembly).2.2]
    exact List.mem_map.mpr ⟨entry, he, rfl⟩

theorem run_domainsAbove {fuel p shapes templates reduced allowed modeIds minimumModes output}
    (h : run fuel p shapes templates reduced allowed modeIds minimumModes = .success output)
    {nt nm : Nat} (ht : ∀leaf∈templates.leaves, nt ≤ leaf.name)
    (hm : ∀n∈modeIds, nm ≤ n) : output.substitution.DomainsAbove nt nm := by
  obtain ⟨t⟩ := run_trace h
  exact t.domainsAbove ht hm

theorem setup_run_domains {s : ComparisonChecker.Setup}
    {fuel : Nat} {reduced : ComparisonReduction.State} {allowed : List ModVar}
    {minimumModes : Nat} {output : Output}
    (h : run fuel s.work s.shapes s.templates reduced allowed s.modeIds minimumModes = .success output) :
    output.substitution.DomainsAbove s.original.nextType s.original.firstMode := by
  apply run_domainsAbove h
  · intro leaf hl
    exact (ComparisonSkeleton.allocate_leaf_range s.work s.shapes s.names s.original.nextType
      s.annotations.nextMode leaf hl).1
  · intro n hn
    obtain ⟨k, _, he⟩ := List.mem_range'.mp (List.mem_filter.mp hn).1
    omega

theorem setup_run_fixes {s : ComparisonChecker.Setup}
    {fuel : Nat} {reduced : ComparisonReduction.State} {allowed : List ModVar}
    {minimumModes : Nat} {output : Output}
    (h : run fuel s.work s.shapes s.templates reduced allowed s.modeIds minimumModes = .success output) :
    (∀v, v.index < s.original.nextType → output.substitution.type v = .var v) ∧
      (∀v, v.index < s.original.firstMode → output.substitution.mode v = .var v) :=
  ⟨(setup_run_domains h).type_fixed, (setup_run_domains h).mode_fixed⟩

theorem setup_run_target {s : ComparisonChecker.Setup}
    {fuel : Nat} {reduced : ComparisonReduction.State} {allowed : List ModVar}
    {minimumModes : Nat} {output : Output}
    (h : run fuel s.work s.shapes s.templates reduced allowed s.modeIds minimumModes = .success output)
    (ht : s.original.targetType.Bounded s.original.nextType s.original.firstMode) :
    output.substitution.ty s.original.targetType = .ofTy s.original.targetType := by
  have hb := (s.original.targetType.bounded_iff _ _).mp ht
  exact CompareSubstitution.ty_fixed _
    (fun v hv => (setup_run_fixes h).1 v (hb.1 v hv))
    (fun v hv => (setup_run_fixes h).2 v (hb.2 v hv))

theorem setup_run_prepared_fixed {s : ComparisonChecker.Setup}
    {ambient : Bounds} {source target : Scheme}
    (hp : s.original = SchemePreparation.prepare ambient source target)
    {fuel : Nat} {reduced : ComparisonReduction.State} {allowed : List ModVar}
    {minimumModes : Nat} {output : Output}
    (h : run fuel s.work s.shapes s.templates reduced allowed s.modeIds minimumModes = .success output) :
    (∀v∈s.original.assumptions.typeVars, output.substitution.type v = .var v) ∧
      (∀v∈s.original.assumptions.modVars, output.substitution.mode v = .var v) ∧
      output.substitution.ty s.original.targetType = .ofTy s.original.targetType := by
  have hb : s.original.assumptions.Bounded s.original.nextType s.original.firstMode := by
    rw [hp]
    exact (SchemePreparation.prepare_assumptions_bounded_first ambient source target).mono
      (Nat.le_add_right _ _) (Nat.le_refl _)
  have ht : s.original.targetType.Bounded s.original.nextType s.original.firstMode := by
    rw [hp]
    exact (SchemePreparation.prepare_targetType_bounded_first ambient source target).mono
      (Nat.le_add_right _ _) (Nat.le_refl _)
  have hb := (s.original.assumptions.bounded_iff _ _).mp hb
  exact ⟨fun v hv => (setup_run_fixes h).1 v (hb.1 v hv),
    fun v hv => (setup_run_fixes h).2 v (hb.2 v hv), setup_run_target h ht⟩

end ModalityInference.ComparisonJointElimination
