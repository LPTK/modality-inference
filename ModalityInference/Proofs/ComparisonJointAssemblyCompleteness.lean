import ModalityInference.Proofs.ComparisonJointCoordinateWitness
import ModalityInference.Proofs.ComparisonJointAssembly
import ModalityInference.Proofs.ComparisonJointAssemblyNominal

/-! A finite coordinate witness induces one shared selector vector and one
modality strategy satisfying the assembled group program. Both axis summaries
retain the same nominal store and every original scalar obligation. -/
namespace ModalityInference.ComparisonJointAssembly

open ComparisonPropagation ComparisonJointGroup ComparisonJointGuarded
open ComparisonFixedModeWitness ComparisonJointCoordinateWitness

def jointChoices (input : Input) (localChoice otherChoice : Nat → Bool)
    (i : Fin (constantCount input)) : Bool :=
  if i.val = 0 then false
  else if i.val ≤ input.locality.length then localChoice (i.val - 1)
  else otherChoice (i.val - input.locality.length - 1)

theorem jointChoices_locality (input : Input) (localChoice otherChoice : Nat → Bool)
    {i : Nat} (hi : i < input.locality.length) :
    ComparisonJointAxisSummary.parameterWorld (localityEmbedding input)
      (jointChoices input localChoice otherChoice) (fun _ => false) i = localChoice i := by
  change ComparisonJointAxisSummary.parameterWorld (localityEmbedding input)
    (jointChoices input localChoice otherChoice) (fun _ => false)
    (⟨i, by omega⟩ : Fin (input.locality.length+1)).val = localChoice i
  rw [ComparisonJointAxisSummary.parameterWorld_selector]
  simp [localityEmbedding, hi, jointChoices, show i+1 ≤ input.locality.length by omega]

theorem jointChoices_other (input : Input) (localChoice otherChoice : Nat → Bool)
    {i : Nat} (hi : i < input.other.length) :
    ComparisonJointAxisSummary.parameterWorld (otherEmbedding input)
      (jointChoices input localChoice otherChoice) (fun _ => false) i = otherChoice i := by
  change ComparisonJointAxisSummary.parameterWorld (otherEmbedding input)
    (jointChoices input localChoice otherChoice) (fun _ => false)
    (⟨i, by omega⟩ : Fin (input.other.length+1)).val = otherChoice i
  rw [ComparisonJointAxisSummary.parameterWorld_selector]
  simp [otherEmbedding, hi, jointChoices,
    show ¬input.locality.length+i+1 ≤ input.locality.length by omega,
    show input.locality.length+i+1-input.locality.length-1=i by omega]

theorem strategy_modeUniform (images : ModVar → ModExpr) :
    ComparisonJointAxes.ModeUniform ModalSynthesis.locality (SchemeModeSynthesis.strategy images) := by
  intro left right i h
  apply SymbolicModes.eval_congr
  intro w hw
  apply h w
  exact SchemeModeSynthesis.coordinate_support _ (Nat.mod_lt _ (by decide)) hw

theorem compile_complete {fuel minimumModes cutoff : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input} {σ : CompareSubstitution}
    (hprepare : prepare fuel assumptions required g = .success input)
    (hb : 6 * cutoff ≤ minimumModes) (hs : FixedImages cutoff σ)
    (hheads : ∀ i : Fin g.leaves.length, ComparisonInterpolation.Supports (· ∈ g.heads)
      (fun v => v.index < cutoff) (σ.type (.flex g.leaves[i])))
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hp : (nominalStore g σ).Polynomial g.heads.length)
    (hinput : ∀ headWorld inputs, input.Holds g.heads.length
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs))
      (witnessValues g σ headWorld inputs)) :
    ∃ choice : Fin (constantCount input) → Bool,
      Holds choice (nominalStore g σ) (SchemeModeSynthesis.strategy σ.mode)
        (compile ModalSynthesis.locality g.leaves.length g.heads.length input minimumModes) := by
  obtain ⟨localChoice, hlocal, hlocalOther⟩ := ComparisonJointAxes.selectors_complete
    (axisValues_uniform true g σ) (strategy_modeUniform σ.mode)
    (fun headWorld inputs => (prepare_axis_witness hprepare (hinput headWorld inputs)).1)
  obtain ⟨otherChoice, hother, hotherOther⟩ := ComparisonJointAxes.selectors_complete
    (axisValues_uniform false g σ) (strategy_modeUniform σ.mode)
    (fun headWorld inputs => (prepare_axis_witness hprepare (hinput headWorld inputs)).2)
  refine ⟨jointChoices input localChoice otherChoice, ?_⟩
  simp only [compile, holds_append, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hvalues : ∀ headWorld inputs i, witnessValues g σ headWorld inputs (state .unaffected i) =
        ComparisonJointProgram.values (nominalStore g σ) headWorld i := by
      intro headWorld inputs i
      apply Bool.eq_iff_iff.mpr
      rw [ComparisonJointProgram.values_true]
      exact (nominalStore_correct g σ headWorld inputs i).symm
    apply (nominalProgram_guarded_iff hprepare hp.2.1 _ (witnessValues g σ)
      (SchemeModeSynthesis.strategy σ.mode) hvalues).mpr
    intro headWorld inputs
    rw [← parameterValue_valuation]
    exact (hinput headWorld inputs).1
  · apply axis_compile_complete (hb.trans (modeBound_minimum input minimumModes)) hs hheads hf
      (by omega) (Nat.le_succ _) (prepare_linear hprepare).2.1 hp.2.1 ?_
      (input_supported input (4*g.leaves.length+g.heads.length) minimumModes).1
    intro headWorld inputs
    rw [ComparisonJointAxes.ownClauses_holds]
    intro i hi
    rw [jointChoices_locality input localChoice otherChoice hi]
    exact (ComparisonJointAxes.ownClauses_holds _ _ _ _ _ _ _).mp (hlocal headWorld inputs) i hi
  · apply axis_compile_complete (hb.trans (modeBound_minimum input minimumModes)) hs hheads hf
      (by omega) (Nat.le_succ _) (prepare_linear hprepare).2.2 hp.2.1 ?_
      (input_supported input (4*g.leaves.length+g.heads.length) minimumModes).2.1
    intro headWorld inputs
    rw [ComparisonJointAxes.ownClauses_holds]
    intro i hi
    rw [jointChoices_other input localChoice otherChoice hi]
    exact (ComparisonJointAxes.ownClauses_holds _ _ _ _ _ _ _).mp (hother headWorld inputs) i hi
  · apply (oppositeClauses_correct (localityEmbedding input) _ _ _ (Nat.le_succ _)).mpr
    intro inputs
    rw [ComparisonJointAxes.otherClauses_holds]
    intro i hi
    rw [jointChoices_locality input localChoice otherChoice hi]
    exact (ComparisonJointAxes.otherClauses_holds _ _ _ _ _ _ _).mp (hlocalOther inputs) i hi
  · apply (oppositeClauses_correct (otherEmbedding input) _ _ _ (Nat.le_succ _)).mpr
    intro inputs
    rw [ComparisonJointAxes.otherClauses_holds]
    intro i hi
    rw [jointChoices_other input localChoice otherChoice hi]
    exact (ComparisonJointAxes.otherClauses_holds _ _ _ _ _ _ _).mp (hotherOther inputs) i hi
  · apply (scalarClauses_correct _ _ _ _).mpr
    intro inputs
    simpa only [modes_parameterValue] using (hinput (fun _ => false) inputs).2.2.2

theorem strategy_uniform_of_modeDomain {σ : CompareSubstitution} {modeIds : List Nat}
    (hscope : ∀ entry ∈ σ.modes, entry.1 ∈ modeIds) :
    ModalSynthesis.Uniform ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
      (SchemeModeSynthesis.strategy σ.mode) := by
  apply SchemeModeSynthesis.strategy_uniform
  intro v hv
  cases v with
  | rigid n => rfl
  | flex n =>
    have hn : σ.modes.lookup n = none := List.lookup_eq_none_iff.mpr fun entry he => by
      simpa only [bne_iff_ne] using
        (fun h : n = entry.1 => hv entry.1 (hscope entry he) (congrArg ModVar.flex h))
    simp [CompareSubstitution.mode, hn]

/-- Every finite admissible coordinate witness reaches success in the actual
assembled solver, with all groups permitted to retain the same mode strategy. -/
theorem run_complete {fuel minimumModes cutoff : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {input : Input} {σ : CompareSubstitution} {modeIds : List Nat}
    (hprepare : prepare fuel assumptions required g = .success input)
    (hb : 6 * cutoff ≤ minimumModes) (hs : FixedImages cutoff σ)
    (hheads : ∀ i : Fin g.leaves.length, ComparisonInterpolation.Supports (· ∈ g.heads)
      (fun v => v.index < cutoff) (σ.type (.flex g.leaves[i])))
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hp : (nominalStore g σ).Polynomial g.heads.length)
    (hinput : ∀ headWorld inputs, input.Holds g.heads.length
      (parameterValue g.heads.length headWorld (SchemeModeSynthesis.strategy σ.mode inputs))
      (witnessValues g σ headWorld inputs))
    (hscope : ∀ entry ∈ σ.modes, entry.1 ∈ modeIds) :
    ∃ n, ∀ budget ≥ n, ∃ result,
      run budget ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
        g.leaves.length g.heads.length input minimumModes = .success result := by
  obtain ⟨choice, hc⟩ := compile_complete hprepare hb hs hheads hf hp hinput
  obtain ⟨n, hn⟩ := ComparisonJointGuarded.run_complete
    ⟨choice, nominalStore g σ, hp, SchemeModeSynthesis.strategy σ.mode,
      strategy_uniform_of_modeDomain hscope, hc⟩
  refine ⟨n, ?_⟩
  intro budget hfuel
  obtain ⟨solution, hsolution⟩ := hn budget hfuel
  exact ⟨reconstruct ModalSynthesis.locality g.leaves.length g.heads.length input solution minimumModes,
    by simp [run, hsolution, bind, RunResult.bind, pure]⟩

end ModalityInference.ComparisonJointAssembly
