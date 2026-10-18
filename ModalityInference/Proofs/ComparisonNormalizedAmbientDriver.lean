import ModalityInference.ComparisonNormalizedAmbientDriver
import ModalityInference.Proofs.ComparisonAmbientNormalization
import ModalityInference.Proofs.ComparisonAmbientDriver
import ModalityInference.Proofs.ComparisonPreparedDriverCompleteness

namespace ModalityInference.ComparisonNormalizedAmbientDriver
open ComparisonAmbientNormalization

/-- The returned witness is certified in the original ambient context, with
exactly the original quantified domain and the original fresh target names. -/
theorem run_result {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {result : CompareSubstitution} (h : run fuel ambient source target=.success result) :
    let p:=SchemePreparation.prepare ambient source target
    CompareInstantiatesUnder p.assumptions source result ∧ result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  obtain ⟨hi,hs,hb,ht⟩ := ComparisonAmbientDriver.run_result h
  have hc := prepared_backward ambient source target
  refine ⟨⟨hi.domain,hi.images.of_models hc.modes,hc.defined hi.body⟩,
    fun entry he => hc.wellShaped (hs entry he),fun c he => hc.entails (hb c he),?_⟩
  have ht' := hc.algebra ht
  simpa only [SchemePreparation.prepare,subsumptionIndices_normalize] using ht'

theorem run_algebra_subsumesUnder {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {result : CompareSubstitution} (h : run fuel ambient source target=.success result) :
    AlgebraSubsumesUnder ambient source target := by
  obtain ⟨hi,hs,hb,ht⟩ := run_result h
  exact ⟨result,hi.domain,hs,hi.images,hi.body,hb,ht⟩

@[simp] theorem run_nil (fuel : Nat) (source target : Scheme) :
    run fuel [] source target=ComparisonPreparedDriver.run fuel source target := by
  simp only [run,normalize_nil,ComparisonAmbientDriver.run_nil]

open ComparisonPartialPropagation.Fuel

theorem run_settles (ambient : Bounds) (source target : Scheme) :
    Settles (fun fuel => run fuel ambient source target) :=
  ComparisonAmbientDriver.run_settles (normalize ambient) source target

theorem run_terminates (ambient : Bounds) (source target : Scheme) :
    ∃threshold result,result ≠ .exhausted ∧
      ∀fuel≥threshold,run fuel ambient source target=result :=
  (run_settles ambient source target).2

theorem run_stable {small large : Nat} {ambient : Bounds} {source target : Scheme}
    {result : RunResult CompareSubstitution}
    (h : run small ambient source target=result) (hr : result ≠ .exhausted)
    (hle : small≤large) : run large ambient source target=result :=
  (run_settles ambient source target).1 hle h hr

/-- Conservative normalization can discharge redundant raw assumptions without
requiring their written partial annotations to become defined. -/
theorem run_complete_normalizes_empty {ambient : Bounds} {source target : Scheme}
    (he : normalize ambient=[])
    (ht : source.typeParams.Nodup) (hm : source.modParams.Nodup)
    (h : AlgebraSubsumesUnder ambient source target)
    (hshape : ∃φ,ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    ∃threshold result,∀fuel≥threshold,run fuel ambient source target=.success result := by
  have hs : AlgebraSubsumesUnder [] source target := by
    simpa only [he] using (subsumes_iff ambient source target).mpr h
  obtain ⟨φ,hφ⟩ := hshape
  have hφ' := (prepared_backward ambient source.requireDefinedInstances target).shapes φ hφ
  rw [he] at hφ'
  obtain ⟨threshold,result,hr⟩ :=
    ComparisonPreparedDriver.run_complete_finite_model ht hm hs ⟨φ,hφ'⟩
  exact ⟨threshold,result,fun fuel hf => by
    simpa only [run,he,ComparisonAmbientDriver.run_nil] using hr fuel hf⟩

end ModalityInference.ComparisonNormalizedAmbientDriver
