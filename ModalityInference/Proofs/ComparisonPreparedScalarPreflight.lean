import ModalityInference.ComparisonPreparedScalarPreflight
import ModalityInference.Proofs.ComparisonPreparedModeWitness
import ModalityInference.Proofs.ComparisonCheckerTermination

/-! The scalar preflight is stable for arbitrary inputs and eventually accepts
every normalized admissible witness. It introduces no type or mode assumptions. -/
namespace ModalityInference.ComparisonPreparedScalarPreflight

open ComparisonPartialPropagation.Fuel

theorem run_settles (p : SchemePreparation.Prepared) :
    Settles (fun fuel => run fuel p) := by
  unfold run
  exact Settles.bind (modes_settles _ _) (fun _ => Settles.pure ())

theorem run_terminates (p : SchemePreparation.Prepared) :
    ∃threshold result, result ≠ .exhausted ∧ ∀fuel≥threshold,run fuel p=result :=
  (run_settles p).2

theorem run_stable {small large : Nat} {p : SchemePreparation.Prepared} {result : RunResult Unit}
    (h : run small p=result) (hr : result ≠ .exhausted) (hle : small≤large) :
    run large p=result := (run_settles p).1 hle h hr

theorem run_complete {p : SchemePreparation.Prepared} {strategy : (Nat → Bool) → Nat → Bool}
    (hu : ModalSynthesis.Uniform ModalSynthesis.locality
      (ComparisonPreparedScalar.flexibleAtoms p) strategy)
    (hv : ∀world,(formula p).eval (strategy world)=true) :
    ∃threshold,∀fuel≥threshold,run fuel p=.success () := by
  obtain ⟨threshold,hthreshold⟩ := SchemeModeSynthesis.run_complete hu hv
  refine ⟨threshold,fun fuel hf => ?_⟩
  obtain ⟨result,hr⟩ := hthreshold fuel hf
  simp only [run,hr,bind,pure,RunResult.bind]

/-- The original admissible witness establishes every required scalar guard;
only its finite mode domain is used to synthesize a uniform feasible strategy. -/
theorem run_prepared_complete {source target : Scheme} {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : ComparisonWitnessRestriction.Supported (SchemePreparation.prepare [] source target) σ)
    (hd : ComparisonPreparedScalar.ModeDomain (SchemePreparation.prepare [] source target) σ) :
    ∃threshold,∀fuel≥threshold,
      run fuel (SchemePreparation.prepare [] source target)=.success () := by
  let p:=SchemePreparation.prepare [] source target
  obtain ⟨n,scalar,hs⟩ := ComparisonPreparedScalar.run_complete p
  have hv := (ComparisonPreparedScalar.run_valid (hs n le_rfl)
      (fun _=>0) (fun _=>false) (fun _ _=>false) (SchemeModeSynthesis.strategy σ.mode)).mp
    (ComparisonPreparedScalar.run_prepared_valid hw hsp (hs n le_rfl) _ _ _)
  apply run_complete hd.uniform
  intro world
  change (!(boundsModeFormula p.assumptions).eval (SchemeModeSynthesis.strategy σ.mode world) ||
    (boundsModeFormula (ComparisonPreparedScalar.required p)).eval
      (SchemeModeSynthesis.strategy σ.mode world))=true
  cases ha : (boundsModeFormula p.assumptions).eval (SchemeModeSynthesis.strategy σ.mode world) with
  | false => rfl
  | true => simpa only [Bool.not_true,Bool.false_or] using hv world ha

end ModalityInference.ComparisonPreparedScalarPreflight
