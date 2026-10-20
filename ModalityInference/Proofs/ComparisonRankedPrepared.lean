import ModalityInference.ComparisonRankedPrepared
import ModalityInference.Proofs.ComparisonRankedEndpointReflection
import ModalityInference.Proofs.ComparisonPreparedWitness
import ModalityInference.Proofs.ComparisonPreparedDriver
import ModalityInference.Proofs.BackendComplete

/-! Original-context guard checking and witness reconstruction for the exact
fixed-rank, shared-modality comparison stage. -/
namespace ModalityInference.ComparisonRankedPrepared

open ComparisonPreparation ComparisonSelectedBases ComparisonRankedBasis
  ComparisonControls ComparisonAlgebra ComparisonRankedDecision

theorem count_pos (p : SchemePreparation.Prepared) (rank : Nat) : 0 < count p rank := by
  exact Nat.pow_pos (by decide)

theorem modeScope_iff (p : SchemePreparation.Prepared) (modes : List (Nat × ModExpr)) :
    modeScope p modes = true ↔ ∀ entry ∈ modes, p.firstMode ≤ entry.1 := by
  simp [modeScope]

theorem supported_iff (p : SchemePreparation.Prepared) (modes : List (Nat × ModExpr)) :
    supported p modes = true ↔
      ∀ v ∈ inputModes p, ∀ w ∈ (modeFunction modes v).vars, w ∈ inputModes p := by
  simp only [supported, List.all_eq_true, List.contains_iff_mem, ModExpr.mem_freeVariables]

theorem scalarQuery_iff (p : SchemePreparation.Prepared) (modes : List (Nat × ModExpr)) :
    (∀ world, (scalarQuery p modes).eval world = true) ↔
      EntailsAll p.assumptions
        ((ComparisonPreparedScalar.required p).map
          (Constraint.subst TypeExpr.var (modeFunction modes))) ∧
      ∀ entry ∈ modes, Entails p.assumptions (.defined entry.2) := by
  simp only [scalarQuery, BoolExpr.eval_imp_true, boundsModeFormula_correct]
  constructor
  · intro h
    have hm : ∀ η, ModeModels p.assumptions η → ModeModels (guards p modes) η := by
      intro η hη
      simpa only [projectedModes_encodeModes] using h (encodeModes η) (by
        simpa only [projectedModes_encodeModes] using hη)
    refine ⟨(ComparisonPreparedScalar.required_entails_iff _ _ _).mpr ?_, ?_⟩
    · intro η hη c hc
      exact hm η hη c (List.mem_append_left _ hc)
    · intro entry he η hη
      exact hm η hη _ (List.mem_append_right _ (List.mem_map.mpr ⟨entry,he,rfl⟩))
  · rintro ⟨hrequired, himages⟩ world hw c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact (ComparisonPreparedScalar.required_entails_iff _ _ _).mp hrequired _ hw c hc
    · obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hc
      exact himages entry he _ hw

theorem endpoint_support (p : SchemePreparation.Prepared) :
    ∀ pair ∈ endpoints p,
      ComparisonInterpolation.Supports (· ∈ inputNames p) (· ∈ inputModes p) (.ofTy pair.1) ∧
      ComparisonInterpolation.Supports (· ∈ inputNames p) (· ∈ inputModes p) (.ofTy pair.2) := by
  intro pair hp
  have h := ComparisonSignedObservation.endpoints_input hp
  exact ⟨ComparisonStructuralEndpoints.ofTy_supported pair.1
    (fun _ hv => (mem_inputNames p _).mpr (h.1 hv))
    (fun _ hv => (mem_inputModes p _).mpr (h.2.2.1 hv)),
    ComparisonStructuralEndpoints.ofTy_supported pair.2
      (fun _ hv => (mem_inputNames p _).mpr (h.2.1 hv))
      (fun _ hv => (mem_inputModes p _).mpr (h.2.2.2 hv))⟩

theorem selected_type {p : SchemePreparation.Prepared}
    {images : List (Nat × CompareTy)} {modes : List (Nat × ModExpr)}
    (hk : images.map Prod.fst = inputTypeKeys p) :
    imageTypes (inputTypeKeys p) (selected images) =
      ({ types := images, modes := modes } : CompareSubstitution).type := by
  funext v
  cases v with
  | rigid => rfl
  | flex n =>
    by_cases hn : n ∈ inputTypeKeys p
    · obtain ⟨a, ha⟩ : ∃ a, images.lookup n = some a := by
        cases he : images.lookup n with
        | some a => exact ⟨a,rfl⟩
        | none =>
          have hn' : n ∈ images.map Prod.fst := hk ▸ hn
          obtain ⟨entry,he',heq⟩ := List.mem_map.mp hn'
          have hne := (List.lookup_eq_none_iff.mp he) entry he'
          exact False.elim ((bne_iff_ne.mp hne) heq.symm)
      simp [imageTypes, hn, selected, CompareSubstitution.type, ha]
    · have he : images.lookup n = none := by
        apply List.lookup_eq_none_iff.mpr
        intro entry he
        apply bne_iff_ne.mpr
        intro heq
        exact hn (hk ▸ List.mem_map.mpr ⟨entry,he,heq.symm⟩)
      simp [imageTypes, hn, CompareSubstitution.type, he]

theorem run_spec {fuel p rank modes result}
    (h : run fuel p rank modes = .success result) :
    modeScope p modes = true ∧ supported p modes = true ∧
      (∃ report, ConcreteBackend.decideFormula fuel (scalarQuery p modes) = .success report ∧
        report.valid = true) ∧
      ∃ images, ComparisonRankedDecision.run fuel p.assumptions (input p rank)
        (typeNames p rank) (modeNames p rank) (count p rank) (modeFunction modes) (endpoints p) =
          .success images ∧ result = {types := images.images, modes := modes} := by
  by_cases hscope : modeScope p modes = true
  · by_cases hsupport : supported p modes = true
    · simp only [run, hscope, hsupport, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      cases hs : ConcreteBackend.decideFormula fuel (scalarQuery p modes) with
      | rejected _ => simp [hs, bind, RunResult.bind] at h
      | exhausted => simp [hs, bind, RunResult.bind] at h
      | success report =>
        simp only [hs, bind, RunResult.bind] at h
        split at h
        · cases h
        rename_i hv
        cases hr : ComparisonRankedDecision.run fuel p.assumptions (input p rank)
            (typeNames p rank) (modeNames p rank) (count p rank) (modeFunction modes) (endpoints p) with
        | rejected _ => simp [hr] at h
        | exhausted => simp [hr] at h
        | success images =>
          simp only [hr, pure, RunResult.success.injEq] at h
          subst result
          exact ⟨hscope, hsupport, ⟨report,rfl,by simpa using hv⟩, images,rfl,rfl⟩
    · simp [run, hscope, hsupport, bind, RunResult.bind] at h
  · simp [run, hscope, bind, RunResult.bind] at h

theorem run_sound {fuel rank modes result ambient source target}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (h : run fuel (SchemePreparation.prepare ambient source target) rank modes = .success result) :
    PreparedWitnessUnder (SchemePreparation.prepare ambient source target) result := by
  let p := SchemePreparation.prepare ambient source target
  obtain ⟨hscope, hsupport, ⟨report, hreport, hvalid⟩, output, hout, rfl⟩ := run_spec h
  obtain ⟨hkeys, hforms, hmachine⟩ := ComparisonRankedDecision.run_sound hout
  change output.images.map Prod.fst = inputTypeKeys p at hkeys
  have hscalar := (scalarQuery_iff p modes).mp
    ((ConcreteBackend.decideFormula_correct hreport).mp hvalid)
  let σ : CompareSubstitution := {types := output.images, modes := modes}
  have hreps : ∀ image ∈ output.images, Representable p.assumptions .unit image.2 := by
    intro image hi
    exact (hforms image hi).representable
      (types_representable hn (inputNames p) (inputModes p) rank)
  have hdefined : σ.WellFormedUnder p.assumptions :=
    CompareSubstitution.wellFormedUnder_of_images
      (fun image hi => (hreps image hi).2.1) hscalar.2
  have hinst : ∀ a, instantiate (inputTypeKeys p) (selected output.images)
      (modeFunction modes) a = σ.ty a := by
    intro a
    simp only [instantiate, selected_type (modes := modes) hkeys, CompareSubstitution.ty]
    rfl
  have himages : ∀ k ∈ inputTypeKeys p,
      LatticeForm (imageBasis p rank).types (selected output.images k) := by
    intro k hk
    exact hforms _ (selected_mem (hkeys.symm ▸ hk))
  have hguards : ∀ pair ∈ endpoints p,
      (instantiate (inputTypeKeys p) (selected output.images) (modeFunction modes) pair.1).DefinedUnder
        p.assumptions ∧
      (instantiate (inputTypeKeys p) (selected output.images) (modeFunction modes) pair.2).DefinedUnder
        p.assumptions := by
    intro pair hp
    simp only [hinst]
    have hg := ComparisonPreparedScalar.endpoint_guards hscalar.1 hp
    exact ⟨ComparisonSignedClosedAlignment.defined_of_annotations hdefined.types pair.1
      (hg _ (by simp)), ComparisonSignedClosedAlignment.defined_of_annotations hdefined.types pair.2
        (hg _ (by simp))⟩
  have hpairs := (endpoints_iff_machineValid hn hΔ (inputNames p) (inputModes p) rank
    (inputTypeKeys p) (selected output.images) (modeFunction modes) (endpoints p)
    himages ((supported_iff p modes).mp hsupport) (endpoint_support p) hguards).mpr hmachine
  apply ComparisonPreparedWitness.prepared_of_endpoints
  · refine ⟨?_,(modeScope_iff p modes).mp hscope⟩
    intro image hi
    exact ((mem_inputTypeKeys p image.1).mp
      (hkeys ▸ List.mem_map.mpr ⟨image,hi,rfl⟩)).2
  · exact fun image hi => (hreps image hi).1
  · exact hdefined
  · exact hscalar.1
  · intro pair hp
    simpa only [hinst] using hpairs pair (List.mem_append_right _ hp)

def normalModes (σ : CompareSubstitution) : List (Nat × ModExpr) :=
  (σ.modes.map Prod.fst).map fun n => (n, σ.mode (.flex n))

theorem normalModes_mode (σ : CompareSubstitution) : modeFunction (normalModes σ) = σ.mode := by
  funext v
  cases v with
  | rigid => rfl
  | flex n =>
    by_cases hn : n ∈ σ.modes.map Prod.fst
    · simp only [modeFunction, CompareSubstitution.mode, normalModes, List.lookup_graph _ hn,
        Option.getD_some]
    · have he : σ.modes.lookup n = none := by
        apply List.lookup_eq_none_iff.mpr
        intro entry he
        exact bne_iff_ne.mpr (fun h => hn (List.mem_map.mpr ⟨entry,he,h.symm⟩))
      have he' : (normalModes σ).lookup n = none := by
        apply List.lookup_eq_none_iff.mpr
        intro entry he
        obtain ⟨k,hk,rfl⟩ := List.mem_map.mp he
        exact bne_iff_ne.mpr (fun h => hn (h ▸ hk))
      simp [modeFunction, CompareSubstitution.mode, he, he']

theorem prepared_required {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hs : ComparisonWitnessRestriction.Supported (SchemePreparation.prepare ambient source target) σ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    EntailsAll (SchemePreparation.prepare ambient source target).assumptions
      ((ComparisonPreparedScalar.required (SchemePreparation.prepare ambient source target)).map
        (Constraint.subst TypeExpr.var σ.mode)) := by
  let p := SchemePreparation.prepare ambient source target
  intro c hc
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp ho with hscalar | hguard
  · have he := ComparisonGuardedTotal.scalarBounds_entails hw.1.2.2.1
      _ (List.mem_map.mpr ⟨original,hscalar,rfl⟩)
    have hkind := ComparisonPreparedScalar.required_scalar p (List.mem_append_left _ hscalar)
    cases original <;> try contradiction
    · exact he
    · exact he
  · obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hguard
    obtain ⟨pair,hp,hm⟩ := List.mem_flatMap.mp hm
    have hg := ComparisonStructuralEndpoints.all_guarded_of_boundsDefined hw hs hΔ _
      (ComparisonSignedObservation.prepared_interpreted_mem hw hp)
    rcases List.mem_append.mp hm with hl | hr
    · exact ComparisonSignedObservation.annotation_defined hg.left_defined m hl
    · exact ComparisonSignedObservation.annotation_defined hg.right_defined m hr

theorem prepared_scalar {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hs : ComparisonWitnessRestriction.Supported (SchemePreparation.prepare ambient source target) σ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    modeScope (SchemePreparation.prepare ambient source target) (normalModes σ) = true ∧
      supported (SchemePreparation.prepare ambient source target) (normalModes σ) = true ∧
      ∀ world, (scalarQuery (SchemePreparation.prepare ambient source target) (normalModes σ)).eval world =
        true := by
  let p := SchemePreparation.prepare ambient source target
  refine ⟨(modeScope_iff _ _).mpr ?_,(supported_iff _ _).mpr ?_,
    (scalarQuery_iff _ _).mpr ?_⟩
  · intro entry he
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
    obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hn
    exact hw.1.1.2 old hold
  · rw [normalModes_mode]
    intro v hv w hw'
    exact (mem_inputModes p w).mpr (hs.mode ((mem_inputModes p v).mp hv) hw')
  · rw [normalModes_mode]
    refine ⟨prepared_required hw hs hΔ,?_⟩
    intro entry he
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp he
    exact hw.2.1.modes (.flex n)

theorem prepared_complete {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    ∃ rank modes threshold result, ∀ fuel ≥ threshold,
      run fuel (SchemePreparation.prepare ambient source target) rank modes = .success result := by
  let p := SchemePreparation.prepare ambient source target
  obtain ⟨rank,τ,hτ,_,_,hs,himages⟩ := prepared_ranked_lists_complete hn hw
  have hscalar := prepared_scalar hτ hs hΔ
  obtain ⟨scalarFuel,report,hreport⟩ := ConcreteBackend.decideFormula_complete
    (scalarQuery p (normalModes τ))
  have hv : report.valid = true :=
    (ConcreteBackend.decideFormula_correct (hreport scalarFuel le_rfl)).mpr hscalar.2.2
  have hmachine := machineValid_of_endpoints hΔ (inputTypeKeys p)
    (typeNames p rank) (modeNames p rank) (count p rank) τ.mode (endpoints p)
    (fun n => τ.type (.flex n)) (prepared_witness_endpoints hτ hs hΔ)
  obtain ⟨typeFuel,result,hresult⟩ := ComparisonRankedDecision.run_complete p.assumptions
    (inputTypeKeys p) (fun _ => imageBasis p rank)
    (typeNames p rank) (modeNames p rank) (count p rank) τ.mode (endpoints p)
    (fun n => τ.type (.flex n))
    (fun n hn => (himages (.flex n)
      ((mem_inputNames p _).mp ((mem_inputTypeKeys p n).mp hn).1)).1) hmachine
  refine ⟨rank,normalModes τ,max scalarFuel typeFuel,
    {types := result.images, modes := normalModes τ},?_⟩
  intro fuel hf
  have hsf := hreport fuel ((Nat.le_max_left _ _).trans hf)
  have htf := hresult fuel ((Nat.le_max_right _ _).trans hf)
  change ComparisonRankedDecision.run fuel p.assumptions (input p rank)
    (typeNames p rank) (modeNames p rank) (count p rank) τ.mode (endpoints p) = _ at htf
  change run fuel p rank (normalModes τ) = _
  change modeScope p (normalModes τ) = true ∧ supported p (normalModes τ) = true ∧ _ at hscalar
  simp only [run,hscalar.1,hscalar.2.1,Bool.not_true,Bool.false_eq_true,↓reduceIte,
    hsf,bind,RunResult.bind,hv]
  rw [normalModes_mode,htf]
  rfl

theorem prepared_success_iff {ambient : Bounds} {source target : Scheme}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    (∃ rank modes fuel result,
      run fuel (SchemePreparation.prepare ambient source target) rank modes = .success result) ↔
    ∃ σ, PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ := by
  constructor
  · rintro ⟨rank,modes,fuel,result,h⟩
    exact ⟨result,run_sound hn hΔ h⟩
  · rintro ⟨σ,hw⟩
    obtain ⟨rank,modes,threshold,result,h⟩ := prepared_complete hn hΔ hw
    exact ⟨rank,modes,threshold,result,h threshold le_rfl⟩

theorem compare_sound {fuel rank modes result ambient source target}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (h : compare fuel ambient source target rank modes = .success result) :
    let p := SchemePreparation.prepare ambient source target
    CompareInstantiatesUnder p.assumptions source result ∧ result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  cases hr : run fuel (SchemePreparation.prepare ambient source target) rank modes with
  | rejected _ => simp [compare,hr,bind,RunResult.bind] at h
  | exhausted => simp [compare,hr,bind,RunResult.bind] at h
  | success action =>
    simp only [compare,hr,bind,RunResult.bind,pure,RunResult.success.injEq] at h
    subst result
    exact ComparisonPreparedDriver.reconstruct_result (run_sound hn hΔ hr)

theorem compare_complete {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    ∃ rank modes threshold result, ∀ fuel ≥ threshold,
      compare fuel ambient source target rank modes = .success result := by
  obtain ⟨rank,modes,threshold,result,h⟩ := prepared_complete hn hΔ hw
  exact ⟨rank,modes,threshold,
    ComparisonPreparation.reconstruct (SchemePreparation.prepare ambient source target) result,
    fun fuel hf => by simp only [compare,h fuel hf,bind,RunResult.bind,pure]⟩

end ModalityInference.ComparisonRankedPrepared
