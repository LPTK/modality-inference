import ModalityInference.ComparisonPreparedScalar
import ModalityInference.Proofs.ComparisonGuardedEndpointQueries
import ModalityInference.Proofs.ComparisonSignedPreparedEndpoints
import ModalityInference.Proofs.ComparisonGuardedTotal
import ModalityInference.Proofs.ComparisonReductionClosure
import ModalityInference.Proofs.SchemeModeWitness

/-! Prepared scalar obligations are checked under their original assumptions.
Finite assembly preserves the common strategy, its quantified domain, and the
definedness certificates needed by every whole endpoint. -/
namespace ModalityInference.ComparisonPreparedScalar
open ComparisonSignedEndpoints

theorem source_binary (theory goals : CNF) : (source theory goals).Binary := by
  intro c hc
  obtain ⟨guard,hg,rfl⟩:=List.mem_map.mp hc
  simp

theorem source_allowed (theory goals : CNF) (keys : List Nat) : (source theory goals).Allowed keys := by
  intro c hc literal hl
  obtain ⟨guard,hg,rfl⟩:=List.mem_map.mp hc
  cases hl

theorem source_valid_iff (theory goals : CNF) (size : Nat → Nat) (shape : Nat → Bool)
    (images : Nat → (Nat → Bool) → Bool) (strategy : (Nat → Bool) → Nat → Bool) :
    (source theory goals).Valid size shape images strategy ↔
      ∀world,CNFHolds (strategy world) theory → CNFHolds (strategy world) goals := by
  simp [ComparisonGuardedEndpointQueries.Source.Valid,
    ComparisonSignedEndpointQueries.Source.Valid,ComparisonSignedStrategySynthesis.Valid,
    source,ClauseHolds,CompiledClause.Holds,ComparisonSignedPoints.raw,
    ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared]
  constructor
  · intro h world ht goal hg
    simpa [ClauseHolds] using h (fun _=>world) goal hg ht
  · intro h world goal hg ht
    simpa [ClauseHolds] using h (world 1) ht goal hg

theorem run_spec {fuel : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run fuel p=.success result) :
    ∃theory goals,CompactCNF.toCNF fuel true (boundsModeFormula p.assumptions)=.success theory ∧
      CompactCNF.toCNF fuel true (boundsModeFormula (required p))=.success goals ∧
      result=source theory goals := by
  cases ht:CompactCNF.toCNF fuel true (boundsModeFormula p.assumptions) <;>
    simp [run,ht,bind,RunResult.bind] at h
  cases hg:CompactCNF.toCNF fuel true (boundsModeFormula (required p)) <;> simp [hg,pure] at h
  exact ⟨_,_,rfl,rfl,h.symm⟩


theorem run_complete (p : SchemePreparation.Prepared) :
    ∃threshold result,∀fuel≥threshold,run fuel p=.success result := by
  obtain ⟨nt,theory,ht⟩:=CompactCNF.toCNF_complete (boundsModeFormula p.assumptions) true
  obtain ⟨ng,goals,hg⟩:=CompactCNF.toCNF_complete (boundsModeFormula (required p)) true
  exact ⟨max nt ng,source theory goals,fun fuel hf=>by
    simp [run,ht fuel (le_trans (le_max_left _ _) hf),
      hg fuel (le_trans (le_max_right _ _) hf),bind,pure,RunResult.bind]⟩

theorem run_stable {n : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run n p=.success result) :
    ∀fuel≥n,run fuel p=.success result := by
  obtain ⟨theory,goals,ht,hg,rfl⟩:=run_spec h
  intro fuel hf
  simp [run,CompactCNF.toCNF_monotone ht fuel hf,CompactCNF.toCNF_monotone hg fuel hf,
    bind,pure,RunResult.bind]

theorem run_binary {fuel : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run fuel p=.success result) :
    result.Binary := by
  obtain ⟨theory,goals,_,_,rfl⟩:=run_spec h
  exact source_binary theory goals

theorem run_allowed {fuel : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run fuel p=.success result) (keys : List Nat) :
    result.Allowed keys := by
  obtain ⟨theory,goals,_,_,rfl⟩:=run_spec h
  exact source_allowed theory goals keys

theorem run_valid {fuel : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run fuel p=.success result)
    (size : Nat → Nat) (shape : Nat → Bool) (images : Nat → (Nat → Bool) → Bool)
    (strategy : (Nat → Bool) → Nat → Bool) :
    result.Valid size shape images strategy ↔
      ∀world,(boundsModeFormula p.assumptions).eval (strategy world)=true →
        (boundsModeFormula (required p)).eval (strategy world)=true := by
  obtain ⟨theory,goals,ht,hg,rfl⟩:=run_spec h
  rw [source_valid_iff]
  exact forall_congr' fun world=>imp_congr (CompactCNF.toCNF_correct ht (strategy world))
    (CompactCNF.toCNF_correct hg (strategy world))


theorem models_strategy {Δ : Bounds} {modes : ModVar → ModExpr}
    (hf : ∀v∈Δ.modVars,modes v=.var v) (world : Nat → Bool) :
    ModeModels Δ (projectedModes (SchemeModeSynthesis.strategy modes world)) ↔
      ModeModels Δ (projectedModes world) := by
  apply ModeModels.congr Δ
  intro v hv
  simp only [projectedModes,SchemeModeSynthesis.strategy_coordinate modes world v 0 (by decide),
    SchemeModeSynthesis.strategy_coordinate modes world v 1 (by decide),
    SchemeModeSynthesis.strategy_coordinate modes world v 2 (by decide),hf v hv,
    SchemeModeSynthesis.coordinate,ModExpr.project,BoolExpr.eval]

theorem models_substituted {Δ goals : Bounds} {modes : ModVar → ModExpr}
    (hm : ComparisonModeRestriction.Fixed Δ modes) (world : Nat → Bool)
    (hw : ModeModels Δ (projectedModes world)) :
    ModeModels goals (projectedModes (SchemeModeSynthesis.strategy modes world)) ↔
      ModeModels (goals.map (Constraint.subst TypeExpr.var modes)) (projectedModes world) := by
  simp only [ModeModels,List.forall_mem_map]
  exact forall_congr' fun c=>imp_congr_right fun _=>
    (ModeSatisfies.subst_functions c TypeExpr.var modes
      (fun v=>SchemeModeSynthesis.strategy_eval modes world v (hm.total _ hw v))).symm

/-- The scalar source checks the original substituted obligations under the
original declared assumptions. Partial symbolic expressions retain their guards. -/
theorem run_valid_substituted {fuel : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run fuel p=.success result)
    (size : Nat → Nat) (shape : Nat → Bool) (images : Nat → (Nat → Bool) → Bool)
    {modes : ModVar → ModExpr} (hm : ComparisonModeRestriction.Fixed p.assumptions modes) :
    result.Valid size shape images (SchemeModeSynthesis.strategy modes) ↔
      ∀η,ModeModels p.assumptions η →
        ModeModels ((required p).map (Constraint.subst TypeExpr.var modes)) η := by
  rw [run_valid h]
  simp only [boundsModeFormula_correct]
  constructor
  · intro hv η hη
    have hw : ModeModels p.assumptions (projectedModes (encodeModes η)) := by
      simpa only [projectedModes_encodeModes] using hη
    have hh := (models_substituted hm (encodeModes η) hw).mp
      (hv (encodeModes η) ((models_strategy hm.fixed (encodeModes η)).mpr hw))
    simpa only [projectedModes_encodeModes] using hh
  · intro hv world hw
    have ho := (models_strategy hm.fixed world).mp hw
    exact (models_substituted hm world ho).mpr (hv _ ho)


theorem required_scalar (p : SchemePreparation.Prepared) {c : Constraint} (hc : c∈required p) :
    ComparisonReduction.Scalar c := by
  rcases List.mem_append.mp hc with hc|hc
  · have hh:=(List.mem_filter.mp hc).2
    cases c <;> simp_all [ComparisonReduction.Scalar]
  · obtain ⟨m,hm,rfl⟩:=List.mem_map.mp hc
    trivial

theorem required_entails_iff (p : SchemePreparation.Prepared) (Δ : Bounds)
    (modes : ModVar → ModExpr) :
    EntailsAll Δ ((required p).map (Constraint.subst TypeExpr.var modes)) ↔
      ∀η,ModeModels Δ η →
        ModeModels ((required p).map (Constraint.subst TypeExpr.var modes)) η := by
  constructor
  · intro h η hη c hc
    obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hc
    have hs:=required_scalar p ho
    have he:=h _ (List.mem_map.mpr ⟨original,ho,rfl⟩)
    cases original <;> try contradiction
    · exact he.denote hη
    · exact he η hη
  · intro h c hc
    obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hc
    have hs:=required_scalar p ho
    have he:=fun η hη=>h η hη _ (List.mem_map.mpr ⟨original,ho,rfl⟩)
    cases original <;> try contradiction
    · exact Submode.valid he
    · exact he

theorem run_valid_entails {fuel : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run fuel p=.success result)
    (size : Nat → Nat) (shape : Nat → Bool) (images : Nat → (Nat → Bool) → Bool)
    {modes : ModVar → ModExpr} (hm : ComparisonModeRestriction.Fixed p.assumptions modes) :
    result.Valid size shape images (SchemeModeSynthesis.strategy modes) ↔
      EntailsAll p.assumptions ((required p).map (Constraint.subst TypeExpr.var modes)) :=
  (run_valid_substituted h size shape images hm).trans (required_entails_iff p _ modes).symm

theorem annotation_mem {p : SchemePreparation.Prepared} {pair : Ty×Ty}
    (hp : pair∈ComparisonSignedObservation.endpoints p) {a : Ty} (ha : a∈[pair.1,pair.2])
    {m : ModExpr} (hm : m∈ComparisonAnnotations.expressions a) : m∈annotations p := by
  apply List.mem_flatMap.mpr
  refine ⟨pair,hp,?_⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl|rfl
  · exact List.mem_append_left _ hm
  · exact List.mem_append_right _ hm

theorem endpoint_guards {p : SchemePreparation.Prepared} {modes : ModVar → ModExpr}
    (h : EntailsAll p.assumptions ((required p).map (Constraint.subst TypeExpr.var modes)))
    {pair : Ty×Ty} (hp : pair∈ComparisonSignedObservation.endpoints p) :
    ∀a∈[pair.1,pair.2],∀m∈ComparisonAnnotations.expressions a,
      Entails p.assumptions (.defined (m.subst modes)) := by
  intro a ha m hm
  exact h _ (List.mem_map.mpr ⟨.defined m,List.mem_append_right _
    (List.mem_map.mpr ⟨m,annotation_mem hp ha hm,rfl⟩),rfl⟩)

theorem run_endpoint_guards {fuel : Nat} {p : SchemePreparation.Prepared}
    {result : ComparisonGuardedEndpointQueries.Source} (h : run fuel p=.success result)
    {size : Nat → Nat} {shape : Nat → Bool} {images : Nat → (Nat → Bool) → Bool}
    {modes : ModVar → ModExpr} (hm : ComparisonModeRestriction.Fixed p.assumptions modes)
    (hv : result.Valid size shape images (SchemeModeSynthesis.strategy modes))
    {pair : Ty×Ty} (hp : pair∈ComparisonSignedObservation.endpoints p) :
    ∀a∈[pair.1,pair.2],∀m∈ComparisonAnnotations.expressions a,
      Entails p.assumptions (.defined (m.subst modes)) :=
  endpoint_guards ((run_valid_entails h size shape images hm).mp hv) hp


@[simp] theorem mem_modeIds (p : SchemePreparation.Prepared) (n : Nat) :
    n∈modeIds p ↔ p.firstMode≤n ∧ n<p.nextMode := by
  simp only [modeIds,List.mem_range',Nat.one_mul]
  constructor
  · rintro ⟨i,hi,rfl⟩
    omega
  · rintro ⟨hl,hu⟩
    exact ⟨n-p.firstMode,by omega,by omega⟩

theorem assemble_domain {p : SchemePreparation.Prepared}
    {images : SymbolicModes.Elimination (flexibleAtoms p)} {action : Substitution}
    (h : assemble p images=some action) :
    action.types=[] ∧ action.modes.map Prod.fst=modeIds p := by
  have hh:=SymbolicSchemeModes.assemble_domain h
  exact ⟨hh.1,by simpa [modeParameters,SchemeModeSynthesis.parameters,List.map_map,Function.comp_def] using hh.2⟩

theorem assemble_fixed {p : SchemePreparation.Prepared}
    {images : SymbolicModes.Elimination (flexibleAtoms p)} {action : Substitution}
    (h : assemble p images=some action) {v : ModVar}
    (hv : ∀n∈modeIds p,v≠.flex n) : action.mode v=.var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    exact SymbolicSchemeModes.assemble_fixed h
      (SchemeModeSynthesis.parameters_lookup_none (fun hn=>hv n hn rfl))

theorem assemble_total {p : SchemePreparation.Prepared}
    {images : SymbolicModes.Elimination (flexibleAtoms p)} {action : Substitution}
    (h : assemble p images=some action) (η : ModVar → Mode) (v : ModVar) :
    (action.mode v).WellFormed η := SymbolicSchemeModes.assemble_wellFormed h η v

/-- Finite assembly preserves the exact common Boolean strategy on every input
world, including all fixed variables outside the quantified mode domain. -/
theorem assemble_strategy {p : SchemePreparation.Prepared}
    {images : SymbolicModes.Elimination (flexibleAtoms p)} {action : Substitution}
    (h : assemble p images=some action) :
    SchemeModeSynthesis.strategy action.mode=
      (fun world v=>(images.substitute v).eval world) := by
  funext world
  have he : projectedModes (SchemeModeSynthesis.strategy action.mode world)=
      projectedModes (fun v=>(images.substitute v).eval world) := by
    funext v
    have ha:=SchemeModeSynthesis.assemble_eval h (projectedModes world) v
    rw [SchemeModeSynthesis.encodeModes_projectedModes] at ha
    exact Option.some.inj
      ((SchemeModeSynthesis.strategy_eval action.mode world v (assemble_total h _ _)).symm.trans ha)
  simpa only [SchemeModeSynthesis.encodeModes_projectedModes] using congrArg encodeModes he

theorem assemble_fixed_context {p : SchemePreparation.Prepared}
    {images : SymbolicModes.Elimination (flexibleAtoms p)} {action : Substitution}
    (h : assemble p images=some action)
    (hscope : ∀v∈p.assumptions.modVars,v.index<p.firstMode) :
    ComparisonModeRestriction.Fixed p.assumptions action.mode := by
  constructor
  · intro η _ v
    exact assemble_total h η v
  · intro v hv
    apply assemble_fixed h
    intro n hn he
    have hlo:=(mem_modeIds p n).mp hn |>.1
    have hhi:=hscope v hv
    subst v
    simp only [ModVar.index] at hhi
    omega

theorem assemble_fixed_prepared {ambient : Bounds} {source target : Scheme}
    {images : SymbolicModes.Elimination (flexibleAtoms (SchemePreparation.prepare ambient source target))}
    {action : Substitution} (h : assemble (SchemePreparation.prepare ambient source target) images=some action) :
    ComparisonModeRestriction.Fixed (SchemePreparation.prepare ambient source target).assumptions action.mode :=
  assemble_fixed_context h
    (Bounds.bounded_iff _ _ _ |>.mp (SchemePreparation.prepare_assumptions_bounded_first ambient source target)).2


theorem modes_assemble (p : SchemePreparation.Prepared) (input : ComparisonSignedSynthesis.Input)
    (sources : List ComparisonGuardedEndpointQueries.Source) (selectors : Nat → Bool) :
    ∃action,assemble p
      (ComparisonGuardedEndpointQueries.modes ModalSynthesis.locality (flexibleAtoms p)
        input sources selectors)=some action :=
  ComparisonGuardedEndpointQueries.modes_assembles (flexibleAtoms p) input sources selectors
    (modeParameters p)

theorem assembled_entails {fuel : Nat} {ambient : Bounds} {source target : Scheme}
    {result : ComparisonGuardedEndpointQueries.Source}
    (h : run fuel (SchemePreparation.prepare ambient source target)=.success result)
    {images : SymbolicModes.Elimination (flexibleAtoms (SchemePreparation.prepare ambient source target))}
    {action : Substitution} (ha : assemble (SchemePreparation.prepare ambient source target) images=some action)
    {size : Nat → Nat} {shape : Nat → Bool} {types : Nat → (Nat → Bool) → Bool}
    (hv : result.Valid size shape types (fun world v=>(images.substitute v).eval world)) :
    EntailsAll (SchemePreparation.prepare ambient source target).assumptions
      ((required (SchemePreparation.prepare ambient source target)).map
        (Constraint.subst TypeExpr.var action.mode)) := by
  apply (run_valid_entails h size shape types (assemble_fixed_prepared ha)).mp
  simpa only [assemble_strategy ha] using hv

theorem prepared_fixed {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (h : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    ComparisonModeRestriction.Fixed (SchemePreparation.prepare ambient source target).assumptions σ.mode := by
  constructor
  · intro η hη v
    exact h.2.1.modes v η hη
  · intro v hv
    exact h.1.1.mode_fixed v
      (((Bounds.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_assumptions_bounded_first ambient source target)).2 v hv)

/-- Every admissible prepared witness satisfies the scalar source, including
the written guards at both endpoints of every whole declared or required edge. -/
theorem prepared_required {source target : Scheme} {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : ComparisonWitnessRestriction.Supported (SchemePreparation.prepare [] source target) σ) :
    EntailsAll (SchemePreparation.prepare [] source target).assumptions
      ((required (SchemePreparation.prepare [] source target)).map (Constraint.subst TypeExpr.var σ.mode)) := by
  let p:=SchemePreparation.prepare [] source target
  intro c hc
  obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hc
  rcases List.mem_append.mp ho with hs|hg
  · have he:=ComparisonGuardedTotal.scalarBounds_entails hw.1.2.2.1
      _ (List.mem_map.mpr ⟨original,hs,rfl⟩)
    have hscalar:=required_scalar p (List.mem_append_left _ hs)
    cases original <;> try contradiction
    · exact he
    · exact he
  · obtain ⟨m,hm,rfl⟩:=List.mem_map.mp hg
    obtain ⟨pair,hp,hm⟩:=List.mem_flatMap.mp hm
    have hpair:=ComparisonSignedObservation.prepared_guarded hw hsp hp
    rcases List.mem_append.mp hm with hl|hr
    · exact ComparisonSignedObservation.annotation_defined hpair.left_defined m hl
    · exact ComparisonSignedObservation.annotation_defined hpair.right_defined m hr

theorem run_prepared_valid {fuel : Nat} {source target : Scheme} {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare [] source target) σ)
    (hsp : ComparisonWitnessRestriction.Supported (SchemePreparation.prepare [] source target) σ)
    {result : ComparisonGuardedEndpointQueries.Source}
    (h : run fuel (SchemePreparation.prepare [] source target)=.success result)
    (size : Nat → Nat) (shape : Nat → Bool) (images : Nat → (Nat → Bool) → Bool) :
    result.Valid size shape images (SchemeModeSynthesis.strategy σ.mode) :=
  (run_valid_entails h size shape images (prepared_fixed hw)).mpr (prepared_required hw hsp)

end ModalityInference.ComparisonPreparedScalar
