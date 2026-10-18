import ModalityInference.ComparisonSignedEndpointQueries
import ModalityInference.Proofs.ComparisonSignedNominalEdges
import ModalityInference.Proofs.ComparisonIndexedWorldClauses
import ModalityInference.Proofs.ComparisonSignedQuerySolver

/-! Endpoint parsing, shared signed-family reconstruction, and scalar synthesis
compose into an executable batch solver. Each query keeps its local observer
coordinates, while every query uses the same image family and mode strategy. -/
namespace ModalityInference.ComparisonSignedEndpointQueries
open ComparisonSignedEndpoints ComparisonWorldClauses ComparisonSignedSynthesis ComparisonSignedQueries

def Source.Allowed (source : Source) (keys : List Nat) : Prop :=
  ∀c∈source.clauses,∀literal∈c.literals,literal.1.name∈keys

def Source.Binary (source : Source) : Prop :=
  ∀c∈source.clauses,c.literals.length≤2

def Source.Valid (source : Source) (size : Nat → Nat)
    (images : Nat → (Nat → Bool) → Bool) (strategy : (Nat → Bool) → Nat → Bool) : Prop :=
  ComparisonSignedStrategySynthesis.Valid size source.decode source.theory source.clauses images strategy

theorem Source.nominal_complete (source : Source) (offset : Nat) (size : Nat → Nat) :
    ∃q,source.nominal offset size=some q := by
  obtain ⟨clauses,hc,_⟩:=ComparisonSignedNominalEdges.prepare_complete offset size
    source.decode source.theory source.clauses
  let q : Query := {
    payload := ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls source.clauses)
    decode := ComparisonSignedNominal.guardDecode
    theory := []
    clauses := clauses }
  exact ⟨q,by simp [Source.nominal,hc,q]⟩

theorem Source.nominal_spec {source : Source} {offset : Nat} {size : Nat → Nat} {q : Query}
    (h : source.nominal offset size=some q) :
    ∃clauses,ComparisonSignedNominalEdges.prepare offset size source.decode source.theory source.clauses=
      some clauses ∧ q={
        payload:=ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls source.clauses)
        decode:=ComparisonSignedNominal.guardDecode
        theory:=[]
        clauses:=clauses} := by
  cases hc:ComparisonSignedNominalEdges.prepare offset size source.decode source.theory source.clauses
    <;> simp [Source.nominal,hc] at h
  exact ⟨_,rfl,h.symm⟩

theorem Source.nominal_allowed {source : Source} {offset : Nat} {size : Nat → Nat} {q : Query}
    (h : source.nominal offset size=some q) {keys : List Nat} (ha : source.Allowed keys) :
    q.Allowed keys := by
  obtain ⟨clauses,hc,rfl⟩:=Source.nominal_spec h
  intro c hcm literal hl
  obtain ⟨original,ho,he⟩:=ComparisonSignedNominalEdges.prepare_origin hc hcm
  exact ha original ho literal (he ▸ hl)

theorem Source.nominal_binary {source : Source} {offset : Nat} {size : Nat → Nat} {q : Query}
    (h : source.nominal offset size=some q) (hb : source.Binary) :
    ∀c∈q.clauses,c.literals.length≤2 := by
  obtain ⟨clauses,hc,rfl⟩:=Source.nominal_spec h
  intro c hcm
  obtain ⟨original,ho,he⟩:=ComparisonSignedNominalEdges.prepare_origin hc hcm
  rw [he]
  exact hb original ho

theorem Source.nominal_valid {source : Source} {offset : Nat} {input : Input} {q : Query}
    (h : source.nominal offset (fun n=>(input.bases n).length)=some q)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    (ha : source.Allowed input.keys) (selectors : Nat → Bool) :
    q.Valid selectors images ↔ ∀world,CNFHolds
      (selectedValue (ComparisonWorldModes.worldChoice selectors)
        (ComparisonSignedStrategySynthesis.nominalValue (fun n=>(input.bases n).length)
          source.clauses images world))
      (ComparisonWorldOffsets.nominal offset (source.worlds (fun n=>(input.bases n).length))) := by
  obtain ⟨clauses,hc,rfl⟩:=Source.nominal_spec h
  have hallowed:=Source.nominal_allowed h ha
  have hi (world : Nat → Bool) :
      (∀c∈clauses,c.Holds
        (ComparisonSignedEdges.decoded ComparisonSignedNominal.guardDecode selectors world)
        (fun call=>images call.name (fun i=>
          ComparisonSignedEdges.decoded ComparisonSignedNominal.guardDecode selectors world
            (ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls source.clauses) call i)))) ↔
      CNFHolds
        (selectedValue (ComparisonWorldModes.worldChoice selectors)
          (ComparisonSignedStrategySynthesis.nominalValue (fun n=>(input.bases n).length)
            source.clauses images world))
        (ComparisonWorldOffsets.nominal offset
          (ComparisonSignedStrategySynthesis.worlds (fun n=>(input.bases n).length)
            source.decode source.theory source.clauses)) := by
    rw [ComparisonSignedNominalEdges.prepare_correct hc selectors world images]
    apply forall_congr' fun c=>imp_congr_right fun hcm=>?_
    rw [←ComparisonSignedNominal.guardDecode_value]
    apply ComparisonSignedPoints.images_congr
    intro literal hl
    apply hf.congr (hallowed c hcm literal hl)
    intro i hi
    simp only [ComparisonSignedNominal.payload_value,ComparisonSignedPoints.nominalPoint,if_pos hi]
  constructor
  · intro h world
    exact (hi world).mp (h world (by simp [CNFHolds]))
  · intro h world _
    exact (hi world).mpr (h world)


theorem prepare_complete (size : Nat → Nat) (offset : Nat) (sources : List Source) :
    ∃queries,prepare size offset sources=some queries := by
  induction sources generalizing offset with
  | nil => exact ⟨[],rfl⟩
  | cons source sources ih =>
    obtain ⟨head,hh⟩:=source.nominal_complete offset size
    obtain ⟨tail,ht⟩:=ih (offset+(source.worlds size).length)
    exact ⟨head::tail,by simp [prepare,hh,ht]⟩

theorem prepare_cons {size : Nat → Nat} {offset : Nat} {source : Source}
    {sources : List Source} {queries : List Query}
    (h : prepare size offset (source::sources)=some queries) :
    ∃head tail,source.nominal offset size=some head ∧
      prepare size (offset+(source.worlds size).length) sources=some tail ∧ queries=head::tail := by
  cases hh:source.nominal offset size <;> simp only [prepare,hh,Option.bind_eq_bind] at h
  · simp at h
  cases ht:prepare size (offset+(source.worlds size).length) sources <;> simp [ht] at h
  exact ⟨_,_,rfl,rfl,h.symm⟩

theorem prepare_allowed {size : Nat → Nat} {offset : Nat} {sources : List Source} {queries : List Query}
    (h : prepare size offset sources=some queries) {keys : List Nat}
    (ha : ∀source∈sources,source.Allowed keys) : ∀q∈queries,q.Allowed keys := by
  induction sources generalizing offset queries with
  | nil => simp [prepare] at h; subst queries; simp
  | cons source sources ih =>
    obtain ⟨head,tail,hh,ht,rfl⟩:=prepare_cons h
    exact List.forall_mem_cons.mpr ⟨Source.nominal_allowed hh (ha source List.mem_cons_self),
      ih ht (fun s hs=>ha s (List.mem_cons_of_mem _ hs))⟩

theorem prepare_binary {size : Nat → Nat} {offset : Nat} {sources : List Source} {queries : List Query}
    (h : prepare size offset sources=some queries)
    (hb : ∀source∈sources,source.Binary) : ∀q∈queries,∀c∈q.clauses,c.literals.length≤2 := by
  induction sources generalizing offset queries with
  | nil => simp [prepare] at h; subst queries; simp
  | cons source sources ih =>
    obtain ⟨head,tail,hh,ht,rfl⟩:=prepare_cons h
    exact List.forall_mem_cons.mpr ⟨Source.nominal_binary hh (hb source List.mem_cons_self),
      ih ht (fun s hs=>hb s (List.mem_cons_of_mem _ hs))⟩

def entries (size : Nat → Nat) (images : Nat → (Nat → Bool) → Bool)
    (sources : List Source) : List ComparisonIndexedWorldClauses.Entry :=
  sources.map fun source=>(ComparisonSignedStrategySynthesis.nominalValue size source.clauses images,
    source.worlds size)

theorem entries_worlds (size : Nat → Nat) (images : Nat → (Nat → Bool) → Bool)
    (sources : List Source) : (entries size images sources).flatMap Prod.snd=worlds size sources := by
  simp [entries,worlds,List.flatMap_map]

theorem prepare_valid_iff {input : Input} {offset : Nat} {sources : List Source} {queries : List Query}
    (h : prepare (fun n=>(input.bases n).length) offset sources=some queries)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    (ha : ∀source∈sources,source.Allowed input.keys) (selectors : Nat → Bool) :
    (∀q∈queries,q.Valid selectors images) ↔
      ComparisonIndexedWorldClauses.BatchNominalHolds offset
        (entries (fun n=>(input.bases n).length) images sources)
        (ComparisonWorldModes.worldChoice selectors) := by
  induction sources generalizing offset queries with
  | nil =>
    simp [prepare] at h
    subst queries
    simp [entries,ComparisonIndexedWorldClauses.BatchNominalHolds]
  | cons source sources ih =>
    obtain ⟨head,tail,hh,ht,rfl⟩:=prepare_cons h
    simp only [List.forall_mem_cons,entries,List.map_cons,ComparisonIndexedWorldClauses.BatchNominalHolds]
    exact and_congr (Source.nominal_valid hh hf (ha source List.mem_cons_self) selectors)
      (ih ht (fun s hs=>ha s (List.mem_cons_of_mem _ hs)))

theorem entries_valid (size : Nat → Nat) (images : Nat → (Nat → Bool) → Bool)
    (sources : List Source) (strategy : (Nat → Bool) → Nat → Bool) :
    (∀entry∈entries size images sources,
      ComparisonWorldClauses.Valid entry.1 strategy entry.2) ↔
      ∀source∈sources,source.Valid size images strategy := by
  simp only [entries,List.forall_mem_map]
  exact forall_congr' fun source=>imp_congr_right fun _=>
    ComparisonSignedStrategySynthesis.worlds_correct size source.decode source.theory source.clauses
      images strategy

/-- Every local graph uses the same image family, and the single scalar query
synthesizes one strategy for every route in every endpoint query. -/
theorem strategy_iff {input : Input} {sources : List Source} {queries : List Query}
    (h : prepare (fun n=>(input.bases n).length) 0 sources=some queries)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    (ha : ∀source∈sources,source.Allowed input.keys) (side : Nat → Bool) (flex : List Nat) :
    (∃selectors,CNFHolds selectors
        (scalarQuery side flex (fun n=>(input.bases n).length) sources) ∧
      ∀q∈queries,q.Valid selectors images) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        ∀source∈sources,source.Valid (fun n=>(input.bases n).length) images strategy := by
  have he:=ComparisonIndexedWorldClauses.batch_query_iff side flex
    (entries (fun n=>(input.bases n).length) images sources)
  rw [entries_worlds] at he
  simp only [entries_valid] at he
  rw [←he]
  apply exists_congr
  intro selectors
  exact and_congr_right (fun _=>prepare_valid_iff h hf ha selectors)

/-- Joint symbolic graph consistency and the common scalar condition are
exactly the existence of one positive image family and one uniform strategy. -/
theorem feasible_iff {input : Input} {sources : List Source} {queries : List Query} {r : CNF}
    (hp : prepare (fun n=>(input.bases n).length) 0 sources=some queries)
    (hc : ComparisonSignedQueries.compile input queries=some r)
    (ha : ∀source∈sources,source.Allowed input.keys) (side : Nat → Bool) (flex : List Nat) :
    (∃selectors,CNFHolds selectors
        (scalarQuery side flex (fun n=>(input.bases n).length) sources) ∧
      ComparisonSignedRelations.Holds selectors (input.consistent r) (fun _=>false) (fun _=>false)) ↔
      ∃images,Family input images ∧ ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        ∀source∈sources,source.Valid (fun n=>(input.bases n).length) images strategy := by
  have hallowed:=prepare_allowed hp ha
  constructor
  · rintro ⟨selectors,hs,hc'⟩
    obtain ⟨images,hf,hv⟩:=(ComparisonSignedQueries.consistent_iff hc hallowed selectors).mp hc'
    exact ⟨images,hf,(strategy_iff hp hf ha side flex).mp ⟨selectors,hs,hv⟩⟩
  · rintro ⟨images,hf,strategy,hu,hv⟩
    obtain ⟨selectors,hs,hv⟩:=(strategy_iff hp hf ha side flex).mpr ⟨strategy,hu,hv⟩
    exact ⟨selectors,hs,(ComparisonSignedQueries.consistent_iff hc hallowed selectors).mpr
      ⟨images,hf,hv⟩⟩


theorem modes_uniform (side : Nat → Bool) (flex : List Nat) (input : Input)
    (sources : List Source) (selectors : Nat → Bool) :
    ModalSynthesis.Uniform side flex (fun world v=>
      ((modes side flex input sources selectors).substitute v).eval world) :=
  ComparisonWorldModes.witness_uniform side flex _ selectors

theorem modes_sound {input : Input} {sources : List Source} {queries : List Query}
    (hp : prepare (fun n=>(input.bases n).length) 0 sources=some queries)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    (ha : ∀source∈sources,source.Allowed input.keys) {side : Nat → Bool} {flex : List Nat}
    {selectors : Nat → Bool}
    (hs : CNFHolds selectors (scalarQuery side flex (fun n=>(input.bases n).length) sources))
    (hv : ∀q∈queries,q.Valid selectors images) :
    ∀source∈sources,source.Valid (fun n=>(input.bases n).length) images (fun world v=>
      ((modes side flex input sources selectors).substitute v).eval world) := by
  let es:=entries (fun n=>(input.bases n).length) images sources
  have hscalar : CNFHolds selectors (ComparisonWorldModes.query side flex (es.flatMap Prod.snd)) := by
    simpa only [es,entries_worlds] using hs
  have hn := (prepare_valid_iff hp hf ha selectors).mp hv
  have hn' := (ComparisonIndexedWorldClauses.batch_nominal es 0
    (ComparisonWorldModes.worldChoice selectors)).mpr hn
  simp only [ComparisonIndexedWorldClauses.shiftChoice_zero] at hn'
  have hvalid:=ComparisonIndexedWorldClauses.selectors_sound
    ⟨(ComparisonWorldModes.query_parts side flex _ selectors |>.mp hscalar).1,
      hn',ComparisonWorldModes.witness_sound hscalar⟩
  have hb := (ComparisonIndexedWorldClauses.batch_valid es _).mp hvalid
  have he : (fun world v=>
      ((ComparisonWorldModes.witness side flex (es.flatMap Prod.snd) selectors).substitute v).eval world)=
      (fun world v=>((modes side flex input sources selectors).substitute v).eval world) := by
    simp only [es,entries_worlds,modes]
  rw [he] at hb
  exact (entries_valid _ _ _ _).mp hb

theorem modes_assembles (flex : List Nat) (input : Input) (sources : List Source)
    (selectors : Nat → Bool) (parameters : List (Nat × ModVar)) :
    ∃action,SymbolicSchemeModes.assemble
      (modes ModalSynthesis.locality flex input sources selectors) parameters=some action :=
  ComparisonWorldModes.witness_assembles _ selectors parameters

/-- Successful execution returns one finite type-image list with the requested
keys. Its actual canonical image interpretation and reconstructed modality
strategy satisfy every original guarded endpoint query. -/
theorem run_sound {fuel : Nat} {input : Input} {side : Nat → Bool} {flex : List Nat}
    {sources : List Source} {result : ComparisonSignedQuerySolver.Solution}
    (ha : ∀source∈sources,source.Allowed input.keys)
    (h : run fuel input side flex sources=.success result) :
    ∃queries r,prepare (fun n=>(input.bases n).length) 0 sources=some queries ∧
      ComparisonSignedQueries.compile input queries=some r ∧
      input.reconstruct r (CNFPropagation.valuation result.selectors)=some result.images ∧
      result.images.map Prod.fst=input.keys ∧
      Family input (input.imageValue r (CNFPropagation.valuation result.selectors)) ∧
      ∀source∈sources,source.Valid (fun n=>(input.bases n).length)
        (input.imageValue r (CNFPropagation.valuation result.selectors)) (fun world v=>
          ((modes side flex input sources (CNFPropagation.valuation result.selectors)).substitute v).eval world) := by
  obtain ⟨queries,hp⟩:=prepare_complete (fun n=>(input.bases n).length) 0 sources
  have hr : ComparisonSignedQuerySolver.run fuel input queries
      (scalarQuery side flex (fun n=>(input.bases n).length) sources)=.success result := by
    simpa only [run,hp] using h
  obtain ⟨r,hc,hi,hs,hkeys,hf,hv⟩:=ComparisonSignedQuerySolver.run_sound (prepare_allowed hp ha) hr
  exact ⟨queries,r,hp,hc,hi,hkeys,hf,modes_sound hp hf ha hs hv⟩

theorem run_complete_stable (input : Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) (hb : ∀source∈sources,source.Binary)
    (ha : ∀source∈sources,source.Allowed input.keys)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    {strategy : (Nat → Bool) → Nat → Bool} (hu : ModalSynthesis.Uniform side flex strategy)
    (hv : ∀source∈sources,source.Valid (fun n=>(input.bases n).length) images strategy) :
    ∃threshold result,∀fuel≥threshold,run fuel input side flex sources=.success result := by
  obtain ⟨queries,hp⟩:=prepare_complete (fun n=>(input.bases n).length) 0 sources
  obtain ⟨selectors,hs,hv⟩:=(strategy_iff hp hf ha side flex).mpr ⟨strategy,hu,hv⟩
  obtain ⟨threshold,result,hr⟩:=ComparisonSignedQuerySolver.run_complete_stable input queries
    (scalarQuery side flex (fun n=>(input.bases n).length) sources)
    (prepare_binary hp hb) (prepare_allowed hp ha) hf hv hs
  exact ⟨threshold,result,fun fuel hfu=>by simpa only [run,hp] using hr fuel hfu⟩

theorem run_success_iff (input : Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) (hb : ∀source∈sources,source.Binary)
    (ha : ∀source∈sources,source.Allowed input.keys) :
    (∃fuel result,run fuel input side flex sources=.success result) ↔
      ∃images,Family input images ∧ ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        ∀source∈sources,source.Valid (fun n=>(input.bases n).length) images strategy := by
  constructor
  · rintro ⟨fuel,result,hr⟩
    obtain ⟨queries,r,_,_,_,_,hf,hv⟩:=run_sound ha hr
    exact ⟨_,hf,_,modes_uniform side flex input sources _,hv⟩
  · rintro ⟨images,hf,strategy,hu,hv⟩
    obtain ⟨threshold,result,hr⟩:=run_complete_stable input side flex sources hb ha hf hu hv
    exact ⟨threshold,result,hr threshold le_rfl⟩

theorem run_terminates (input : Input) (side : Nat → Bool) (flex : List Nat) (sources : List Source) :
    ∃threshold,∀fuel≥threshold,run fuel input side flex sources≠.exhausted := by
  obtain ⟨queries,hp⟩:=prepare_complete (fun n=>(input.bases n).length) 0 sources
  simpa only [run,hp] using ComparisonSignedQuerySolver.run_terminates input queries
    (scalarQuery side flex (fun n=>(input.bases n).length) sources)

theorem run_stable {n : Nat} {input : Input} {side : Nat → Bool} {flex : List Nat}
    {sources : List Source} {result : RunResult ComparisonSignedQuerySolver.Solution}
    (hne : result≠.exhausted) (h : run n input side flex sources=result) :
    ∀fuel≥n,run fuel input side flex sources=result := by
  obtain ⟨queries,hp⟩:=prepare_complete (fun n=>(input.bases n).length) 0 sources
  have hr : ComparisonSignedQuerySolver.run n input queries
      (scalarQuery side flex (fun n=>(input.bases n).length) sources)=result := by
    simpa only [run,hp] using h
  simpa only [run,hp] using ComparisonSignedQuerySolver.run_stable hne hr

end ModalityInference.ComparisonSignedEndpointQueries
