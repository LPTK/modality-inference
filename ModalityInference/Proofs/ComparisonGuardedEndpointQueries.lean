import ModalityInference.ComparisonGuardedEndpointQueries
import ModalityInference.Proofs.ComparisonGuardedWorldBatch
import ModalityInference.Proofs.ComparisonSignedEndpointQueries

/-! Symbolic shape activation, nominal graph consistency, and scalar synthesis
compose into one executable endpoint solver. Every active query shares the same
finite image family and reconstructed modality strategy. -/
namespace ModalityInference.ComparisonGuardedEndpointQueries
open ComparisonSignedEndpoints ComparisonSignedSynthesis ComparisonSignedQueries ComparisonWorldClauses

abbrev Source.Allowed (source : Source) (keys : List Nat) := source.source.Allowed keys
abbrev Source.Binary (source : Source) := source.source.Binary

def Source.Valid (source : Source) (size : Nat → Nat) (shape : Nat → Bool)
    (images : Nat → (Nat → Bool) → Bool) (strategy : (Nat → Bool) → Nat → Bool) : Prop :=
  ¬ClauseHolds shape source.guard → source.source.Valid size images strategy

theorem prefix_correct (total : Nat) (guard : Clause) (selectors world : Nat → Bool) :
    ClauseHolds (ComparisonSignedEdges.decoded ComparisonSignedNominal.guardDecode selectors world)
      (guardPrefix total guard) ↔
      ClauseHolds (ComparisonGuardedWorldModes.externalValue total selectors) guard := by
  have hv (v : Nat) : ComparisonSignedEdges.decoded ComparisonSignedNominal.guardDecode selectors world
      (2*ComparisonGuardedWorldModes.externalAtom total v+1)=
      ComparisonGuardedWorldModes.externalValue total selectors v := by
    rw [ComparisonSignedNominal.guardDecode_value]
    simp [ComparisonSignedNominal.guardValue,ComparisonGuardedWorldModes.externalValue,
      show (2*ComparisonGuardedWorldModes.externalAtom total v+1)/2=
        ComparisonGuardedWorldModes.externalAtom total v by omega]
  constructor
  · rintro ⟨v,p,hv',hp⟩
    obtain ⟨⟨u,q⟩,hu,he⟩:=List.mem_map.mp hv'
    cases he
    exact ⟨u,q,hu,(hv u).symm.trans hp⟩
  · rintro ⟨v,p,hv',hp⟩
    exact ⟨_,p,List.mem_map.mpr ⟨(v,p),hv',rfl⟩,(hv v).trans hp⟩

theorem gate_valid (total : Nat) (guard : Clause) (q : Query)
    (hd : q.decode=ComparisonSignedNominal.guardDecode)
    (selectors : Nat → Bool) (images : Nat → (Nat → Bool) → Bool) :
    (gate total guard q).Valid selectors images ↔
      (¬ClauseHolds (ComparisonGuardedWorldModes.externalValue total selectors) guard →
        q.Valid selectors images) := by
  classical
  have hc (world : Nat → Bool) (c : CompiledClause) :
      ({c with guard:=guardPrefix total guard++c.guard}).Holds
        (ComparisonSignedEdges.decoded q.decode selectors world)
        (fun call=>images call.name (fun i=>
          ComparisonSignedEdges.decoded q.decode selectors world (q.payload call i))) ↔
      ClauseHolds (ComparisonGuardedWorldModes.externalValue total selectors) guard ∨
        c.Holds (ComparisonSignedEdges.decoded q.decode selectors world)
          (fun call=>images call.name (fun i=>
            ComparisonSignedEdges.decoded q.decode selectors world (q.payload call i))) := by
    simp only [CompiledClause.Holds,clauseHolds_append,hd,prefix_correct,or_assoc]
  unfold Query.Valid
  simp only [gate,List.forall_mem_map,hc]
  constructor
  · intro h hg world hw c hcm
    exact (h world hw c hcm).resolve_left hg
  · intro h world hw c hcm
    by_cases hg:ClauseHolds (ComparisonGuardedWorldModes.externalValue total selectors) guard
    · exact .inl hg
    · exact .inr (h hg world hw c hcm)

theorem gate_allowed (total : Nat) (guard : Clause) {q : Query} {keys : List Nat}
    (h : q.Allowed keys) : (gate total guard q).Allowed keys := by
  intro c hc literal hl
  obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hc
  exact h original ho literal hl

theorem gate_binary (total : Nat) (guard : Clause) {q : Query}
    (h : ∀c∈q.clauses,c.literals.length≤2) : ∀c∈(gate total guard q).clauses,c.literals.length≤2 := by
  intro c hc
  obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hc
  exact h original ho

theorem Source.nominal_complete (source : Source) (total offset : Nat) (size : Nat → Nat) :
    ∃q,source.nominal total offset size=some q := by
  obtain ⟨q,hq⟩:=source.source.nominal_complete offset size
  exact ⟨gate total source.guard q,by simp [Source.nominal,hq]⟩

theorem Source.nominal_spec {source : Source} {total offset : Nat} {size : Nat → Nat} {q : Query}
    (h : source.nominal total offset size=some q) :
    ∃original,source.source.nominal offset size=some original ∧ q=gate total source.guard original := by
  cases hc:source.source.nominal offset size <;> simp [Source.nominal,hc] at h
  exact ⟨_,rfl,h.symm⟩

theorem Source.nominal_allowed {source : Source} {total offset : Nat} {size : Nat → Nat} {q : Query}
    (h : source.nominal total offset size=some q) {keys : List Nat} (ha : source.Allowed keys) :
    q.Allowed keys := by
  obtain ⟨original,ho,rfl⟩:=Source.nominal_spec h
  exact gate_allowed total source.guard (ComparisonSignedEndpointQueries.Source.nominal_allowed ho ha)

theorem Source.nominal_binary {source : Source} {total offset : Nat} {size : Nat → Nat} {q : Query}
    (h : source.nominal total offset size=some q) (hb : source.Binary) :
    ∀c∈q.clauses,c.literals.length≤2 := by
  obtain ⟨original,ho,rfl⟩:=Source.nominal_spec h
  exact gate_binary total source.guard (ComparisonSignedEndpointQueries.Source.nominal_binary ho hb)

theorem Source.nominal_valid {source : Source} {total offset : Nat} {input : Input} {q : Query}
    (h : source.nominal total offset (fun n=>(input.bases n).length)=some q)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    (ha : source.Allowed input.keys) (selectors : Nat → Bool) :
    q.Valid selectors images ↔
      (¬ClauseHolds (ComparisonGuardedWorldModes.externalValue total selectors) source.guard →
        ∀world,CNFHolds
          (selectedValue (ComparisonWorldModes.worldChoice selectors)
            (ComparisonSignedStrategySynthesis.nominalValue (fun n=>(input.bases n).length)
              source.source.clauses images world))
          (ComparisonWorldOffsets.nominal offset
            (source.source.worlds (fun n=>(input.bases n).length)))) := by
  obtain ⟨original,ho,rfl⟩:=Source.nominal_spec h
  have hd : original.decode=ComparisonSignedNominal.guardDecode := by
    obtain ⟨_,_,rfl⟩:=ComparisonSignedEndpointQueries.Source.nominal_spec ho
    rfl
  exact (gate_valid total source.guard original hd selectors images).trans
    (imp_congr_right fun _=>ComparisonSignedEndpointQueries.Source.nominal_valid ho hf ha selectors)


theorem prepare_complete (total : Nat) (size : Nat → Nat) (offset : Nat) (sources : List Source) :
    ∃queries,prepare total size offset sources=some queries := by
  induction sources generalizing offset with
  | nil => exact ⟨[],rfl⟩
  | cons source sources ih =>
    obtain ⟨head,hh⟩:=source.nominal_complete total offset size
    obtain ⟨tail,ht⟩:=ih (offset+(source.source.worlds size).length)
    exact ⟨head::tail,by simp [prepare,hh,ht]⟩

theorem prepare_cons {total : Nat} {size : Nat → Nat} {offset : Nat} {source : Source}
    {sources : List Source} {queries : List Query}
    (h : prepare total size offset (source::sources)=some queries) :
    ∃head tail,source.nominal total offset size=some head ∧
      prepare total size (offset+(source.source.worlds size).length) sources=some tail ∧
      queries=head::tail := by
  cases hh:source.nominal total offset size <;> simp only [prepare,hh,Option.bind_eq_bind] at h
  · simp at h
  cases ht:prepare total size (offset+(source.source.worlds size).length) sources <;> simp [ht] at h
  exact ⟨_,_,rfl,rfl,h.symm⟩

theorem prepare_allowed {total : Nat} {size : Nat → Nat} {offset : Nat}
    {sources : List Source} {queries : List Query}
    (h : prepare total size offset sources=some queries) {keys : List Nat}
    (ha : ∀source∈sources,source.Allowed keys) : ∀q∈queries,q.Allowed keys := by
  induction sources generalizing offset queries with
  | nil => simp [prepare] at h; subst queries; simp
  | cons source sources ih =>
    obtain ⟨head,tail,hh,ht,rfl⟩:=prepare_cons h
    exact List.forall_mem_cons.mpr ⟨Source.nominal_allowed hh (ha source List.mem_cons_self),
      ih ht (fun s hs=>ha s (List.mem_cons_of_mem _ hs))⟩

theorem prepare_binary {total : Nat} {size : Nat → Nat} {offset : Nat}
    {sources : List Source} {queries : List Query}
    (h : prepare total size offset sources=some queries)
    (hb : ∀source∈sources,source.Binary) : ∀q∈queries,∀c∈q.clauses,c.literals.length≤2 := by
  induction sources generalizing offset queries with
  | nil => simp [prepare] at h; subst queries; simp
  | cons source sources ih =>
    obtain ⟨head,tail,hh,ht,rfl⟩:=prepare_cons h
    exact List.forall_mem_cons.mpr ⟨Source.nominal_binary hh (hb source List.mem_cons_self),
      ih ht (fun s hs=>hb s (List.mem_cons_of_mem _ hs))⟩


def groups (size : Nat → Nat) (images : Nat → (Nat → Bool) → Bool)
    (sources : List Source) : List ComparisonGuardedWorldModes.Group :=
  sources.map fun source=>{
    guard:=source.guard
    nominal:=ComparisonSignedStrategySynthesis.nominalValue size source.source.clauses images
    clauses:=source.source.worlds size }

theorem groups_batch (size : Nat → Nat) (images : Nat → (Nat → Bool) → Bool)
    (sources : List Source) :
    ComparisonGuardedWorldModes.batch (groups size images sources)=entries size sources := by
  simp [groups,ComparisonGuardedWorldModes.batch,ComparisonGuardedWorldModes.guarded,
    entries,Source.entries,List.flatMap_map]

theorem groups_valid (size : Nat → Nat) (images : Nat → (Nat → Bool) → Bool)
    (sources : List Source) (shape : Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool) :
    (∀group∈groups size images sources,¬ClauseHolds shape group.guard →
      ComparisonWorldClauses.Valid group.nominal strategy group.clauses) ↔
      ∀source∈sources,source.Valid size shape images strategy := by
  simp only [groups,List.forall_mem_map,Source.Valid]
  exact forall_congr' fun source=>imp_congr_right fun _=>imp_congr_right fun _=>
    ComparisonSignedStrategySynthesis.worlds_correct size source.source.decode source.source.theory
      source.source.clauses images strategy

theorem prepare_valid_iff {input : Input} {total offset : Nat}
    {sources : List Source} {queries : List Query}
    (h : prepare total (fun n=>(input.bases n).length) offset sources=some queries)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    (ha : ∀source∈sources,source.Allowed input.keys) (selectors : Nat → Bool) :
    (∀q∈queries,q.Valid selectors images) ↔
      ComparisonGuardedWorldModes.BatchNominalHolds offset
        (groups (fun n=>(input.bases n).length) images sources)
        (ComparisonGuardedWorldModes.externalValue total selectors)
        (ComparisonWorldModes.worldChoice selectors) := by
  induction sources generalizing offset queries with
  | nil =>
    simp [prepare] at h
    subst queries
    simp [groups,ComparisonGuardedWorldModes.BatchNominalHolds]
  | cons source sources ih =>
    obtain ⟨head,tail,hh,ht,rfl⟩:=prepare_cons h
    simp only [List.forall_mem_cons,groups,List.map_cons,ComparisonGuardedWorldModes.BatchNominalHolds]
    exact and_congr (Source.nominal_valid hh hf (ha source List.mem_cons_self) selectors)
      (ih ht (fun s hs=>ha s (List.mem_cons_of_mem _ hs)))


theorem scalarQuery_parts (side : Nat → Bool) (flex : List Nat) (size : Nat → Nat)
    (sources : List Source) (shapeCondition : CNF) (selectors : Nat → Bool) :
    CNFHolds selectors (scalarQuery side flex size sources shapeCondition) ↔
      CNFHolds (shapeValue size sources selectors) shapeCondition ∧
        CNFHolds selectors (ComparisonGuardedWorldModes.query side flex (entries size sources)) := by
  rw [scalarQuery,cnfHolds_append,ComparisonPropagation.rename_correct]
  rfl

/-- A chosen shape valuation activates entire endpoint queries. The image
family and modality strategy remain shared across all active alternatives. -/
theorem strategy_iff {input : Input} {sources : List Source} {queries : List Query}
    (h : prepare (entries (fun n=>(input.bases n).length) sources).length
      (fun n=>(input.bases n).length) 0 sources=some queries)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    (ha : ∀source∈sources,source.Allowed input.keys)
    (side : Nat → Bool) (flex : List Nat) (shape : Nat → Bool) :
    (∃selectors,shapeValue (fun n=>(input.bases n).length) sources selectors=shape ∧
      CNFHolds selectors (ComparisonGuardedWorldModes.query side flex
        (entries (fun n=>(input.bases n).length) sources)) ∧
      ∀q∈queries,q.Valid selectors images) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        ∀source∈sources,source.Valid (fun n=>(input.bases n).length) shape images strategy := by
  have he:=ComparisonGuardedWorldModes.batch_query_iff side flex
    (groups (fun n=>(input.bases n).length) images sources) shape
  rw [groups_batch] at he
  simp only [groups_valid] at he
  rw [←he]
  apply exists_congr
  intro selectors
  apply and_congr_right
  intro hshape
  apply and_congr_right
  intro _
  have hh:=prepare_valid_iff h hf ha selectors
  change ComparisonGuardedWorldModes.externalValue _ selectors=shape at hshape
  rw [hshape] at hh
  exact hh


/-- The finite shape condition, every activated nominal graph, and all scalar
blocks are solved by one shared constant valuation and one shared strategy. -/
theorem feasible_iff {input : Input} {sources : List Source} {queries : List Query} {r : CNF}
    (hp : prepare (entries (fun n=>(input.bases n).length) sources).length
      (fun n=>(input.bases n).length) 0 sources=some queries)
    (hc : ComparisonSignedQueries.compile input queries=some r)
    (ha : ∀source∈sources,source.Allowed input.keys)
    (side : Nat → Bool) (flex : List Nat) (shapeCondition : CNF) :
    (∃selectors,CNFHolds selectors
        (scalarQuery side flex (fun n=>(input.bases n).length) sources shapeCondition) ∧
      ComparisonSignedRelations.Holds selectors (input.consistent r) (fun _=>false) (fun _=>false)) ↔
      ∃shape,CNFHolds shape shapeCondition ∧ ∃images,Family input images ∧
        ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
          ∀source∈sources,source.Valid (fun n=>(input.bases n).length) shape images strategy := by
  have hallowed:=prepare_allowed hp ha
  constructor
  · rintro ⟨selectors,hs,hc'⟩
    obtain ⟨hshape,hquery⟩:=(scalarQuery_parts side flex _ sources shapeCondition selectors).mp hs
    obtain ⟨images,hf,hv⟩:=(ComparisonSignedQueries.consistent_iff hc hallowed selectors).mp hc'
    exact ⟨_,hshape,images,hf,(strategy_iff hp hf ha side flex _).mp ⟨selectors,rfl,hquery,hv⟩⟩
  · rintro ⟨shape,hshape,images,hf,strategy,hu,hv⟩
    obtain ⟨selectors,he,hquery,hv⟩:=(strategy_iff hp hf ha side flex shape).mpr ⟨strategy,hu,hv⟩
    refine ⟨selectors,(scalarQuery_parts side flex _ sources shapeCondition selectors).mpr
      ⟨?_,hquery⟩,(ComparisonSignedQueries.consistent_iff hc hallowed selectors).mpr ⟨images,hf,hv⟩⟩
    simpa only [he] using hshape

theorem modes_uniform (side : Nat → Bool) (flex : List Nat) (input : Input)
    (sources : List Source) (selectors : Nat → Bool) :
    ModalSynthesis.Uniform side flex (fun world v=>
      ((modes side flex input sources selectors).substitute v).eval world) :=
  ComparisonGuardedWorldModes.witness_uniform side flex _ selectors

theorem modes_assembles (flex : List Nat) (input : Input) (sources : List Source)
    (selectors : Nat → Bool) (parameters : List (Nat × ModVar)) :
    ∃action,SymbolicSchemeModes.assemble
      (modes ModalSynthesis.locality flex input sources selectors) parameters=some action :=
  ComparisonGuardedWorldModes.witness_assembles _ _ selectors parameters


theorem modes_sound {input : Input} {sources : List Source} {queries : List Query}
    (hp : prepare (entries (fun n=>(input.bases n).length) sources).length
      (fun n=>(input.bases n).length) 0 sources=some queries)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    (ha : ∀source∈sources,source.Allowed input.keys) {side : Nat → Bool} {flex : List Nat}
    {selectors : Nat → Bool}
    (hs : CNFHolds selectors (ComparisonGuardedWorldModes.query side flex
      (entries (fun n=>(input.bases n).length) sources)))
    (hv : ∀q∈queries,q.Valid selectors images) :
    ∀source∈sources,source.Valid (fun n=>(input.bases n).length)
      (shapeValue (fun n=>(input.bases n).length) sources selectors) images (fun world v=>
        ((modes side flex input sources selectors).substitute v).eval world) := by
  let gs:=groups (fun n=>(input.bases n).length) images sources
  have hscalar : CNFHolds selectors
      (ComparisonGuardedWorldModes.query side flex (ComparisonGuardedWorldModes.batch gs)) := by
    simpa only [gs,groups_batch] using hs
  have hn:=(prepare_valid_iff hp hf ha selectors).mp hv
  have hn':=(ComparisonGuardedWorldModes.batch_nominal gs 0
    (shapeValue (fun n=>(input.bases n).length) sources selectors)
    (ComparisonWorldModes.worldChoice selectors)).mpr hn
  simp only [ComparisonIndexedWorldClauses.shiftChoice_zero] at hn'
  have hex : ComparisonGuardedWorldModes.externalValue (ComparisonGuardedWorldModes.batch gs).length
      selectors=shapeValue (fun n=>(input.bases n).length) sources selectors := by
    simp only [gs,groups_batch,shapeValue]
  have hvalid:=ComparisonGuardedWorldModes.query_sound hscalar (by simpa only [hex] using hn')
  have hb:=(ComparisonGuardedWorldModes.batch_valid gs _ _).mp hvalid
  rw [hex] at hb
  have he : (fun world v=>
      ((ComparisonGuardedWorldModes.witness side flex (ComparisonGuardedWorldModes.batch gs)
        selectors).substitute v).eval world)=
      (fun world v=>((modes side flex input sources selectors).substitute v).eval world) := by
    simp only [gs,groups_batch,modes]
  rw [he] at hb
  exact (groups_valid _ _ _ _ _).mp hb


/-- Successful execution reconstructs one finite type family, one modality
strategy, and a shape valuation satisfying the condition and every active query. -/
theorem run_sound {fuel : Nat} {input : Input} {side : Nat → Bool} {flex : List Nat}
    {sources : List Source} {shapeCondition : CNF} {result : ComparisonSignedQuerySolver.Solution}
    (ha : ∀source∈sources,source.Allowed input.keys)
    (h : run fuel input side flex sources shapeCondition=.success result) :
    ∃queries r,prepare (entries (fun n=>(input.bases n).length) sources).length
        (fun n=>(input.bases n).length) 0 sources=some queries ∧
      ComparisonSignedQueries.compile input queries=some r ∧
      input.reconstruct r (CNFPropagation.valuation result.selectors)=some result.images ∧
      result.images.map Prod.fst=input.keys ∧
      CNFHolds (shapeValue (fun n=>(input.bases n).length) sources
        (CNFPropagation.valuation result.selectors)) shapeCondition ∧
      Family input (input.imageValue r (CNFPropagation.valuation result.selectors)) ∧
      ∀source∈sources,source.Valid (fun n=>(input.bases n).length)
        (shapeValue (fun n=>(input.bases n).length) sources (CNFPropagation.valuation result.selectors))
        (input.imageValue r (CNFPropagation.valuation result.selectors)) (fun world v=>
          ((modes side flex input sources (CNFPropagation.valuation result.selectors)).substitute v).eval world) := by
  obtain ⟨queries,hp⟩:=prepare_complete (entries (fun n=>(input.bases n).length) sources).length
    (fun n=>(input.bases n).length) 0 sources
  have hr : ComparisonSignedQuerySolver.run fuel input queries
      (scalarQuery side flex (fun n=>(input.bases n).length) sources shapeCondition)=.success result := by
    simpa only [run,hp] using h
  obtain ⟨r,hc,hi,hs,hkeys,hf,hv⟩:=ComparisonSignedQuerySolver.run_sound (prepare_allowed hp ha) hr
  obtain ⟨hshape,hquery⟩:=(scalarQuery_parts side flex _ sources shapeCondition _).mp hs
  exact ⟨queries,r,hp,hc,hi,hkeys,hshape,hf,modes_sound hp hf ha hquery hv⟩

theorem run_complete_stable (input : Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) (shapeCondition : CNF) (hb : ∀source∈sources,source.Binary)
    (ha : ∀source∈sources,source.Allowed input.keys)
    {shape : Nat → Bool} (hshape : CNFHolds shape shapeCondition)
    {images : Nat → (Nat → Bool) → Bool} (hf : Family input images)
    {strategy : (Nat → Bool) → Nat → Bool} (hu : ModalSynthesis.Uniform side flex strategy)
    (hv : ∀source∈sources,source.Valid (fun n=>(input.bases n).length) shape images strategy) :
    ∃threshold result,∀fuel≥threshold,run fuel input side flex sources shapeCondition=.success result := by
  obtain ⟨queries,hp⟩:=prepare_complete (entries (fun n=>(input.bases n).length) sources).length
    (fun n=>(input.bases n).length) 0 sources
  obtain ⟨selectors,he,hs,hv⟩:=(strategy_iff hp hf ha side flex shape).mpr ⟨strategy,hu,hv⟩
  have hscalar : CNFHolds selectors
      (scalarQuery side flex (fun n=>(input.bases n).length) sources shapeCondition) := by
    apply (scalarQuery_parts side flex _ sources shapeCondition selectors).mpr
    exact ⟨by simpa only [he] using hshape,hs⟩
  obtain ⟨threshold,result,hr⟩:=ComparisonSignedQuerySolver.run_complete_stable input queries
    (scalarQuery side flex (fun n=>(input.bases n).length) sources shapeCondition)
    (prepare_binary hp hb) (prepare_allowed hp ha) hf hv hscalar
  exact ⟨threshold,result,fun fuel hfu=>by simpa only [run,hp] using hr fuel hfu⟩


theorem run_success_iff (input : Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) (shapeCondition : CNF) (hb : ∀source∈sources,source.Binary)
    (ha : ∀source∈sources,source.Allowed input.keys) :
    (∃fuel result,run fuel input side flex sources shapeCondition=.success result) ↔
      ∃shape,CNFHolds shape shapeCondition ∧ ∃images,Family input images ∧
        ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
          ∀source∈sources,source.Valid (fun n=>(input.bases n).length) shape images strategy := by
  constructor
  · rintro ⟨fuel,result,hr⟩
    obtain ⟨queries,r,_,_,_,_,hshape,hf,hv⟩:=run_sound ha hr
    exact ⟨_,hshape,_,hf,_,modes_uniform side flex input sources _,hv⟩
  · rintro ⟨shape,hshape,images,hf,strategy,hu,hv⟩
    obtain ⟨threshold,result,hr⟩:=run_complete_stable input side flex sources shapeCondition hb ha
      hshape hf hu hv
    exact ⟨threshold,result,hr threshold le_rfl⟩

theorem run_terminates (input : Input) (side : Nat → Bool) (flex : List Nat)
    (sources : List Source) (shapeCondition : CNF) :
    ∃threshold,∀fuel≥threshold,run fuel input side flex sources shapeCondition≠.exhausted := by
  obtain ⟨queries,hp⟩:=prepare_complete (entries (fun n=>(input.bases n).length) sources).length
    (fun n=>(input.bases n).length) 0 sources
  simpa only [run,hp] using ComparisonSignedQuerySolver.run_terminates input queries
    (scalarQuery side flex (fun n=>(input.bases n).length) sources shapeCondition)

theorem run_stable {n : Nat} {input : Input} {side : Nat → Bool} {flex : List Nat}
    {sources : List Source} {shapeCondition : CNF}
    {result : RunResult ComparisonSignedQuerySolver.Solution}
    (hne : result≠.exhausted) (h : run n input side flex sources shapeCondition=result) :
    ∀fuel≥n,run fuel input side flex sources shapeCondition=result := by
  obtain ⟨queries,hp⟩:=prepare_complete (entries (fun n=>(input.bases n).length) sources).length
    (fun n=>(input.bases n).length) 0 sources
  have hr : ComparisonSignedQuerySolver.run n input queries
      (scalarQuery side flex (fun n=>(input.bases n).length) sources shapeCondition)=result := by
    simpa only [run,hp] using h
  simpa only [run,hp] using ComparisonSignedQuerySolver.run_stable hne hr

end ModalityInference.ComparisonGuardedEndpointQueries
