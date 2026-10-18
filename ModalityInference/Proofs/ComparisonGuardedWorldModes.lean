import ModalityInference.ComparisonGuardedWorldModes
import ModalityInference.Proofs.ComparisonIndexedWorldClauses

/-! Activation guards and world selectors retain fixed shared constants while
all scalar blocks are solved by one uniform modality strategy. -/
namespace ModalityInference.ComparisonGuardedWorldModes
open ComparisonWorldClauses

@[simp] theorem externalValue_worldChoice (total : Nat) (selectors : Nat → Bool) (i : Nat) :
    externalValue total selectors i=
      ComparisonWorldModes.worldChoice selectors (externalIndex total i) := rfl

theorem externalIndex_disjoint {total i j b : Nat} (hj : j<total) :
    externalIndex total i≠selectorAtom j b := by
  intro he
  have hh:=congrArg (fun v=>(Nat.unpair v).1) he
  simp only [externalIndex,selectorAtom,Nat.unpair_pair] at hh
  omega

private theorem clause_map (f : Nat → Nat) (value : Nat → Bool) (c : Clause) :
    ClauseHolds value (c.map fun literal=>(f literal.1,literal.2)) ↔
      ClauseHolds (fun v=>value (f v)) c := by
  constructor
  · rintro ⟨v,p,hv,hp⟩
    obtain ⟨⟨u,q⟩,hu,he⟩:=List.mem_map.mp hv
    cases he
    exact ⟨u,q,hu,hp⟩
  · rintro ⟨v,p,hv,hp⟩
    exact ⟨f v,p,List.mem_map.mpr ⟨(v,p),hv,rfl⟩,hp⟩

theorem choices_correct (entries : List Entry) (selectors : Nat → Bool) :
    CNFHolds selectors (choices entries) ↔ ∀ei∈entries.zipIdx,
      ClauseHolds (externalValue entries.length selectors) ei.1.guard ∨
        ∃b∈blocks ei.1.clause,
          ComparisonWorldModes.worldChoice selectors (selectorAtom ei.2 b)=true := by
  simp only [choices,CNFHolds,List.forall_mem_map,clauseHolds_append,clause_map]
  apply forall_congr' fun ei=>imp_congr_right fun _=>?_
  apply or_congr_right
  constructor
  · rintro ⟨v,p,hv,hp⟩
    obtain ⟨b,hb,he⟩:=List.mem_map.mp hv
    cases he
    exact ⟨b,hb,hp⟩
  · rintro ⟨b,hb,hp⟩
    exact ⟨ComparisonWorldModes.worldConstant (selectorAtom ei.2 b),true,
      List.mem_map.mpr ⟨b,hb,rfl⟩,hp⟩

theorem query_parts (side : Nat → Bool) (flex : List Nat) (entries : List Entry)
    (selectors : Nat → Bool) :
    CNFHolds selectors (query side flex entries) ↔
      CNFHolds selectors (choices entries) ∧ CNFHolds selectors (prepare side flex entries).query :=
  cnfHolds_append _ _ _

theorem clauses_zip (entries : List Entry) :
    (clauses entries).zipIdx=entries.zipIdx.map (fun (entry,i)=>(entry.clause,i)) := by
  simp [clauses,List.zipIdx_map]

def Valid (nominal : ComparisonIndexedWorldClauses.Nominal) (shape : Nat → Bool)
    (strategy : (Nat → Bool) → Nat → Bool) (entries : List Entry) : Prop :=
  ∀ei∈entries.zipIdx,¬ClauseHolds shape ei.1.guard →
    ∀world,Holds (shared (nominal ei.2) strategy) ei.1.clause world

def NominalHolds (nominal : ComparisonIndexedWorldClauses.Nominal) (shape choice : Nat → Bool)
    (entries : List Entry) : Prop :=
  ∀ei∈entries.zipIdx,¬ClauseHolds shape ei.1.guard → ∀world,
    choice (selectorAtom ei.2 0)=false ∨ ClauseHolds (nominal ei.2 world) (block 0 ei.1.clause)

def extendChoice (total : Nat) (shape choice : Nat → Bool) (v : Nat) : Bool :=
  if (Nat.unpair v).1<total then choice v else shape ((Nat.unpair v).1-total)

@[simp] theorem extendChoice_selector {total i b : Nat} (hi : i<total)
    (shape choice : Nat → Bool) :
    extendChoice total shape choice (selectorAtom i b)=choice (selectorAtom i b) := by
  simp [extendChoice,selectorAtom,hi]

@[simp] theorem extendChoice_external (total i : Nat) (shape choice : Nat → Bool) :
    extendChoice total shape choice (externalIndex total i)=shape i := by
  simp [extendChoice,externalIndex,selectorAtom]

noncomputable def activeChoice (nominal : ComparisonIndexedWorldClauses.Nominal)
    (shape : Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    (entries : List Entry) (v : Nat) : Bool := by
  classical
  let entry := entries[(Nat.unpair v).1]?.getD default
  exact decide (¬ClauseHolds shape entry.guard ∧
    ∀world,ClauseHolds (shared (nominal (Nat.unpair v).1) strategy (Nat.unpair v).2 world)
      (block (Nat.unpair v).2 entry.clause))

noncomputable def canonicalChoice (nominal : ComparisonIndexedWorldClauses.Nominal)
    (shape : Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    (entries : List Entry) : Nat → Bool :=
  extendChoice entries.length shape (activeChoice nominal shape strategy entries)

theorem canonicalChoice_correct (nominal : ComparisonIndexedWorldClauses.Nominal)
    (shape : Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    {entries : List Entry} {entry : Entry} {i : Nat} (h : (entry,i)∈entries.zipIdx) (b : Nat) :
    canonicalChoice nominal shape strategy entries (selectorAtom i b)=true ↔
      ¬ClauseHolds shape entry.guard ∧
      ∀world,ClauseHolds (shared (nominal i) strategy b world) (block b entry.clause) := by
  have hi : i<entries.length := by simpa using List.snd_lt_of_mem_zipIdx h
  have he:=List.mk_mem_zipIdx_iff_getElem?.mp h
  rw [canonicalChoice,extendChoice_selector hi]
  simp [activeChoice,selectorAtom,Nat.unpair_pair,he]

@[simp] theorem canonicalChoice_external (nominal : ComparisonIndexedWorldClauses.Nominal)
    (shape : Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    (entries : List Entry) (i : Nat) :
    canonicalChoice nominal shape strategy entries (externalIndex entries.length i)=shape i := by
  simp [canonicalChoice]

theorem canonical_nominal {nominal : ComparisonIndexedWorldClauses.Nominal}
    {shape : Nat → Bool} {strategy : (Nat → Bool) → Nat → Bool} {entries : List Entry} :
    NominalHolds nominal shape (canonicalChoice nominal shape strategy entries) entries := by
  intro ei hei _ world
  by_cases hc:canonicalChoice nominal shape strategy entries (selectorAtom ei.2 0)=true
  · right
    simpa only [shared,if_pos rfl] using ((canonicalChoice_correct _ _ _ hei 0).mp hc).2 world
  · exact .inl (Bool.eq_false_iff.mpr hc)

theorem canonical_scalar {nominal : ComparisonIndexedWorldClauses.Nominal}
    {shape : Nat → Bool} {strategy : (Nat → Bool) → Nat → Bool} {entries : List Entry} :
    ∀world,CNFHolds (selectedValue (canonicalChoice nominal shape strategy entries) (strategy world))
      (scalar (clauses entries)) := by
  intro world
  rw [scalar_correct]
  intro ci hci b _ hb
  rw [clauses_zip] at hci
  obtain ⟨ei,hei,rfl⟩:=List.mem_map.mp hci
  by_cases hc:canonicalChoice nominal shape strategy entries (selectorAtom ei.2 b)=true
  · right
    simpa only [shared,if_neg hb] using ((canonicalChoice_correct _ _ _ hei b).mp hc).2 world
  · exact .inl (Bool.eq_false_iff.mpr hc)


/-- Preserving the full world-choice valuation also preserves every external
constant. Those constants occupy clause indices beyond this finite batch. -/
theorem externalValue_preserved {entries : List Entry}
    {nominal : ComparisonIndexedWorldClauses.Nominal} {shape : Nat → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} {selectors : Nat → Bool}
    (h : ComparisonWorldModes.worldChoice selectors=canonicalChoice nominal shape strategy entries) :
    externalValue entries.length selectors=shape := by
  funext i
  rw [externalValue_worldChoice,h,canonicalChoice_external]

theorem query_complete {side : Nat → Bool} {flex : List Nat} {entries : List Entry}
    {nominal : ComparisonIndexedWorldClauses.Nominal} {shape : Nat → Bool}
    {strategy : (Nat → Bool) → Nat → Bool} (hu : ModalSynthesis.Uniform side flex strategy)
    (hv : Valid nominal shape strategy entries) :
    ∃selectors,externalValue entries.length selectors=shape ∧
      CNFHolds selectors (query side flex entries) ∧
      NominalHolds nominal shape (ComparisonWorldModes.worldChoice selectors) entries := by
  let choice:=canonicalChoice nominal shape strategy entries
  obtain ⟨selectors,he,hcomponents⟩:=ComparisonWorldModes.components_complete hu choice
    (ComparisonWorldModes.scalarBlocks (clauses entries))
    (fun world=>(ComparisonWorldModes.scalarBlocks_correct choice (strategy world) (clauses entries)).mpr
      (canonical_scalar world))
  have hex : externalValue entries.length selectors=shape:=externalValue_preserved he
  refine ⟨selectors,hex,(query_parts side flex entries selectors).mpr ⟨?_,?_⟩,?_⟩
  · apply (choices_correct entries selectors).mpr
    intro ei hei
    rw [hex]
    by_cases hg:ClauseHolds shape ei.1.guard
    · exact .inl hg
    · right
      obtain ⟨b,hb⟩:=(clause_separation _ ei.1.clause).mp (hv ei hei hg)
      refine ⟨b,block_present (hb (fun _=>false)),?_⟩
      rw [he]
      exact (canonicalChoice_correct nominal shape strategy hei b).mpr ⟨hg,hb⟩
  · apply ComparisonJointModes.query_complete
      (ComparisonWorldModes.component_supported side true _)
      (ComparisonWorldModes.component_supported side false _) hu
    exact fun world=>⟨hcomponents true world,hcomponents false world⟩
  · rw [he]
    exact canonical_nominal

theorem witness_uniform (side : Nat → Bool) (flex : List Nat) (entries : List Entry)
    (selectors : Nat → Bool) :
    ModalSynthesis.Uniform side flex (fun world v=>
      ((witness side flex entries selectors).substitute v).eval world) :=
  ComparisonWorldModes.witness_uniform side flex _ selectors

theorem prepare_witness_sound {side : Nat → Bool} {flex : List Nat} {entries : List Entry}
    {selectors : Nat → Bool} (h : CNFHolds selectors (prepare side flex entries).query)
    (world : Nat → Bool) :
    CNFHolds (selectedValue (ComparisonWorldModes.worldChoice selectors) (fun v=>
      ((witness side flex entries selectors).substitute v).eval world)) (scalar (clauses entries)) := by
  apply (ComparisonWorldModes.scalarBlocks_correct _ _ _).mp
  apply ComparisonWorldModes.components_sound
  have hs:=ComparisonJointModes.witness_sound
    (ComparisonWorldModes.component_supported side true (ComparisonWorldModes.scalarBlocks (clauses entries)))
    (ComparisonWorldModes.component_supported side false (ComparisonWorldModes.scalarBlocks (clauses entries)))
    h world
  intro axis
  cases axis
  · exact hs.2
  · exact hs.1

theorem selectors_sound {entries : List Entry} {nominal : ComparisonIndexedWorldClauses.Nominal}
    {strategy : (Nat → Bool) → Nat → Bool} {selectors : Nat → Bool}
    (hc : CNFHolds selectors (choices entries))
    (hn : NominalHolds nominal (externalValue entries.length selectors)
      (ComparisonWorldModes.worldChoice selectors) entries)
    (hs : ∀world,CNFHolds (selectedValue (ComparisonWorldModes.worldChoice selectors) (strategy world))
      (scalar (clauses entries))) :
    Valid nominal (externalValue entries.length selectors) strategy entries := by
  intro ei hei hg world
  obtain ⟨b,hb,hchoice⟩:=((choices_correct entries selectors).mp hc ei hei).resolve_left hg
  apply (holds_blocks _ _ _).mpr
  refine ⟨b,?_⟩
  by_cases hz:b=0
  · subst b
    have hh:=hn ei hei hg (world 0)
    simpa only [shared,if_pos rfl] using hh.resolve_left (by simp [hchoice])
  · have hci : (ei.1.clause,ei.2)∈(clauses entries).zipIdx := by
      rw [clauses_zip]
      exact List.mem_map.mpr ⟨ei,hei,rfl⟩
    have hh:=(scalar_correct _ _ _).mp (hs (world b)) _ hci b hb hz
    simpa only [shared,if_neg hz] using hh.resolve_left (by simp [hchoice])

theorem query_sound {side : Nat → Bool} {flex : List Nat} {entries : List Entry}
    {nominal : ComparisonIndexedWorldClauses.Nominal} {selectors : Nat → Bool}
    (hq : CNFHolds selectors (query side flex entries))
    (hn : NominalHolds nominal (externalValue entries.length selectors)
      (ComparisonWorldModes.worldChoice selectors) entries) :
    Valid nominal (externalValue entries.length selectors)
      (fun world v=>((witness side flex entries selectors).substitute v).eval world) entries := by
  have hh:=(query_parts side flex entries selectors).mp hq
  exact selectors_sound hh.1 hn (prepare_witness_sound hh.2)

/-- Activation constants are retained exactly, while one uniform scalar
strategy solves every active clause in the entire batch. -/
theorem query_iff (side : Nat → Bool) (flex : List Nat) (entries : List Entry)
    (nominal : ComparisonIndexedWorldClauses.Nominal) (shape : Nat → Bool) :
    (∃selectors,externalValue entries.length selectors=shape ∧
      CNFHolds selectors (query side flex entries) ∧
      NominalHolds nominal shape (ComparisonWorldModes.worldChoice selectors) entries) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧ Valid nominal shape strategy entries := by
  constructor
  · rintro ⟨selectors,hex,hq,hn⟩
    refine ⟨_,witness_uniform side flex entries selectors,?_⟩
    have hv:=query_sound hq (by simpa only [hex] using hn)
    simpa only [hex] using hv
  · rintro ⟨strategy,hu,hv⟩
    exact query_complete hu hv

theorem witness_assembles (flex : List Nat) (entries : List Entry) (selectors : Nat → Bool)
    (parameters : List (Nat × ModVar)) :
    ∃action,SymbolicSchemeModes.assemble
      (witness ModalSynthesis.locality flex entries selectors) parameters=some action :=
  ComparisonWorldModes.witness_assembles _ selectors parameters

end ModalityInference.ComparisonGuardedWorldModes
