import ModalityInference.ComparisonSignedNominalEdges
import ModalityInference.Proofs.ComparisonSignedNominal
import ModalityInference.Proofs.ComparisonSignedEdges
import ModalityInference.Proofs.ComparisonWorldOffsets
import ModalityInference.Proofs.ComparisonSignedStrategySynthesis

/-! Parsed nominal clauses retain their original type calls and compile to a
signed relation under the same global selectors used by scalar synthesis. -/
namespace ModalityInference.ComparisonSignedNominalEdges
open ComparisonSignedEndpoints ComparisonWorldClauses ComparisonSignedRelations

private theorem offset_clause_complete (offset : Nat) (decoder : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause) {c : ModalityInference.Clause}
    (hc : c∈ComparisonWorldOffsets.nominal offset (ComparisonSignedWorlds.query decoder theory clauses)) :
    ∃result,ComparisonSignedNominal.parseClause (ComparisonSignedWorlds.calls clauses) c=some result ∧
      ∃original∈clauses,result.literals=original.literals := by
  obtain ⟨⟨worldClause,index⟩,hci,rfl⟩:=List.mem_map.mp hc
  have hw:=List.fst_mem_of_mem_zipIdx hci
  obtain ⟨original,ho,hw⟩:=List.mem_flatMap.mp hw
  obtain ⟨guard,_,he⟩:=List.mem_map.mp hw
  cases he
  obtain ⟨result,hr,hl⟩:=ComparisonSignedNominal.parse_selected
    (fun l hl=>ComparisonSignedWorlds.call_mem ho hl) decoder guard (offset+index)
  exact ⟨result,hr,original,ho,hl⟩

theorem prepare_complete (offset : Nat) (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause) :
    ∃result,prepare offset size decoder theory clauses=some result ∧
      ∀c∈result,∃original∈clauses,c.literals=original.literals := by
  let shifted:=clauses.map ComparisonSignedPoints.clause
  let original:=ComparisonSignedPoints.theory (ComparisonSignedWorlds.calls clauses) size theory
  obtain ⟨result,hr⟩:=ComparisonSignedNominal.parse_complete (fun c hc=>
    let h:=offset_clause_complete offset (ComparisonSignedPoints.decode decoder) original shifted hc
    ⟨h.choose,h.choose_spec.1⟩)
  refine ⟨result,hr,?_⟩
  intro c hc
  obtain ⟨source,hs,hp⟩:=ComparisonSignedNominal.parse_mem hr hc
  obtain ⟨parsed,hparsed,before,hb,he⟩:=
    offset_clause_complete offset (ComparisonSignedPoints.decode decoder) original shifted hs
  have heq : parsed=c := Option.some.inj (hparsed.symm.trans hp)
  subst parsed
  obtain ⟨source,hsource,rfl⟩:=List.mem_map.mp hb
  exact ⟨source,hsource,he⟩

theorem prepare_origin {offset : Nat} {size : Nat → Nat} {decoder : Nat → Nat × Nat}
    {theory : CNF} {clauses result : List CompiledClause}
    (h : prepare offset size decoder theory clauses=some result) {c : CompiledClause} (hc : c∈result) :
    ∃original∈clauses,c.literals=original.literals := by
  obtain ⟨produced,hp,ho⟩:=prepare_complete offset size decoder theory clauses
  have he : produced=result := Option.some.inj (hp.symm.trans h)
  subst produced
  exact ho c hc

theorem prepare_correct {offset : Nat} {size : Nat → Nat} {decoder : Nat → Nat × Nat}
    {theory : CNF} {clauses result : List CompiledClause}
    (h : prepare offset size decoder theory clauses=some result)
    (selectors world : Nat → Bool) (images : Nat → (Nat → Bool) → Bool) :
    CNFHolds
      (selectedValue (ComparisonWorldModes.worldChoice selectors)
        (ComparisonSignedStrategySynthesis.nominalValue size clauses images world))
      (ComparisonWorldOffsets.nominal offset
        (ComparisonSignedStrategySynthesis.worlds size decoder theory clauses)) ↔
      ∀c∈result,c.Holds (ComparisonSignedNominal.guardValue selectors world)
        (ComparisonSignedPoints.nominalImages (ComparisonSignedWorlds.calls clauses) size images world) :=
  ComparisonSignedNominal.parse_correct h selectors world _

theorem run_spec {offset width key size decoder theory clauses result}
    (h : run offset width key size decoder theory clauses=some result) :
    ∃parsed,prepare offset size decoder theory clauses=some parsed ∧
      ComparisonSignedEdges.compileWith
        (ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls clauses))
        width key size ComparisonSignedNominal.guardDecode [] parsed=some result := by
  cases hp:prepare offset size decoder theory clauses <;> simp [run,hp] at h
  exact ⟨_,rfl,h⟩

theorem run_complete (offset width : Nat) (key : Nat → List Bool) (size : Nat → Nat)
    (decoder : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause)
    (hb : ∀c∈clauses,c.literals.length≤2) :
    ∃result,run offset width key size decoder theory clauses=some result := by
  obtain ⟨parsed,hp,ho⟩:=prepare_complete offset size decoder theory clauses
  have hb' : ∀c∈parsed,c.literals.length≤2 := by
    intro c hc
    obtain ⟨original,hm,he⟩:=ho c hc
    rw [he]
    exact hb original hm
  obtain ⟨result,hr⟩:=ComparisonSignedEdges.compile_complete
    (payload:=ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls clauses))
    (width:=width) (key:=key) (size:=size) (decode:=ComparisonSignedNominal.guardDecode)
    (theory:=[]) hb'
  exact ⟨result,by simp [run,hp,hr]⟩

def tupleImages (key : Nat → List Bool) (size : Nat → Nat) (value : (Nat → Bool) → Bool)
    (name : Nat) (point : Nat → Bool) : Bool :=
  value (ComparisonSignedPolynomials.tuple (key name) (size name) true point)

theorem callValue_nominal (names : List Call) (key : Nat → List Bool) (size : Nat → Nat)
    (value : (Nat → Bool) → Bool) (selectors world : Nat → Bool) (call : Call) :
    value (ComparisonSignedEdges.callValueWith (ComparisonSignedNominal.payload names) key size
      (ComparisonSignedEdges.decoded ComparisonSignedNominal.guardDecode selectors world) call true)=
      ComparisonSignedPoints.nominalImages names size (tupleImages key size value) world call := by
  rw [ComparisonSignedEdges.callValue_tuple]
  apply congrArg value
  funext i
  unfold ComparisonSignedPolynomials.tuple
  split
  · rfl
  · split
    · next hi =>
      have hj : i-((key call.name).length+1)<size call.name := by omega
      dsimp only
      rw [ComparisonSignedNominal.payload_value]
      simp only [ComparisonSignedPoints.nominalPoint,if_pos hj]
    · rfl

theorem run_valid_iff {offset width key size decoder theory clauses result}
    (h : run offset width key size decoder theory clauses=some result)
    (selectors : Nat → Bool) {value : (Nat → Bool) → Bool}
    (hn : ∀a,value (ComparisonSignedCanonical.toggle 0 a)=!value a)
    (hs : ∀{a b},Same width a b → value a=value b) :
    (∀a b,Holds selectors result a b → value a≤value b) ↔
      ∀world,CNFHolds
        (selectedValue (ComparisonWorldModes.worldChoice selectors)
          (ComparisonSignedStrategySynthesis.nominalValue size clauses (tupleImages key size value) world))
        (ComparisonWorldOffsets.nominal offset
          (ComparisonSignedStrategySynthesis.worlds size decoder theory clauses)) := by
  obtain ⟨parsed,hp,hc⟩:=run_spec h
  rw [ComparisonSignedEdges.compile_valid_iff hc selectors hn hs]
  constructor
  · intro h world
    apply (prepare_correct hp selectors world (tupleImages key size value)).mpr
    have hh:=h world (by simp [CNFHolds])
    have he : (fun call => value (ComparisonSignedEdges.callValueWith
        (ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls clauses)) key size
        (ComparisonSignedEdges.decoded ComparisonSignedNominal.guardDecode selectors world) call true)) =
        ComparisonSignedPoints.nominalImages (ComparisonSignedWorlds.calls clauses) size
          (tupleImages key size value) world := funext fun call => callValue_nominal _ _ _ _ _ _ call
    rw [he,ComparisonSignedNominal.guardDecode_value] at hh
    exact hh
  · intro h world _
    have hh:=(prepare_correct hp selectors world (tupleImages key size value)).mp (h world)
    have he : (fun call => value (ComparisonSignedEdges.callValueWith
        (ComparisonSignedNominal.payload (ComparisonSignedWorlds.calls clauses)) key size
        (ComparisonSignedEdges.decoded ComparisonSignedNominal.guardDecode selectors world) call true)) =
        ComparisonSignedPoints.nominalImages (ComparisonSignedWorlds.calls clauses) size
          (tupleImages key size value) world := funext fun call => callValue_nominal _ _ _ _ _ _ call
    rw [he,ComparisonSignedNominal.guardDecode_value]
    exact hh

/-- A zero-offset endpoint graph and the scalar query use one common selector
valuation and one common image family. -/
theorem run_strategy_iff {width key size decoder theory clauses result}
    (h : run 0 width key size decoder theory clauses=some result)
    (side : Nat → Bool) (flex : List Nat) {value : (Nat → Bool) → Bool}
    (hn : ∀a,value (ComparisonSignedCanonical.toggle 0 a)=!value a)
    (hs : ∀{a b},Same width a b → value a=value b) :
    (∃selectors,CNFHolds selectors
        (ComparisonSignedStrategySynthesis.scalarQuery side flex size decoder theory clauses) ∧
      ∀a b,Holds selectors result a b → value a≤value b) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        ComparisonSignedStrategySynthesis.Valid size decoder theory clauses
          (tupleImages key size value) strategy := by
  have he := ComparisonSignedStrategySynthesis.query_iff side flex size decoder theory clauses
    (tupleImages key size value)
  rw [←he]
  apply exists_congr
  intro selectors
  apply and_congr_right
  intro _
  simpa only [ComparisonWorldOffsets.nominal_zero,
    ComparisonSignedStrategySynthesis.nominalQuery] using run_valid_iff h selectors hn hs

end ModalityInference.ComparisonSignedNominalEdges
