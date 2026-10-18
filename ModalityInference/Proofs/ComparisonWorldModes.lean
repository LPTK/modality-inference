import ModalityInference.ComparisonWorldModes
import ModalityInference.Proofs.ComparisonWorldClauses
import ModalityInference.Proofs.ComparisonJointModes

/-! Constant world and dependency-axis choices are compiled into one selector
query. Scalar reconstruction preserves a single uniform strategy across all
world blocks and leaves the same world selectors available to nominal solving. -/
namespace ModalityInference.ComparisonWorldModes
open ComparisonWorldClauses

@[simp] theorem encode_world (selectors values : Nat → Bool) (i : Nat) :
    ModalSynthesis.encode selectors values (worldConstant i)=worldChoice selectors i := by
  change ModalSynthesis.encode selectors values (4*i+1)=selectors (4*i+1)
  rw [show 4*i+1=2*(2*i)+1 by omega,ModalSynthesis.encode_odd]

@[simp] theorem encode_axis (selectors values : Nat → Bool) (i : Nat) :
    ModalSynthesis.encode selectors values (axisConstant i)=selectors (axisConstant i) := by
  change ModalSynthesis.encode selectors values (4*i+3)=selectors (4*i+3)
  rw [show 4*i+3=2*(2*i+1)+1 by omega,ModalSynthesis.encode_odd]

def ScalarHolds (choice value : Nat → Bool) (entries : List (Nat × Clause)) : Prop :=
  ∀entry∈entries,choice entry.1=false ∨ ClauseHolds value entry.2

theorem scalarBlocks_correct (choice value : Nat → Bool) (cs : List WorldClause) :
    ScalarHolds choice value (scalarBlocks cs) ↔
      CNFHolds (selectedValue choice value) (scalar cs) := by
  rw [scalar_correct]
  simp only [ScalarHolds,scalarBlocks,List.forall_mem_flatMap,List.forall_mem_map,
    List.mem_filter,bne_iff_ne,and_imp]

theorem even_clause (selectors values : Nat → Bool) (c : Clause) :
    ClauseHolds (ModalSynthesis.encode selectors values) (c.map fun literal => (2*literal.1,literal.2)) ↔
      ClauseHolds values c := by
  constructor
  · rintro ⟨v,p,hl,hv⟩
    obtain ⟨⟨w,q⟩,hw,he⟩:=List.mem_map.mp hl
    cases he
    exact ⟨w,q,hw,by simpa only [ModalSynthesis.encode_even] using hv⟩
  · rintro ⟨v,p,hv,he⟩
    exact ⟨2*v,p,List.mem_map.mpr ⟨(v,p),hv,rfl⟩,by simpa only [ModalSynthesis.encode_even] using he⟩

theorem component_correct (side : Nat → Bool) (axis : Bool) (entries : List (Nat × Clause))
    (selectors value : Nat → Bool) :
    CNFHolds (ModalSynthesis.encode selectors value) (component side axis entries) ↔
      ∀i (hi:i<entries.length),worldChoice selectors entries[i].1=false ∨
        selectors (axisConstant i)=!axis ∨
        ClauseHolds value (entries[i].2.filter fun literal => side literal.1 == axis) := by
  simp only [component,CNFHolds,List.forall_mem_map,List.forall_mem_zipIdx']
  apply forall_congr' fun i => forall_congr' fun hi => ?_
  rw [clauseHolds_append,even_clause]
  have hn : ClauseHolds (ModalSynthesis.encode selectors value) [] ↔ False := by simp [ClauseHolds]
  simp only [clauseHolds_cons,encode_world,encode_axis,hn,or_false,or_assoc]

theorem component_supported (side : Nat → Bool) (axis : Bool) (entries : List (Nat × Clause)) :
    ComparisonJointModes.ComponentSupported side axis (component side axis entries) := by
  intro v hv
  obtain ⟨c,hc,polarity,hp⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨⟨entry,i⟩,hei,rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hp with hp|hp
  · rcases List.mem_cons.mp hp with he|hp
    · cases he
      left
      simp only [worldConstant,ModalSynthesis.selector,beq_iff_eq]
      omega
    · cases List.mem_singleton.mp hp
      left
      simp only [axisConstant,ModalSynthesis.selector,beq_iff_eq]
      omega
  · obtain ⟨⟨w,p⟩,hw,he⟩ := List.mem_map.mp hp
    cases he
    exact .inr ⟨w,rfl,by simpa using (List.mem_filter.mp hw).2⟩

/-- World selectors and dependency-axis selectors occupy disjoint constant names. -/
def joinChoices (world axis : Nat → Bool) (v : Nat) : Bool :=
  if v%4=1 then world (v/4) else axis (v/4)

@[simp] theorem joinChoices_world (world axis : Nat → Bool) (i : Nat) :
    worldChoice (joinChoices world axis) i=world i := by
  simp [worldChoice,worldConstant,joinChoices,show (4*i+1)/4=i by omega]

@[simp] theorem joinChoices_axis (world axis : Nat → Bool) (i : Nat) :
    joinChoices world axis (axisConstant i)=axis i := by
  simp [axisConstant,joinChoices,show (4*i+3)/4=i by omega]

theorem components_complete {side : Nat → Bool} {flex : List Nat}
    {strategy : (Nat → Bool) → Nat → Bool} (hu : ModalSynthesis.Uniform side flex strategy)
    (choice : Nat → Bool) (entries : List (Nat × Clause))
    (h : ∀world,ScalarHolds choice (strategy world) entries) :
    ∃selectors,worldChoice selectors=choice ∧ ∀axis world,
      CNFHolds (ModalSynthesis.encode selectors (strategy world)) (component side axis entries) := by
  classical
  let axis : Nat → Bool := fun i => if hi:i<entries.length then
    decide (∀world,ClauseHolds (strategy world) (entries[i].2.filter fun l => side l.1==true))
    else false
  refine ⟨joinChoices choice axis,funext (joinChoices_world choice axis),?_⟩
  intro b world
  rw [component_correct]
  intro i hi
  simp only [joinChoices_world,joinChoices_axis]
  by_cases hc:choice entries[i].1=false
  · exact .inl hc
  · right
    have hh : ∀world,ClauseHolds (strategy world) entries[i].2 := fun world =>
      (h world entries[i] (List.getElem_mem hi)).resolve_left hc
    have hf:=ModalSynthesis.clause_factor hu hh
    cases b
    · by_cases ha:∀world,ClauseHolds (strategy world) (entries[i].2.filter fun l => side l.1==true)
      · left
        simp only [axis,dif_pos hi,Bool.not_false,decide_eq_true_eq]
        exact ha
      · right
        exact (hf.resolve_left ha) world
    · by_cases ha:∀world,ClauseHolds (strategy world) (entries[i].2.filter fun l => side l.1==true)
      · exact .inr (ha world)
      · left
        simp only [axis,dif_pos hi,Bool.not_true,decide_eq_false_iff_not]
        exact ha

theorem components_sound {side : Nat → Bool} {entries : List (Nat × Clause)}
    {selectors value : Nat → Bool}
    (h : ∀axis,CNFHolds (ModalSynthesis.encode selectors value) (component side axis entries)) :
    ScalarHolds (worldChoice selectors) value entries := by
  intro entry he
  obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem he
  have hc := (component_correct side (selectors (axisConstant i)) entries selectors value).mp
    (h (selectors (axisConstant i))) i hi
  rcases hc with hc|hc|hc
  · exact .inl hc
  · cases hd:selectors (axisConstant i) <;> simp [hd] at hc
  · right
    obtain ⟨v,p,hv,hp⟩:=hc
    exact ⟨v,p,(List.mem_filter.mp hv).1,hp⟩

theorem query_parts (side : Nat → Bool) (flex : List Nat) (cs : List WorldClause)
    (selectors : Nat → Bool) :
    CNFHolds selectors (query side flex cs) ↔
      CNFHolds (worldChoice selectors) (choices cs) ∧
      CNFHolds selectors (prepare side flex cs).query := by
  rw [query,cnfHolds_append]
  apply and_congr_left
  intro _
  change CNFHolds selectors (ComparisonPropagation.rename worldConstant (choices cs)) ↔ _
  exact ComparisonPropagation.rename_correct worldConstant (choices cs) selectors

theorem witness_uniform (side : Nat → Bool) (flex : List Nat) (cs : List WorldClause)
    (selectors : Nat → Bool) :
    ModalSynthesis.Uniform side flex (fun world v =>
      ((witness side flex cs selectors).substitute v).eval world) := by
  exact ComparisonJointModes.witness_uniform
    (component_supported side true _) (component_supported side false _) selectors

theorem witness_sound {side : Nat → Bool} {flex : List Nat} {cs : List WorldClause}
    {selectors : Nat → Bool} (h : CNFHolds selectors (query side flex cs)) (world : Nat → Bool) :
    CNFHolds (selectedValue (worldChoice selectors) (fun v =>
      ((witness side flex cs selectors).substitute v).eval world)) (scalar cs) := by
  apply (scalarBlocks_correct _ _ _).mp
  apply components_sound
  have hs:=ComparisonJointModes.witness_sound
    (component_supported side true (scalarBlocks cs))
    (component_supported side false (scalarBlocks cs))
    ((query_parts side flex cs selectors).mp h).2 world
  intro axis
  cases axis
  · exact hs.2
  · exact hs.1

/-- A fixed world choice is extended only with dependency-axis constants. All
selected scalar blocks are solved by the same uniform strategy. -/
theorem query_complete {side : Nat → Bool} {flex : List Nat} {cs : List WorldClause}
    {strategy : (Nat → Bool) → Nat → Bool} (hu : ModalSynthesis.Uniform side flex strategy)
    (choice : Nat → Bool) (hc : CNFHolds choice (choices cs))
    (hs : ∀world,CNFHolds (selectedValue choice (strategy world)) (scalar cs)) :
    ∃selectors,worldChoice selectors=choice ∧ CNFHolds selectors (query side flex cs) := by
  obtain ⟨selectors,he,h⟩:=components_complete hu choice (scalarBlocks cs)
    (fun world => (scalarBlocks_correct choice (strategy world) cs).mpr (hs world))
  refine ⟨selectors,he,(query_parts side flex cs selectors).mpr ⟨he ▸ hc,?_⟩⟩
  apply ComparisonJointModes.query_complete
    (component_supported side true _) (component_supported side false _) hu
  exact fun world => ⟨h true world,h false world⟩

theorem query_iff (side : Nat → Bool) (flex : List Nat) (cs : List WorldClause)
    (choice : Nat → Bool) :
    (∃selectors,worldChoice selectors=choice ∧ CNFHolds selectors (query side flex cs)) ↔
      CNFHolds choice (choices cs) ∧ ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        ∀world,CNFHolds (selectedValue choice (strategy world)) (scalar cs) := by
  constructor
  · rintro ⟨selectors,he,h⟩
    refine ⟨he ▸ ((query_parts side flex cs selectors).mp h).1,_,
      witness_uniform side flex cs selectors,?_⟩
    intro world
    simpa only [←he] using witness_sound h world
  · rintro ⟨hc,strategy,hu,hs⟩
    exact query_complete hu choice hc hs

/-- The nominal component keeps the very same constant selectors used by the
single scalar solve; neither images nor modes are chosen separately per world. -/
theorem separated_iff (side : Nat → Bool) (flex : List Nat) (cs : List WorldClause)
    (nominalValue : (Nat → Bool) → Nat → Bool) :
    (∃selectors,CNFHolds selectors (query side flex cs) ∧
      ∀world,CNFHolds (selectedValue (worldChoice selectors) (nominalValue world)) (nominal cs)) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧ Valid nominalValue strategy cs := by
  constructor
  · rintro ⟨selectors,h,hn⟩
    refine ⟨_,witness_uniform side flex cs selectors,selectors_sound (choice:=worldChoice selectors) ?_⟩
    exact ⟨((query_parts side flex cs selectors).mp h).1,hn,witness_sound h⟩
  · rintro ⟨strategy,hu,h⟩
    obtain ⟨choice,hc,hn,hs⟩:=(selectors_iff nominalValue strategy cs).mp h
    obtain ⟨selectors,he,hq⟩:=query_complete hu choice hc hs
    exact ⟨selectors,hq,fun world => he ▸ hn world⟩

theorem witness_assembles {flex : List Nat} (cs : List WorldClause)
    (selectors : Nat → Bool) (parameters : List (Nat × ModVar)) :
    ∃action,SymbolicSchemeModes.assemble
      (witness ModalSynthesis.locality flex cs selectors) parameters=some action := by
  exact ComparisonJointModes.witness_assembles
    (component_supported _ true _) (component_supported _ false _) selectors parameters

end ModalityInference.ComparisonWorldModes
