import ModalityInference.ComparisonSignedNominal
import ModalityInference.Proofs.ComparisonSignedStrategySynthesis
import ModalityInference.Proofs.ComparisonSignedEdgeProjection

/-! Decoding actual nominal clauses preserves their original signed calls,
selector parameters and independent point inputs. Generated two-call clauses
remain binary and always decode successfully. -/
namespace ModalityInference.ComparisonSignedNominal
open ComparisonSignedEndpoints ComparisonWorldClauses

def guardValue (selectors world : Nat → Bool) (v : Nat) : Bool :=
  if v%2=1 then selectors (v/2) else world (v/2)

def encoded (names : List Call) (selectors world : Nat → Bool)
    (images : (Nat → Bool) → Call → Bool) : Nat → Bool :=
  selectedValue (ComparisonWorldModes.worldChoice selectors)
    (ComparisonSignedWorlds.nominalValue names (fun w=>w) images world)

theorem guardAtom_correct {v : Nat} (hv : isImage v=false) (names : List Call)
    (selectors world : Nat → Bool) (images : (Nat → Bool) → Call → Bool) :
    encoded names selectors world images v=guardValue selectors world (guardAtom v) := by
  have hmod : v%4≠2 := by simpa [isImage] using hv
  by_cases ho:v%2=1
  · have hd : v=2*(v/2)+1 := by omega
    conv_lhs => rw [hd]
    simp only [encoded,selectedValue_odd,ComparisonWorldModes.worldChoice]
    simp [guardAtom,ho,guardValue,show (2*ComparisonWorldModes.worldConstant (v/2)+1)/2=
      ComparisonWorldModes.worldConstant (v/2) by omega]
  · have hd : v=2*(2*(v/4)) := by omega
    calc
      encoded names selectors world images v=encoded names selectors world images (2*(2*(v/4))) :=
        congrArg (encoded names selectors world images) hd
      _=world (v/4) := by simp only [encoded,selectedValue_even,ComparisonSignedWorlds.nominal_even]
      _=guardValue selectors world (guardAtom v) := by simp [guardAtom,ho,guardValue]

theorem image_correct {names : List Call} {v : Nat} {call : Call}
    (hv : isImage v=true) (hc : names[v/4]?=some call)
    (selectors world : Nat → Bool) (images : (Nat → Bool) → Call → Bool) :
    encoded names selectors world images v=images world call := by
  have hmod : v%4=2 := by simpa [isImage] using hv
  have hd : v=2*(2*(v/4)+1) := by omega
  conv_lhs => rw [hd]
  simp only [encoded,selectedValue_even]
  simp [ComparisonSignedWorlds.nominalValue,hc,show (2*(v/4)+1)/2=v/4 by omega]

theorem holds_guard_cons (g : ModalityInference.Clause) (ls : List (Call × Bool))
    (v : Nat) (p : Bool) (world : Nat → Bool) (images : Call → Bool) :
    (CompiledClause.mk ((v,p)::g) ls).Holds world images ↔
      world v=p ∨ (CompiledClause.mk g ls).Holds world images := by
  simp only [CompiledClause.Holds,clauseHolds_cons,or_assoc]

theorem holds_image_cons (g : ModalityInference.Clause) (ls : List (Call × Bool))
    (call : Call) (p : Bool) (world : Nat → Bool) (images : Call → Bool) :
    (CompiledClause.mk g ((call,p)::ls)).Holds world images ↔
      images call=p ∨ (CompiledClause.mk g ls).Holds world images := by
  simp only [CompiledClause.Holds,List.mem_cons]
  aesop

theorem parseClause_correct {names : List Call} {c : ModalityInference.Clause} {result : CompiledClause}
    (h : parseClause names c=some result) (selectors world : Nat → Bool)
    (images : (Nat → Bool) → Call → Bool) :
    ClauseHolds (encoded names selectors world images) c ↔
      result.Holds (guardValue selectors world) (images world) := by
  induction c generalizing result with
  | nil =>
    simp only [parseClause,Option.some.injEq] at h
    cases h
    simp [ClauseHolds,CompiledClause.Holds]
  | cons literal rest ih =>
    rcases literal with ⟨v,p⟩
    cases ht:parseClause names rest with
    | none => simp [parseClause,ht] at h
    | some tail =>
      cases hi:isImage v with
      | false =>
        simp only [parseClause,ht,hi,Bool.false_eq_true,if_false] at h
        cases h
        rw [clauseHolds_cons,holds_guard_cons,guardAtom_correct hi]
        exact or_congr Iff.rfl (ih ht)
      | true =>
        cases hc:names[v/4]? with
        | none => simp [parseClause,ht,hi,hc] at h
        | some call =>
          simp only [parseClause,ht,hi,if_true,hc] at h
          cases h
          rw [clauseHolds_cons,holds_image_cons,image_correct hi hc]
          exact or_congr Iff.rfl (ih ht)

def Covered (names : List Call) (c : ModalityInference.Clause) : Prop :=
  ∀v p,(v,p)∈c → isImage v=true → ∃call,names[v/4]?=some call

theorem parseClause_complete {names : List Call} {c : ModalityInference.Clause}
    (h : Covered names c) : ∃result,parseClause names c=some result := by
  induction c with
  | nil => exact ⟨⟨[],[]⟩,rfl⟩
  | cons literal rest ih =>
    obtain ⟨tail,ht⟩:=ih (fun v p hv hi => h v p (.tail _ hv) hi)
    rcases literal with ⟨v,p⟩
    cases hi:isImage v
    · exact ⟨⟨(guardAtom v,p)::tail.guard,tail.literals⟩,by simp [parseClause,ht,hi]⟩
    · obtain ⟨call,hc⟩:=h v p (.head _) hi
      exact ⟨⟨tail.guard,(call,p)::tail.literals⟩,by simp [parseClause,ht,hi,hc]⟩

theorem parseClause_append {names : List Call} {left right : ModalityInference.Clause}
    {a b : CompiledClause} (ha : parseClause names left=some a) (hb : parseClause names right=some b) :
    parseClause names (left++right)=some ⟨a.guard++b.guard,a.literals++b.literals⟩ := by
  induction left generalizing a with
  | nil =>
    simp only [parseClause,Option.some.injEq] at ha
    cases ha
    exact hb
  | cons literal rest ih =>
    rcases literal with ⟨v,p⟩
    cases ht:parseClause names rest with
    | none => simp [parseClause,ht] at ha
    | some tail =>
      cases hi:isImage v with
      | false =>
        simp only [parseClause,ht,hi,Bool.false_eq_true,if_false] at ha
        cases ha
        simp only [List.cons_append,parseClause,ih ht,hi,Bool.false_eq_true,if_false]
        rfl
      | true =>
        cases hc:names[v/4]? with
        | none => simp [parseClause,ht,hi,hc] at ha
        | some call =>
          simp only [parseClause,ht,hi,if_true,hc] at ha
          cases ha
          simp only [List.cons_append,parseClause,ih ht,hi,if_true,hc]
          rfl

theorem parseClause_guards {names : List Call} {c : ModalityInference.Clause}
    (h : ∀l∈c,isImage l.1=false) :
    parseClause names c=some ⟨c.map (fun l => (guardAtom l.1,l.2)),[]⟩ := by
  induction c with
  | nil => rfl
  | cons literal rest ih =>
    have hi:=h literal (.head _)
    have ht:=ih (fun l hl=>h l (.tail _ hl))
    simp [parseClause,hi,ht]

theorem mem_block {b v : Nat} {p : Bool} {c : WorldClause} (h : (v,p)∈block b c) :
    (b,(v,p))∈c := by
  obtain ⟨⟨b',v',p'⟩,hm,hv⟩:=List.mem_filterMap.mp h
  dsimp at hv
  split at hv
  · next he =>
    cases he
    cases Option.some.inj hv
    exact hm
  · simp at hv

theorem rawAtom_even {decoder : Nat → Nat × Nat} {v : Nat}
    (h : (ComparisonSignedWorlds.rawAtom decoder v).1=0) :
    (ComparisonSignedWorlds.rawAtom decoder v).2%2=0 := by
  by_cases hb:(decoder v).1=0
  · simp [ComparisonSignedWorlds.rawAtom,hb]
  · simp [ComparisonSignedWorlds.rawAtom,hb] at h

theorem raw_block_even {decoder : Nat → Nat × Nat} {c : ModalityInference.Clause}
    {v : Nat} {p : Bool} (h : (v,p)∈block 0 (ComparisonSignedWorlds.rawClause decoder c)) :
    v%2=0 := by
  obtain ⟨⟨u,q⟩,_,he⟩:=List.mem_map.mp (mem_block h)
  simp only [Prod.mk.injEq] at he
  rw [←he.2.1]
  exact rawAtom_even he.1

theorem block_imageClause (names : List Call) (literals : List (Call × Bool)) :
    block 0 (ComparisonSignedWorlds.imageClause names literals)=
      literals.map (fun l => (2*names.idxOf l.1+1,l.2)) := by
  induction literals with
  | nil => rfl
  | cons l ls ih => simpa [block,ComparisonSignedWorlds.imageClause] using congrArg (List.cons (2*names.idxOf l.1+1,l.2)) ih

theorem parseClause_imageClause {names : List Call} {literals : List (Call × Bool)}
    (h : ∀l∈literals,l.1∈names) :
    parseClause names ((block 0 (ComparisonSignedWorlds.imageClause names literals)).map
      (fun l=>(2*l.1,l.2)))=some ⟨[],literals⟩ := by
  rw [block_imageClause]
  simp only [List.map_map,Function.comp_def]
  induction literals with
  | nil => rfl
  | cons literal rest ih =>
    rcases literal with ⟨call,p⟩
    have hc:=h (call,p) (.head _)
    have ht:=ih (fun l hl=>h l (.tail _ hl))
    have hi:=List.idxOf_lt_length_of_mem hc
    have he : names[names.idxOf call]=call := by
      simpa only [List.idxOf,beq_iff_eq] using
        (List.findIdx_getElem (xs:=names) (p:=(·==call)) (w:=hi))
    have hd : 2*(2*names.idxOf call+1)/4=names.idxOf call := by omega
    have hm : isImage (2*(2*names.idxOf call+1))=true := by simp only [isImage,beq_iff_eq];omega
    simp only [List.map_cons,parseClause,ht,hm,if_true,hd,List.getElem?_eq_getElem hi,he]
    rfl

/-- The nominal parser retains exactly the original signed calls. Raw guards
and the constant world selector contribute no additional image literals. -/
theorem parse_selected {names : List Call} {literals : List (Call × Bool)}
    (h : ∀l∈literals,l.1∈names) (decoder : Nat → Nat × Nat)
    (guard : ModalityInference.Clause) (index : Nat) :
    ∃result,parseClause names (selected index 0
      (ComparisonSignedWorlds.rawClause decoder guard++ComparisonSignedWorlds.imageClause names literals))=
      some result ∧ result.literals=literals := by
  let guardPart : ModalityInference.Clause := (2*selectorAtom index 0+1,false)::
    (block 0 (ComparisonSignedWorlds.rawClause decoder guard)).map (fun l=>(2*l.1,l.2))
  have hp : ∀l∈guardPart,isImage l.1=false := by
    intro l hl
    rcases List.mem_cons.mp hl with rfl|hl
    · simp only [isImage,beq_eq_false_iff_ne]
      omega
    · obtain ⟨⟨v,p⟩,hm,he⟩:=List.mem_map.mp hl
      cases he
      have hv:=raw_block_even hm
      simp only [isImage,beq_eq_false_iff_ne]
      omega
  have he : selected index 0
      (ComparisonSignedWorlds.rawClause decoder guard++ComparisonSignedWorlds.imageClause names literals)=
      guardPart++((block 0 (ComparisonSignedWorlds.imageClause names literals)).map (fun l=>(2*l.1,l.2))) := by
    simp only [selected,block,List.filterMap_append,List.map_append,List.cons_append,guardPart]
  rw [he]
  exact ⟨_,parseClause_append (parseClause_guards hp) (parseClause_imageClause h),rfl⟩

theorem parse_correct {names : List Call} {cs : CNF} {result : List CompiledClause}
    (h : parse names cs=some result) (selectors world : Nat → Bool)
    (images : (Nat → Bool) → Call → Bool) :
    CNFHolds (encoded names selectors world images) cs ↔
      ∀c∈result,c.Holds (guardValue selectors world) (images world) := by
  induction cs generalizing result with
  | nil =>
    simp only [parse,Option.some.injEq] at h
    cases h
    simp [CNFHolds]
  | cons c cs ih =>
    cases hh:parseClause names c with
    | none => simp [parse,hh] at h
    | some head =>
      cases ht:parse names cs with
      | none => simp [parse,hh,ht] at h
      | some tail =>
        simp only [parse,hh,ht] at h
        cases h
        simp only [CNFHolds,List.forall_mem_cons]
        exact and_congr (parseClause_correct hh selectors world images) (ih ht)

theorem parse_complete {names : List Call} {cs : CNF}
    (h : ∀c∈cs,∃result,parseClause names c=some result) :
    ∃result,parse names cs=some result := by
  induction cs with
  | nil => exact ⟨[],rfl⟩
  | cons c cs ih =>
    obtain ⟨head,hh⟩:=h c (.head _)
    obtain ⟨tail,ht⟩:=ih (fun d hd=>h d (.tail _ hd))
    exact ⟨head::tail,by simp [parse,hh,ht]⟩

theorem parse_mem {names : List Call} {cs : CNF} {result : List CompiledClause}
    (h : parse names cs=some result) {c : CompiledClause} (hc : c∈result) :
    ∃original∈cs,parseClause names original=some c := by
  induction cs generalizing result with
  | nil => simp [parse] at h;subst result;cases hc
  | cons original rest ih =>
    cases hh:parseClause names original with
    | none => simp [parse,hh] at h
    | some head =>
      cases ht:parse names rest with
      | none => simp [parse,hh,ht] at h
      | some tail =>
        simp only [parse,hh,ht] at h
        cases h
        rcases List.mem_cons.mp hc with rfl|hc
        · exact ⟨original,.head _,hh⟩
        · obtain ⟨d,hd,he⟩:=ih ht hc
          exact ⟨d,.tail _ hd,he⟩

theorem nominal_clause_complete (decoder : Nat → Nat × Nat) (theory : CNF)
    (clauses : List CompiledClause) {c : ModalityInference.Clause}
    (hc : c∈nominal (ComparisonSignedWorlds.query decoder theory clauses)) :
    ∃result,parseClause (ComparisonSignedWorlds.calls clauses) c=some result ∧
      ∃original∈clauses,result.literals=original.literals := by
  obtain ⟨⟨worldClause,index⟩,hci,rfl⟩:=List.mem_map.mp hc
  have hw:=List.fst_mem_of_mem_zipIdx hci
  obtain ⟨original,ho,hw⟩:=List.mem_flatMap.mp hw
  obtain ⟨guard,_,he⟩:=List.mem_map.mp hw
  cases he
  obtain ⟨result,hr,hl⟩:=parse_selected (fun l hl=>ComparisonSignedWorlds.call_mem ho hl) decoder guard index
  exact ⟨result,hr,original,ho,hl⟩

/-- Every generated nominal clause decodes, preserving its original two-call
shape rather than introducing new occurrences during world separation. -/
theorem parse_nominal_complete (decoder : Nat → Nat × Nat) (theory : CNF)
    (clauses : List CompiledClause) :
    ∃result,parse (ComparisonSignedWorlds.calls clauses)
      (nominal (ComparisonSignedWorlds.query decoder theory clauses))=some result ∧
      ∀c∈result,∃original∈clauses,c.literals=original.literals := by
  obtain ⟨result,hr⟩:=parse_complete (fun c hc=>
    let h:=nominal_clause_complete decoder theory clauses hc
    ⟨h.choose,h.choose_spec.1⟩)
  refine ⟨result,hr,?_⟩
  intro c hc
  obtain ⟨original,ho,hp⟩:=parse_mem hr hc
  obtain ⟨parsed,hparsed,source,hs,he⟩:=nominal_clause_complete decoder theory clauses ho
  have heq : parsed=c := Option.some.inj (hparsed.symm.trans hp)
  subst parsed
  exact ⟨source,hs,he⟩

theorem prepare_complete (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (theory : CNF) (clauses : List CompiledClause) :
    ∃result,prepare size decoder theory clauses=some result ∧
      ∀c∈result,∃original∈clauses,c.literals=original.literals := by
  obtain ⟨result,hr,h⟩:=parse_nominal_complete (ComparisonSignedPoints.decode decoder)
    (ComparisonSignedPoints.theory (ComparisonSignedWorlds.calls clauses) size theory)
    (clauses.map ComparisonSignedPoints.clause)
  refine ⟨result,hr,?_⟩
  intro c hc
  obtain ⟨original,ho,he⟩:=h c hc
  obtain ⟨source,hs,rfl⟩:=List.mem_map.mp ho
  exact ⟨source,hs,he⟩

theorem prepare_binary {size : Nat → Nat} {decoder : Nat → Nat × Nat}
    {theory : CNF} {clauses result : List CompiledClause}
    (h : prepare size decoder theory clauses=some result)
    (hb : ∀c∈clauses,c.literals.length≤2) : ∀c∈result,c.literals.length≤2 := by
  obtain ⟨produced,hp,ho⟩:=prepare_complete size decoder theory clauses
  have he : produced=result := Option.some.inj (hp.symm.trans h)
  subst produced
  intro c hc
  obtain ⟨original,hm,he⟩:=ho c hc
  rw [he]
  exact hb original hm

theorem prepare_correct {size : Nat → Nat} {decoder : Nat → Nat × Nat}
    {theory : CNF} {clauses result : List CompiledClause}
    (h : prepare size decoder theory clauses=some result)
    (selectors world : Nat → Bool) (images : Nat → (Nat → Bool) → Bool) :
    CNFHolds
      (selectedValue (ComparisonWorldModes.worldChoice selectors)
        (ComparisonSignedStrategySynthesis.nominalValue size clauses images world))
      (ComparisonSignedStrategySynthesis.nominalQuery size decoder theory clauses) ↔
      ∀c∈result,c.Holds (guardValue selectors world)
        (ComparisonSignedPoints.nominalImages (ComparisonSignedWorlds.calls clauses) size images world) :=
  parse_correct h selectors world _

theorem guardDecode_value (selectors world : Nat → Bool) :
    ComparisonSignedEdges.decoded guardDecode selectors world=guardValue selectors world := by
  funext v
  by_cases hv:v%2=1 <;> simp [ComparisonSignedEdges.decoded,guardDecode,guardValue,hv]

theorem payload_value (names : List Call) (selectors world : Nat → Bool) (call : Call) (i : Nat) :
    ComparisonSignedEdges.decoded guardDecode selectors world (payload names call i)=
      world (ComparisonSignedPoints.pointAtom names call i) := by
  simp [ComparisonSignedEdges.decoded,guardDecode,payload]

theorem calls_clause_map (clauses : List CompiledClause) :
    ComparisonSignedWorlds.calls (clauses.map ComparisonSignedPoints.clause)=
      ComparisonSignedWorlds.calls clauses := by
  simp [ComparisonSignedWorlds.calls,List.flatMap_map,ComparisonSignedPoints.clause]

theorem prepare_origin {size : Nat → Nat} {decoder : Nat → Nat × Nat}
    {theory : CNF} {clauses result : List CompiledClause}
    (h : prepare size decoder theory clauses=some result) {c : CompiledClause} (hc : c∈result) :
    ∃original∈clauses,c.literals=original.literals := by
  obtain ⟨produced,hp,ho⟩:=prepare_complete size decoder theory clauses
  have he : produced=result := Option.some.inj (hp.symm.trans h)
  subst produced
  exact ho c hc

theorem prepare_allowed {size : Nat → Nat} {decoder : Nat → Nat × Nat}
    {theory : CNF} {clauses result : List CompiledClause} {allowed : Call → Prop}
    (h : prepare size decoder theory clauses=some result)
    (ha : ∀c∈clauses,∀l∈c.literals,allowed l.1) :
    ∀c∈result,∀l∈c.literals,allowed l.1 := by
  intro c hc l hl
  obtain ⟨original,ho,he⟩:=prepare_origin h hc
  exact ha original ho l (he ▸ hl)

end ModalityInference.ComparisonSignedNominal
