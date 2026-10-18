import ModalityInference.Proofs.ComparisonWorldModes
import ModalityInference.Proofs.ComparisonWorldOffsets

/-! Clause-local nominal interpretations share a single scalar strategy.
This permits each endpoint query to keep its own observer namespace while all
its scalar obligations enter one common synthesis problem. -/
namespace ModalityInference.ComparisonIndexedWorldClauses
open ComparisonWorldClauses

abbrev Nominal := Nat → (Nat → Bool) → Nat → Bool

def Valid (nominal : Nominal) (scalar : (Nat → Bool) → Nat → Bool)
    (cs : List WorldClause) : Prop :=
  ∀ci∈cs.zipIdx,∀world,Holds (shared (nominal ci.2) scalar) ci.1 world

def NominalHolds (nominal : Nominal) (cs : List WorldClause) (choice : Nat → Bool) : Prop :=
  ∀ci∈cs.zipIdx,∀world,
    choice (selectorAtom ci.2 0)=false ∨ ClauseHolds (nominal ci.2 world) (block 0 ci.1)

def SelectedValid (nominal : Nominal) (scalar : (Nat → Bool) → Nat → Bool)
    (cs : List WorldClause) (choice : Nat → Bool) : Prop :=
  CNFHolds choice (choices cs) ∧ NominalHolds nominal cs choice ∧
    ∀world,CNFHolds (selectedValue choice (scalar world)) (ComparisonWorldClauses.scalar cs)

noncomputable def canonicalChoice (nominal : Nominal) (scalar : (Nat → Bool) → Nat → Bool)
    (cs : List WorldClause) (v : Nat) : Bool := by
  classical
  exact decide (∀world,ClauseHolds
    (shared (nominal (Nat.unpair v).1) scalar (Nat.unpair v).2 world)
    (block (Nat.unpair v).2 (cs[(Nat.unpair v).1]?.getD [])))

theorem canonicalChoice_correct (nominal : Nominal) (scalar : (Nat → Bool) → Nat → Bool)
    {cs : List WorldClause} {c : WorldClause} {i : Nat} (h : (c,i)∈cs.zipIdx) (b : Nat) :
    canonicalChoice nominal scalar cs (selectorAtom i b)=true ↔
      ∀world,ClauseHolds (shared (nominal i) scalar b world) (block b c) := by
  have he := List.mk_mem_zipIdx_iff_getElem?.mp h
  simp [canonicalChoice,selectorAtom,Nat.unpair_pair,he]

theorem selectors_complete {nominal : Nominal} {scalar : (Nat → Bool) → Nat → Bool}
    {cs : List WorldClause} (h : Valid nominal scalar cs) :
    SelectedValid nominal scalar cs (canonicalChoice nominal scalar cs) := by
  refine ⟨(choices_correct _ _).mpr ?_,?_,?_⟩
  · intro ci hci
    obtain ⟨b,hb⟩ := (clause_separation _ ci.1).mp (h ci hci)
    exact ⟨b,block_present (hb (fun _ => false)),(canonicalChoice_correct _ _ hci b).mpr hb⟩
  · intro ci hci world
    by_cases hc : canonicalChoice nominal scalar cs (selectorAtom ci.2 0)=true
    · right
      simpa only [shared,if_pos rfl] using ((canonicalChoice_correct _ _ hci 0).mp hc world)
    · exact .inl (Bool.eq_false_iff.mpr hc)
  · intro world
    apply (scalar_correct _ _ _).mpr
    intro ci hci b _ hb
    by_cases hc : canonicalChoice nominal scalar cs (selectorAtom ci.2 b)=true
    · right
      simpa only [shared,if_neg hb] using ((canonicalChoice_correct _ _ hci b).mp hc world)
    · exact .inl (Bool.eq_false_iff.mpr hc)

theorem selectors_sound {nominal : Nominal} {scalar : (Nat → Bool) → Nat → Bool}
    {cs : List WorldClause} {choice : Nat → Bool}
    (h : SelectedValid nominal scalar cs choice) : Valid nominal scalar cs := by
  intro ci hci world
  obtain ⟨b,hb,hchoice⟩ := (choices_correct _ _).mp h.1 ci hci
  apply (holds_blocks _ _ _).mpr
  refine ⟨b,?_⟩
  by_cases hz : b=0
  · subst b
    have hn := h.2.1 ci hci (world 0)
    simpa only [shared,if_pos rfl] using hn.resolve_left (by simp [hchoice])
  · have hs := (scalar_correct _ _ _).mp (h.2.2 (world b)) ci hci b hb hz
    simpa only [shared,if_neg hz] using hs.resolve_left (by simp [hchoice])

theorem selectors_iff (nominal : Nominal) (scalar : (Nat → Bool) → Nat → Bool)
    (cs : List WorldClause) :
    Valid nominal scalar cs ↔ ∃choice,SelectedValid nominal scalar cs choice :=
  ⟨fun h => ⟨_,selectors_complete h⟩,fun ⟨_,h⟩ => selectors_sound h⟩

/-- All scalar blocks are compiled together. In particular, the existential
modality strategy is outside the conjunction of local nominal interpretations. -/
theorem query_iff (side : Nat → Bool) (flex : List Nat) (cs : List WorldClause)
    (nominal : Nominal) :
    (∃selectors,CNFHolds selectors (ComparisonWorldModes.query side flex cs) ∧
      NominalHolds nominal cs (ComparisonWorldModes.worldChoice selectors)) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧ Valid nominal strategy cs := by
  constructor
  · rintro ⟨selectors,h,hn⟩
    refine ⟨_,ComparisonWorldModes.witness_uniform side flex cs selectors,
      selectors_sound (choice:=ComparisonWorldModes.worldChoice selectors) ?_⟩
    exact ⟨((ComparisonWorldModes.query_parts side flex cs selectors).mp h).1,
      hn,ComparisonWorldModes.witness_sound h⟩
  · rintro ⟨strategy,hu,h⟩
    obtain ⟨choice,hc,hn,hs⟩:=(selectors_iff nominal strategy cs).mp h
    obtain ⟨selectors,he,hq⟩:=ComparisonWorldModes.query_complete hu choice hc hs
    exact ⟨selectors,hq,he ▸ hn⟩

theorem constant_valid (nominal scalar : (Nat → Bool) → Nat → Bool) (cs : List WorldClause) :
    Valid (fun _=>nominal) scalar cs ↔ ComparisonWorldClauses.Valid nominal scalar cs := by
  constructor
  · intro h world c hc
    obtain ⟨i,hi,rfl⟩:=List.getElem_of_mem hc
    exact h (cs[i],i) (List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)) world
  · intro h ci hci world
    exact h world ci.1 (List.fst_mem_of_mem_zipIdx hci)

theorem constant_nominal (nominal : (Nat → Bool) → Nat → Bool) (cs : List WorldClause)
    (choice : Nat → Bool) :
    NominalHolds (fun _=>nominal) cs choice ↔
      ∀world,CNFHolds (selectedValue choice (nominal world)) (ComparisonWorldClauses.nominal cs) := by
  simp only [NominalHolds,nominal_correct]
  exact ⟨fun h world ci hci=>h ci hci world,fun h ci hci world=>h world ci hci⟩


theorem valid_congr {left right : Nominal} {scalar : (Nat → Bool) → Nat → Bool}
    {cs : List WorldClause} (h : ∀ci∈cs.zipIdx,left ci.2=right ci.2) :
    Valid left scalar cs ↔ Valid right scalar cs := by
  unfold Valid
  exact forall_congr' fun ci=>imp_congr_right fun hci=>by rw [h ci hci]

theorem nominal_congr {left right : Nominal} {cs : List WorldClause} {choice : Nat → Bool}
    (h : ∀ci∈cs.zipIdx,left ci.2=right ci.2) :
    NominalHolds left cs choice ↔ NominalHolds right cs choice := by
  unfold NominalHolds
  exact forall_congr' fun ci=>imp_congr_right fun hci=>by rw [h ci hci]

private theorem valid_shift (nominal : Nominal) (scalar : (Nat → Bool) → Nat → Bool)
    (cs : List WorldClause) (offset : Nat) :
    (∀ci∈cs.zipIdx offset,∀world,Holds (shared (nominal ci.2) scalar) ci.1 world) ↔
      Valid (fun i=>nominal (offset+i)) scalar cs := by
  rw [List.zipIdx_eq_map_add]
  simp only [List.forall_mem_map]
  rfl

private theorem nominal_shift (nominal : Nominal) (cs : List WorldClause)
    (choice : Nat → Bool) (offset : Nat) :
    (∀ci∈cs.zipIdx offset,∀world,
      choice (selectorAtom ci.2 0)=false ∨ ClauseHolds (nominal ci.2 world) (block 0 ci.1)) ↔
      NominalHolds (fun i=>nominal (offset+i)) cs
        (ComparisonWorldOffsets.shiftChoice offset choice) := by
  rw [List.zipIdx_eq_map_add]
  simp only [List.forall_mem_map,NominalHolds,ComparisonWorldOffsets.shiftChoice_selector]

theorem valid_append (nominal : Nominal) (scalar : (Nat → Bool) → Nat → Bool)
    (left right : List WorldClause) :
    Valid nominal scalar (left++right) ↔
      Valid nominal scalar left ∧ Valid (fun i=>nominal (left.length+i)) scalar right := by
  change (∀ci∈(left++right).zipIdx,_) ↔ _
  rw [List.zipIdx_append]
  simp only [List.forall_mem_append,Nat.zero_add]
  exact and_congr Iff.rfl (valid_shift nominal scalar right left.length)

theorem nominal_append (nominal : Nominal) (choice : Nat → Bool) (left right : List WorldClause) :
    NominalHolds nominal (left++right) choice ↔
      NominalHolds nominal left choice ∧ NominalHolds (fun i=>nominal (left.length+i)) right
        (ComparisonWorldOffsets.shiftChoice left.length choice) := by
  change (∀ci∈(left++right).zipIdx,_) ↔ _
  rw [List.zipIdx_append]
  simp only [List.forall_mem_append,Nat.zero_add]
  exact and_congr Iff.rfl (nominal_shift nominal right choice left.length)

abbrev Entry := ((Nat → Bool) → Nat → Bool) × List WorldClause

def batchNominal : List Entry → Nominal
  | [],_ => fun _ _=>false
  | (value,cs)::rest,i => if i<cs.length then value else batchNominal rest (i-cs.length)

def BatchNominalHolds : Nat → List Entry → (Nat → Bool) → Prop
  | _,[],_ => True
  | offset,(value,cs)::rest,choice =>
      (∀world,CNFHolds (selectedValue choice (value world)) (ComparisonWorldOffsets.nominal offset cs)) ∧
        BatchNominalHolds (offset+cs.length) rest choice

@[simp] theorem batchNominal_head {value : (Nat → Bool) → Nat → Bool} {cs : List WorldClause}
    {rest : List Entry} {i : Nat} (hi : i<cs.length) :
    batchNominal ((value,cs)::rest) i=value := by simp [batchNominal,hi]

@[simp] theorem batchNominal_tail (value : (Nat → Bool) → Nat → Bool) (cs : List WorldClause)
    (rest : List Entry) (i : Nat) :
    batchNominal ((value,cs)::rest) (cs.length+i)=batchNominal rest i := by
  simp [batchNominal,Nat.not_lt_of_ge (Nat.le_add_right cs.length i)]

theorem batch_valid (entries : List Entry) (scalar : (Nat → Bool) → Nat → Bool) :
    Valid (batchNominal entries) scalar (entries.flatMap Prod.snd) ↔
      ∀entry∈entries,ComparisonWorldClauses.Valid entry.1 scalar entry.2 := by
  induction entries with
  | nil => simp [Valid]
  | cons entry rest ih =>
    rcases entry with ⟨value,cs⟩
    rw [List.flatMap_cons,valid_append]
    have hl := valid_congr (scalar:=scalar) (cs:=cs) (left:=batchNominal ((value,cs)::rest))
      (right:=fun _=>value) (fun ci hci=>batchNominal_head (by simpa using List.snd_lt_of_mem_zipIdx hci))
    simp only [batchNominal_tail] at *
    rw [hl,constant_valid,ih]
    simp only [List.forall_mem_cons]

@[simp] theorem shiftChoice_zero (choice : Nat → Bool) :
    ComparisonWorldOffsets.shiftChoice 0 choice=choice := by
  funext v
  simp [ComparisonWorldOffsets.shiftChoice,selectorAtom]

@[simp] theorem shiftChoice_add (left right : Nat) (choice : Nat → Bool) :
    ComparisonWorldOffsets.shiftChoice right (ComparisonWorldOffsets.shiftChoice left choice)=
      ComparisonWorldOffsets.shiftChoice (left+right) choice := by
  funext v
  simp [ComparisonWorldOffsets.shiftChoice,selectorAtom,Nat.add_assoc]

theorem batch_nominal (entries : List Entry) (offset : Nat) (choice : Nat → Bool) :
    NominalHolds (batchNominal entries) (entries.flatMap Prod.snd)
      (ComparisonWorldOffsets.shiftChoice offset choice) ↔ BatchNominalHolds offset entries choice := by
  induction entries generalizing offset with
  | nil => simp [NominalHolds,BatchNominalHolds]
  | cons entry rest ih =>
    rcases entry with ⟨value,cs⟩
    rw [List.flatMap_cons,nominal_append]
    have hl := nominal_congr (cs:=cs)
      (choice:=ComparisonWorldOffsets.shiftChoice offset choice)
      (left:=batchNominal ((value,cs)::rest)) (right:=fun _=>value)
      (fun ci hci=>batchNominal_head (by simpa using List.snd_lt_of_mem_zipIdx hci))
    simp only [batchNominal_tail,shiftChoice_add]
    rw [hl,constant_nominal,ih]
    change ((_ ∧ _) ↔ (_ ∧ _))
    apply and_congr_left
    intro _
    apply forall_congr' fun world=>?_
    exact (ComparisonWorldOffsets.nominal_correct offset choice (value world) cs).symm

/-- Separate nominal namespaces are retained, but scalar obligations from the
entire batch are solved together by one uniform strategy. -/
theorem batch_query_iff (side : Nat → Bool) (flex : List Nat) (entries : List Entry) :
    (∃selectors,CNFHolds selectors
        (ComparisonWorldModes.query side flex (entries.flatMap Prod.snd)) ∧
      BatchNominalHolds 0 entries (ComparisonWorldModes.worldChoice selectors)) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        ∀entry∈entries,ComparisonWorldClauses.Valid entry.1 strategy entry.2 := by
  have h := query_iff side flex (entries.flatMap Prod.snd) (batchNominal entries)
  simpa only [batch_valid,←batch_nominal entries 0,shiftChoice_zero] using h

end ModalityInference.ComparisonIndexedWorldClauses
