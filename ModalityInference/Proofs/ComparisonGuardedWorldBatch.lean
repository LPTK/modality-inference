import ModalityInference.Proofs.ComparisonGuardedWorldModes

namespace ModalityInference.ComparisonGuardedWorldModes
open ComparisonWorldClauses

theorem valid_congr {left right : ComparisonIndexedWorldClauses.Nominal}
    {shape : Nat → Bool} {strategy : (Nat → Bool) → Nat → Bool} {entries : List Entry}
    (h : ∀ei∈entries.zipIdx,left ei.2=right ei.2) :
    Valid left shape strategy entries ↔ Valid right shape strategy entries := by
  unfold Valid
  exact forall_congr' fun ei=>imp_congr_right fun hei=>by rw [h ei hei]

theorem nominal_congr {left right : ComparisonIndexedWorldClauses.Nominal}
    {shape choice : Nat → Bool} {entries : List Entry}
    (h : ∀ei∈entries.zipIdx,left ei.2=right ei.2) :
    NominalHolds left shape choice entries ↔ NominalHolds right shape choice entries := by
  unfold NominalHolds
  exact forall_congr' fun ei=>imp_congr_right fun hei=>by rw [h ei hei]

private theorem valid_shift (nominal : ComparisonIndexedWorldClauses.Nominal) (shape : Nat → Bool)
    (strategy : (Nat → Bool) → Nat → Bool) (entries : List Entry) (offset : Nat) :
    (∀ei∈entries.zipIdx offset,¬ClauseHolds shape ei.1.guard →
      ∀world,Holds (shared (nominal ei.2) strategy) ei.1.clause world) ↔
      Valid (fun i=>nominal (offset+i)) shape strategy entries := by
  rw [List.zipIdx_eq_map_add]
  simp only [List.forall_mem_map]
  rfl

private theorem nominal_shift (nominal : ComparisonIndexedWorldClauses.Nominal)
    (shape choice : Nat → Bool) (entries : List Entry) (offset : Nat) :
    (∀ei∈entries.zipIdx offset,¬ClauseHolds shape ei.1.guard → ∀world,
      choice (selectorAtom ei.2 0)=false ∨ ClauseHolds (nominal ei.2 world) (block 0 ei.1.clause)) ↔
      NominalHolds (fun i=>nominal (offset+i)) shape
        (ComparisonWorldOffsets.shiftChoice offset choice) entries := by
  rw [List.zipIdx_eq_map_add]
  simp only [List.forall_mem_map,NominalHolds,ComparisonWorldOffsets.shiftChoice_selector]

theorem valid_append (nominal : ComparisonIndexedWorldClauses.Nominal) (shape : Nat → Bool)
    (strategy : (Nat → Bool) → Nat → Bool) (left right : List Entry) :
    Valid nominal shape strategy (left++right) ↔
      Valid nominal shape strategy left ∧
        Valid (fun i=>nominal (left.length+i)) shape strategy right := by
  change (∀ei∈(left++right).zipIdx,_) ↔ _
  rw [List.zipIdx_append]
  simp only [List.forall_mem_append,Nat.zero_add]
  exact and_congr Iff.rfl (valid_shift nominal shape strategy right left.length)

theorem nominal_append (nominal : ComparisonIndexedWorldClauses.Nominal) (shape choice : Nat → Bool)
    (left right : List Entry) :
    NominalHolds nominal shape choice (left++right) ↔
      NominalHolds nominal shape choice left ∧
        NominalHolds (fun i=>nominal (left.length+i)) shape
          (ComparisonWorldOffsets.shiftChoice left.length choice) right := by
  change (∀ei∈(left++right).zipIdx,_) ↔ _
  rw [List.zipIdx_append]
  simp only [List.forall_mem_append,Nat.zero_add]
  exact and_congr Iff.rfl (nominal_shift nominal shape choice right left.length)

def guarded (guard : Clause) (cs : List WorldClause) : List Entry :=
  cs.map fun c=>⟨guard,c⟩

@[simp] theorem guarded_length (guard : Clause) (cs : List WorldClause) :
    (guarded guard cs).length=cs.length := List.length_map _

theorem guarded_valid (guard : Clause) (cs : List WorldClause)
    (nominal strategy : (Nat → Bool) → Nat → Bool) (shape : Nat → Bool) :
    Valid (fun _=>nominal) shape strategy (guarded guard cs) ↔
      (¬ClauseHolds shape guard → ComparisonWorldClauses.Valid nominal strategy cs) := by
  rw [←ComparisonIndexedWorldClauses.constant_valid]
  simp only [Valid,guarded,List.zipIdx_map,List.forall_mem_map,ComparisonIndexedWorldClauses.Valid]
  exact ⟨fun h hg ci hci world=>h ci hci hg world,
    fun h ci hci hg world=>h hg ci hci world⟩

theorem guarded_nominal (guard : Clause) (cs : List WorldClause)
    (nominal : (Nat → Bool) → Nat → Bool) (shape choice : Nat → Bool) :
    NominalHolds (fun _=>nominal) shape choice (guarded guard cs) ↔
      (¬ClauseHolds shape guard → ∀world,
        CNFHolds (selectedValue choice (nominal world)) (ComparisonWorldClauses.nominal cs)) := by
  rw [←ComparisonIndexedWorldClauses.constant_nominal]
  simp only [NominalHolds,guarded,List.zipIdx_map,List.forall_mem_map,
    ComparisonIndexedWorldClauses.NominalHolds]
  exact ⟨fun h hg ci hci world=>h ci hci hg world,
    fun h ci hci hg world=>h hg ci hci world⟩

structure Group where
  guard : Clause
  nominal : (Nat → Bool) → Nat → Bool
  clauses : List WorldClause

def batch (groups : List Group) : List Entry :=
  groups.flatMap fun group=>guarded group.guard group.clauses

def batchNominal (groups : List Group) : ComparisonIndexedWorldClauses.Nominal :=
  ComparisonIndexedWorldClauses.batchNominal (groups.map fun group=>(group.nominal,group.clauses))

def BatchNominalHolds : Nat → List Group → (Nat → Bool) → (Nat → Bool) → Prop
  | _,[],_,_ => True
  | offset,group::groups,shape,choice =>
      (¬ClauseHolds shape group.guard → ∀world,
        CNFHolds (selectedValue choice (group.nominal world))
          (ComparisonWorldOffsets.nominal offset group.clauses)) ∧
      BatchNominalHolds (offset+group.clauses.length) groups shape choice

@[simp] theorem batchNominal_head {group : Group} {groups : List Group} {i : Nat}
    (hi : i<group.clauses.length) : batchNominal (group::groups) i=group.nominal := by
  simp [batchNominal,hi]

@[simp] theorem batchNominal_tail (group : Group) (groups : List Group) (i : Nat) :
    batchNominal (group::groups) (group.clauses.length+i)=batchNominal groups i := by
  simp [batchNominal]

theorem batch_valid (groups : List Group) (shape : Nat → Bool)
    (strategy : (Nat → Bool) → Nat → Bool) :
    Valid (batchNominal groups) shape strategy (batch groups) ↔
      ∀group∈groups,¬ClauseHolds shape group.guard →
        ComparisonWorldClauses.Valid group.nominal strategy group.clauses := by
  induction groups with
  | nil => simp [Valid,batch]
  | cons group groups ih =>
    change Valid _ _ _ (guarded group.guard group.clauses++batch groups) ↔ _
    rw [valid_append]
    have hl:=valid_congr (shape:=shape) (strategy:=strategy)
      (entries:=guarded group.guard group.clauses)
      (left:=batchNominal (group::groups)) (right:=fun _=>group.nominal) (fun ei hei=>
        batchNominal_head (by simpa [guarded] using List.snd_lt_of_mem_zipIdx hei))
    simp only [guarded_length,batchNominal_tail] at *
    rw [hl,guarded_valid,ih]
    simp only [List.forall_mem_cons]

theorem batch_nominal (groups : List Group) (offset : Nat) (shape choice : Nat → Bool) :
    NominalHolds (batchNominal groups) shape (ComparisonWorldOffsets.shiftChoice offset choice) (batch groups) ↔
      BatchNominalHolds offset groups shape choice := by
  induction groups generalizing offset with
  | nil => simp [NominalHolds,batch,BatchNominalHolds]
  | cons group groups ih =>
    change NominalHolds _ _ _ (guarded group.guard group.clauses++batch groups) ↔ _
    rw [nominal_append]
    have hl:=nominal_congr (shape:=shape)
      (choice:=ComparisonWorldOffsets.shiftChoice offset choice)
      (entries:=guarded group.guard group.clauses)
      (left:=batchNominal (group::groups)) (right:=fun _=>group.nominal) (fun ei hei=>
        batchNominal_head (by simpa [guarded] using List.snd_lt_of_mem_zipIdx hei))
    simp only [guarded_length,batchNominal_tail,ComparisonIndexedWorldClauses.shiftChoice_add]
    rw [hl,guarded_nominal,ih]
    change ((_ ∧ _) ↔ (_ ∧ _))
    apply and_congr_left
    intro _
    apply imp_congr_right
    intro _
    apply forall_congr' fun world=>?_
    exact (ComparisonWorldOffsets.nominal_correct offset choice (group.nominal world) group.clauses).symm

/-- Local nominal namespaces and guarded activation share one exact external
constant valuation and one scalar strategy across the entire batch. -/
theorem batch_query_iff (side : Nat → Bool) (flex : List Nat) (groups : List Group) (shape : Nat → Bool) :
    (∃selectors,externalValue (batch groups).length selectors=shape ∧
      CNFHolds selectors (query side flex (batch groups)) ∧
      BatchNominalHolds 0 groups shape (ComparisonWorldModes.worldChoice selectors)) ↔
      ∃strategy,ModalSynthesis.Uniform side flex strategy ∧
        ∀group∈groups,¬ClauseHolds shape group.guard →
          ComparisonWorldClauses.Valid group.nominal strategy group.clauses := by
  have h:=query_iff side flex (batch groups) (batchNominal groups) shape
  simpa only [batch_valid,←batch_nominal groups 0,ComparisonIndexedWorldClauses.shiftChoice_zero] using h

end ModalityInference.ComparisonGuardedWorldModes
