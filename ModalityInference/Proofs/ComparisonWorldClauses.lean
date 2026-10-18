import ModalityInference.ComparisonWorldClauses
import ModalityInference.Proofs.ComparisonJointClauses

/-! Constant selectors separate universal clauses over independent raw worlds.
The interpretation of every block is fixed before separation; repeated scalar
worlds may therefore use one common modality strategy. -/
namespace ModalityInference.ComparisonWorldClauses

theorem independent_clause {B : Type*} {W : B → Type*}
    (P : ∀b,W b → Prop) :
    (∀world : ∀b,W b, ∃b,P b (world b)) ↔ ∃b,∀w,P b w := by
  classical
  constructor
  · intro h
    by_contra hn
    have hb : ∀b,∃w,¬P b w := by
      intro b
      simpa only [not_forall] using (not_exists.mp hn b)
    choose world hw using hb
    obtain ⟨b,hb⟩ := h world
    exact hw b hb
  · rintro ⟨b,hb⟩ world
    exact ⟨b,hb _⟩

/-- One selector is chosen for a complete clause, independently of every input
valuation. Any strategy captured by `P` is retained literally on both sides. -/
theorem independent_clauses {C B : Type*} {W : B → Type*}
    (P : C → ∀b,W b → Prop) :
    (∀world : ∀b,W b, ∀c, ∃b,P c b (world b)) ↔
      ∃select : C → B, ∀c w,P c (select c) w := by
  classical
  constructor
  · intro h
    have hc : ∀c,∃b,∀w,P c b w := fun c =>
      (independent_clause (P c)).mp (fun world => h world c)
    exact Classical.skolem.mp hc
  · rintro ⟨select,h⟩ world c
    exact ⟨select c,h c _⟩

def Holds (realize : Nat → (Nat → Bool) → Nat → Bool)
    (c : WorldClause) (world : Nat → Nat → Bool) : Prop :=
  ∃literal∈c,realize literal.1 (world literal.1) literal.2.1=literal.2.2

theorem block_holds (b : Nat) (c : WorldClause) (value : Nat → Bool) :
    ClauseHolds value (block b c) ↔
      ∃literal∈c,literal.1=b ∧ value literal.2.1=literal.2.2 := by
  simp only [ClauseHolds,block,List.mem_filterMap]
  constructor
  · rintro ⟨v,p,⟨source,hs,he⟩,hv⟩
    split at he
    next hb =>
      have he' : source.2=(v,p) := Option.some.inj he
      exact ⟨source,hs,hb,by simpa only [he'] using hv⟩
    next => cases he
  · rintro ⟨literal,hl,hb,hv⟩
    exact ⟨literal.2.1,literal.2.2,⟨literal,hl,by simp [hb]⟩,hv⟩

theorem holds_blocks (realize : Nat → (Nat → Bool) → Nat → Bool)
    (c : WorldClause) (world : Nat → Nat → Bool) :
    Holds realize c world ↔ ∃b,ClauseHolds (realize b (world b)) (block b c) := by
  constructor
  · rintro ⟨literal,hl,hv⟩
    exact ⟨literal.1,(block_holds _ _ _).mpr ⟨literal,hl,rfl,hv⟩⟩
  · rintro ⟨b,h⟩
    obtain ⟨literal,hl,hb,hv⟩ := (block_holds _ _ _).mp h
    exact ⟨literal,hl,by simpa only [hb] using hv⟩

theorem clause_separation (realize : Nat → (Nat → Bool) → Nat → Bool)
    (c : WorldClause) :
    (∀world,Holds realize c world) ↔
      ∃b,∀w,ClauseHolds (realize b w) (block b c) := by
  simp only [holds_blocks]
  exact independent_clause (W := fun _ : Nat => Nat → Bool)
    (fun b w => ClauseHolds (realize b w) (block b c))

/-- World zero is nominal. Every other world is interpreted by the same
strategy on the same canonical input domain after separation. -/
def shared (nominal scalar : (Nat → Bool) → Nat → Bool)
    (b : Nat) : (Nat → Bool) → Nat → Bool := if b=0 then nominal else scalar

theorem shared_clause_separation (nominal scalar : (Nat → Bool) → Nat → Bool)
    (c : WorldClause) :
    (∀world,Holds (shared nominal scalar) c world) ↔
      (∀w,ClauseHolds (nominal w) (block 0 c)) ∨
        ∃b,b≠0 ∧ ∀w,ClauseHolds (scalar w) (block b c) := by
  rw [clause_separation]
  constructor
  · rintro ⟨b,h⟩
    by_cases hb : b=0
    · subst b
      exact .inl (by simpa only [shared,if_pos rfl] using h)
    · exact .inr ⟨b,hb,by simpa only [shared,if_neg hb] using h⟩
  · rintro (h|⟨b,hb,h⟩)
    · exact ⟨0,by simpa only [shared,if_pos rfl] using h⟩
    · exact ⟨b,by simpa only [shared,if_neg hb] using h⟩

def selectedValue (choice value : Nat → Bool) (v : Nat) : Bool :=
  if v%2=0 then value (v/2) else choice (v/2)

@[simp] theorem selectedValue_even (choice value : Nat → Bool) (v : Nat) :
    selectedValue choice value (2*v)=value v := by simp [selectedValue]

@[simp] theorem selectedValue_odd (choice value : Nat → Bool) (v : Nat) :
    selectedValue choice value (2*v+1)=choice v := by
  have he : (2*v+1)/2=v := by omega
  simp [selectedValue,he]

theorem selected_correct (choice value : Nat → Bool) (i b : Nat) (c : WorldClause) :
    ClauseHolds (selectedValue choice value) (selected i b c) ↔
      choice (selectorAtom i b)=false ∨ ClauseHolds value (block b c) := by
  rw [selected,clauseHolds_cons,selectedValue_odd]
  apply or_congr_right
  constructor
  · rintro ⟨v,p,h,hv⟩
    obtain ⟨⟨w,q⟩,hw,he⟩ := List.mem_map.mp h
    cases he
    exact ⟨w,p,hw,by simpa using hv⟩
  · rintro ⟨v,p,h,hv⟩
    exact ⟨2*v,p,List.mem_map.mpr ⟨(v,p),h,rfl⟩,by simpa using hv⟩

theorem choices_correct (choice : Nat → Bool) (cs : List WorldClause) :
    CNFHolds choice (choices cs) ↔
      ∀ci∈cs.zipIdx,∃b∈blocks ci.1,choice (selectorAtom ci.2 b)=true := by
  simp only [choices,CNFHolds,List.forall_mem_map]
  apply forall_congr' fun ci => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨v,p,h,hv⟩
    obtain ⟨b,hb,he⟩ := List.mem_map.mp h
    cases he
    exact ⟨b,hb,hv⟩
  · rintro ⟨b,hb,hv⟩
    exact ⟨selectorAtom ci.2 b,true,List.mem_map.mpr ⟨b,hb,rfl⟩,hv⟩

theorem nominal_correct (choice value : Nat → Bool) (cs : List WorldClause) :
    CNFHolds (selectedValue choice value) (nominal cs) ↔
      ∀ci∈cs.zipIdx,choice (selectorAtom ci.2 0)=false ∨ ClauseHolds value (block 0 ci.1) := by
  simp only [nominal,CNFHolds,List.forall_mem_map,selected_correct]

theorem scalar_correct (choice value : Nat → Bool) (cs : List WorldClause) :
    CNFHolds (selectedValue choice value) (scalar cs) ↔
      ∀ci∈cs.zipIdx,∀b∈blocks ci.1,b≠0 →
        choice (selectorAtom ci.2 b)=false ∨ ClauseHolds value (block b ci.1) := by
  simp only [scalar,CNFHolds,List.forall_mem_flatMap,List.forall_mem_map,
    List.mem_filter,bne_iff_ne,selected_correct]
  simp only [and_imp]

theorem block_present {b : Nat} {c : WorldClause} {value : Nat → Bool}
    (h : ClauseHolds value (block b c)) : b∈blocks c := by
  obtain ⟨l,hl,hb,_⟩ := (block_holds b c value).mp h
  simp only [blocks,List.mem_dedup,List.mem_map]
  exact ⟨l,hl,hb⟩

def Valid (nominal scalar : (Nat → Bool) → Nat → Bool) (cs : List WorldClause) : Prop :=
  ∀world,∀c∈cs,Holds (shared nominal scalar) c world

def SelectedValid (nominalValue scalarValue : (Nat → Bool) → Nat → Bool)
    (cs : List WorldClause) (choice : Nat → Bool) : Prop :=
  CNFHolds choice (choices cs) ∧
    (∀w,CNFHolds (selectedValue choice (nominalValue w)) (nominal cs)) ∧
    (∀w,CNFHolds (selectedValue choice (scalarValue w)) (scalar cs))

noncomputable def canonicalChoice (nominal scalar : (Nat → Bool) → Nat → Bool)
    (cs : List WorldClause) (v : Nat) : Bool := by
  classical
  exact decide (∀w,ClauseHolds (shared nominal scalar (Nat.unpair v).2 w)
    (block (Nat.unpair v).2 (cs[(Nat.unpair v).1]?.getD [])))

theorem canonicalChoice_correct (nominal scalar : (Nat → Bool) → Nat → Bool)
    {cs : List WorldClause} {c : WorldClause} {i : Nat} (h : (c,i)∈cs.zipIdx) (b : Nat) :
    canonicalChoice nominal scalar cs (selectorAtom i b)=true ↔
      ∀w,ClauseHolds (shared nominal scalar b w) (block b c) := by
  have he := List.mk_mem_zipIdx_iff_getElem?.mp h
  simp [canonicalChoice,selectorAtom,Nat.unpair_pair,he]

theorem selectors_complete {nominalValue scalarValue : (Nat → Bool) → Nat → Bool}
    {cs : List WorldClause} (h : Valid nominalValue scalarValue cs) :
    SelectedValid nominalValue scalarValue cs (canonicalChoice nominalValue scalarValue cs) := by
  refine ⟨(choices_correct _ _).mpr ?_,?_,?_⟩
  · intro ci hci
    obtain ⟨b,hb⟩ := (clause_separation _ ci.1).mp
      (fun world => h world ci.1 (List.fst_mem_of_mem_zipIdx hci))
    exact ⟨b,block_present (hb (fun _ => false)),(canonicalChoice_correct _ _ hci b).mpr hb⟩
  · intro w
    apply (nominal_correct _ _ _).mpr
    intro ci hci
    by_cases hc : canonicalChoice nominalValue scalarValue cs (selectorAtom ci.2 0)=true
    · right
      simpa only [shared,if_pos rfl] using ((canonicalChoice_correct _ _ hci 0).mp hc w)
    · exact .inl (Bool.eq_false_iff.mpr hc)
  · intro w
    apply (scalar_correct _ _ _).mpr
    intro ci hci b _ hb
    by_cases hc : canonicalChoice nominalValue scalarValue cs (selectorAtom ci.2 b)=true
    · right
      simpa only [shared,if_neg hb] using ((canonicalChoice_correct _ _ hci b).mp hc w)
    · exact .inl (Bool.eq_false_iff.mpr hc)

theorem selectors_sound {nominalValue scalarValue : (Nat → Bool) → Nat → Bool}
    {cs : List WorldClause} {choice : Nat → Bool}
    (h : SelectedValid nominalValue scalarValue cs choice) : Valid nominalValue scalarValue cs := by
  intro world c hc
  obtain ⟨i,hi⟩ := List.mem_iff_getElem.mp hc
  have hci : (c,i)∈cs.zipIdx := List.mk_mem_zipIdx_iff_getElem?.mpr
    (by simpa only [hi.2] using List.getElem?_eq_getElem hi.1)
  obtain ⟨b,hb,hchoice⟩ := (choices_correct _ _).mp h.1 (c,i) hci
  apply (holds_blocks _ _ _).mpr
  refine ⟨b,?_⟩
  by_cases hz : b=0
  · subst b
    have hn := (nominal_correct _ _ _).mp (h.2.1 (world 0)) (c,i) hci
    simpa only [shared,if_pos rfl] using hn.resolve_left (by simp [hchoice])
  · have hs := (scalar_correct _ _ _).mp (h.2.2 (world b)) (c,i) hci b hb hz
    simpa only [shared,if_neg hz] using hs.resolve_left (by simp [hchoice])

/-- The compiled selector, nominal and scalar clauses preserve one common
strategy exactly. Scalar worlds are reindexed before the single scalar solve. -/
theorem selectors_iff (nominal scalar : (Nat → Bool) → Nat → Bool) (cs : List WorldClause) :
    Valid nominal scalar cs ↔ ∃choice,SelectedValid nominal scalar cs choice :=
  ⟨fun h => ⟨_,selectors_complete h⟩,fun ⟨_,h⟩ => selectors_sound h⟩

end ModalityInference.ComparisonWorldClauses
