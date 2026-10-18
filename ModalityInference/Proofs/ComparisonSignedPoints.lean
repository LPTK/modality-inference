import ModalityInference.ComparisonSignedPoints
import ModalityInference.Proofs.ComparisonSignedWorlds

/-! Exact finite point abstraction for a shared image family. Independent
nominal point slots are tied to observed basis bits in the antecedent; lifting
or erasing those slots preserves every scalar world and its common strategy. -/
namespace ModalityInference.ComparisonSignedPoints
open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout
open ComparisonPropagation ComparisonWorldClauses

def basisPoint (size : Nat → Nat) (world : Nat → Bool) (call : Call) (i : Nat) : Bool :=
  if i<size call.name then world (routeAtom call.route (basisAtom i)) else false

def nominalPoint (names : List Call) (size : Nat → Nat) (world : Nat → Bool)
    (call : Call) (i : Nat) : Bool :=
  if i<size call.name then world (pointAtom names call i) else false

def basisImages (size : Nat → Nat) (images : Nat → (Nat → Bool) → Bool)
    (world : Nat → Bool) (call : Call) : Bool := images call.name (basisPoint size world call)

def nominalImages (names : List Call) (size : Nat → Nat)
    (images : Nat → (Nat → Bool) → Bool) (world : Nat → Bool) (call : Call) : Bool :=
  images call.name (nominalPoint names size world call)

def raw (decoder : Nat → Nat × Nat) (scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) : Nat → Bool :=
  ComparisonSignedWorlds.rawValue decoder (fun w=>w) scalar world

def eraseWorld (world : Nat → Nat → Bool) (b i : Nat) : Bool :=
  if b=0 then world 0 (2*i) else world b i

def extendWorld (names : List Call) (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (scalar : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool) (b i : Nat) : Bool :=
  if b=0 then
    if i%2=0 then world 0 (i/2)
    else match names[(Nat.unpair (i/2)).1]? with
      | none => false
      | some call => basisPoint size (raw decoder scalar world) call (Nat.unpair (i/2)).2
  else world b i

@[simp] theorem eraseWorld_ne (world : Nat → Nat → Bool) {b : Nat} (hb : b≠0) :
    eraseWorld world b=world b := funext fun i => by simp [eraseWorld,hb]

@[simp] theorem extendWorld_ne (names : List Call) (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (scalar : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool) {b : Nat} (hb : b≠0) :
    extendWorld names size decoder scalar world b=world b := funext fun i => by simp [extendWorld,hb]

theorem raw_source (decoder : Nat → Nat × Nat) (scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (v : Nat) :
    raw (decode decoder) scalar world (sourceAtom v)=raw decoder scalar (eraseWorld world) v := by
  by_cases hb:(decoder v).1=0
  · simp [raw,ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared,sourceAtom,decode,hb,eraseWorld]
  · simp [raw,ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared,sourceAtom,decode,hb]

theorem raw_point (decoder : Nat → Nat × Nat) (scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (names : List Call) (call : Call) (i : Nat) :
    raw (decode decoder) scalar world (pointAtom names call i)=world 0 (pointAtom names call i) := by
  simp [raw,ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared,pointAtom,decode]

theorem extend_source (names : List Call) (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (scalar : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool) (v : Nat) :
    raw (decode decoder) scalar (extendWorld names size decoder scalar world) (sourceAtom v)=
      raw decoder scalar world v := by
  by_cases hb:(decoder v).1=0
  · simp [raw,ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared,sourceAtom,decode,hb,extendWorld]
  · simp [raw,ComparisonSignedWorlds.rawValue,ComparisonWorldClauses.shared,sourceAtom,decode,hb]

theorem extend_point {names : List Call} {call : Call} (hc : call∈names)
    (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (scalar : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool) (i : Nat) :
    extendWorld names size decoder scalar world 0 (pointAtom names call i)=
      basisPoint size (raw decoder scalar world) call i := by
  have hi:=List.idxOf_lt_length_of_mem hc
  have he : names[names.idxOf call]=call := by
    simpa only [List.idxOf,beq_iff_eq] using
      (List.findIdx_getElem (xs:=names) (p:=(·==call)) (w:=hi))
  have hd : (2*Nat.pair (names.idxOf call) i+1)/2=Nat.pair (names.idxOf call) i := by omega
  simp [extendWorld,pointAtom,hd,Nat.unpair_pair,List.getElem?_eq_getElem hi,he]

theorem pointClauses_correct (names : List Call) (size : Nat → Nat) (world : Nat → Bool) :
    CNFHolds world (pointClauses names size) ↔
      ∀call∈names,∀i<size call.name,
        world (pointAtom names call i)=world (sourceAtom (routeAtom call.route (basisAtom i))) := by
  simp only [pointClauses,CNFHolds,List.forall_mem_flatMap,List.mem_range]
  apply forall_congr' fun call => imp_congr_right fun _ => forall_congr' fun i => imp_congr_right fun _ => ?_
  simp only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  have hn : ClauseHolds world [] ↔ False := by simp [ClauseHolds]
  simp only [clauseHolds_cons,hn,or_false]
  cases world (pointAtom names call i) <;> cases world (sourceAtom (routeAtom call.route (basisAtom i))) <;> simp

theorem clause_correct (c : CompiledClause) (world : Nat → Bool) (images : Call → Bool) :
    (clause c).Holds world images ↔ c.Holds (world ∘ sourceAtom) images := by
  change (ClauseHolds world (c.guard.map fun l => (sourceAtom l.1,l.2)) ∨ _) ↔ _
  have hm : ClauseHolds world (c.guard.map fun l => (sourceAtom l.1,l.2)) ↔
      ClauseHolds (world ∘ sourceAtom) c.guard := by
    simpa only [ComparisonPropagation.rename,CNFHolds,List.forall_mem_map,List.mem_singleton,forall_eq] using
      (rename_correct sourceAtom [c.guard] world)
  exact or_congr hm Iff.rfl

theorem images_congr {c : CompiledClause} {world : Nat → Bool} {left right : Call → Bool}
    (h : ∀literal∈c.literals,left literal.1=right literal.1) :
    c.Holds world left ↔ c.Holds world right := by
  constructor
  · rintro (hc|⟨literal,hl,hv⟩)
    · exact .inl hc
    · exact .inr ⟨literal,hl,(h literal hl).symm.trans hv⟩
  · rintro (hc|⟨literal,hl,hv⟩)
    · exact .inl hc
    · exact .inr ⟨literal,hl,(h literal hl).trans hv⟩

theorem erase_theory {names : List Call} {size : Nat → Nat} {decoder : Nat → Nat × Nat}
    {scalar : (Nat → Bool) → Nat → Bool} {world : Nat → Nat → Bool} {original : CNF}
    (h : CNFHolds (raw (decode decoder) scalar world) (theory names size original)) :
    CNFHolds (raw decoder scalar (eraseWorld world)) original := by
  have hh:=(rename_correct sourceAtom original _).mp (cnfHolds_append _ _ _ |>.mp h).1
  simpa only [Function.comp_def,raw_source] using hh

theorem nominalImages_eq {names : List Call} {call : Call} (hc : call∈names)
    (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (scalar : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool)
    (images : Nat → (Nat → Bool) → Bool)
    (h : CNFHolds (raw (decode decoder) scalar world) (pointClauses names size)) :
    nominalImages names size images (world 0) call=
      basisImages size images (raw decoder scalar (eraseWorld world)) call := by
  apply congrArg (images call.name)
  funext i
  by_cases hi:i<size call.name
  · simp only [nominalPoint,basisPoint,if_pos hi]
    exact (raw_point decoder scalar world names call i).symm.trans
      (((pointClauses_correct names size _).mp h call hc i hi).trans
        (raw_source decoder scalar world _))
  · simp only [nominalPoint,basisPoint,if_neg hi]

theorem extend_theory {names : List Call} {size : Nat → Nat} {decoder : Nat → Nat × Nat}
    {scalar : (Nat → Bool) → Nat → Bool} {world : Nat → Nat → Bool} {original : CNF}
    (h : CNFHolds (raw decoder scalar world) original) :
    CNFHolds (raw (decode decoder) scalar (extendWorld names size decoder scalar world))
      (theory names size original) := by
  apply (cnfHolds_append _ _ _).mpr
  constructor
  · apply (rename_correct sourceAtom original _).mpr
    simpa only [Function.comp_def,extend_source] using h
  · apply (pointClauses_correct names size _).mpr
    intro call hc i hi
    rw [raw_point,extend_point hc,extend_source]
    simp only [basisPoint,if_pos hi]

theorem extend_images {names : List Call} {call : Call} (hc : call∈names)
    (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (scalar : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool)
    (images : Nat → (Nat → Bool) → Bool) :
    nominalImages names size images (extendWorld names size decoder scalar world 0) call=
      basisImages size images (raw decoder scalar world) call := by
  apply congrArg (images call.name)
  funext i
  by_cases hi:i<size call.name
  · simp only [nominalPoint,basisPoint,if_pos hi,extend_point hc]
  · simp only [nominalPoint,basisPoint,if_neg hi]

/-- Point abstraction preserves one shared finite image family and one common
scalar strategy. The new nominal coordinates are universally quantified, and
are related to the actual route observations by the unchanged antecedent. -/
theorem abstract_valid (size : Nat → Nat) (decoder : Nat → Nat × Nat)
    (scalar : (Nat → Bool) → Nat → Bool) (images : Nat → (Nat → Bool) → Bool)
    (original : CNF) (clauses : List CompiledClause) :
    (∀world,∀c∈clauses,CNFHolds (raw decoder scalar world) original →
      c.Holds (raw decoder scalar world) (basisImages size images (raw decoder scalar world))) ↔
    (∀world,∀c∈clauses.map clause,
      CNFHolds (raw (decode decoder) scalar world)
        (theory (ComparisonSignedWorlds.calls clauses) size original) →
      c.Holds (raw (decode decoder) scalar world)
        (nominalImages (ComparisonSignedWorlds.calls clauses) size images (world 0))) := by
  constructor
  · intro h world c hc ht
    obtain ⟨originalClause,hmem,rfl⟩:=List.mem_map.mp hc
    rw [clause_correct]
    simp only [Function.comp_def,raw_source]
    apply (images_congr (fun l hl => nominalImages_eq
      (ComparisonSignedWorlds.call_mem hmem hl) size decoder scalar world images
      (cnfHolds_append _ _ _ |>.mp ht).2)).mpr
    exact h (eraseWorld world) originalClause hmem (erase_theory ht)
  · intro h world c hc ht
    have hh:=h (extendWorld (ComparisonSignedWorlds.calls clauses) size decoder scalar world)
      (clause c) (List.mem_map.mpr ⟨c,hc,rfl⟩) (extend_theory ht)
    rw [clause_correct] at hh
    simp only [Function.comp_def,extend_source] at hh
    exact (images_congr (fun l hl => extend_images
      (ComparisonSignedWorlds.call_mem hc hl) size decoder scalar world images)).mp hh

end ModalityInference.ComparisonSignedPoints
