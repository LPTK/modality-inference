import ModalityInference.ComparisonSignedWorlds
import ModalityInference.Proofs.ComparisonSignedEndpoints
import ModalityInference.Proofs.ComparisonWorldClauses

/-! World-tagged guarded endpoint clauses retain point-equality hypotheses before
separating independent raw inputs. All image observations use one nominal family,
and every scalar block uses the same strategy. -/
namespace ModalityInference.ComparisonSignedWorlds
open ComparisonSignedEndpoints ComparisonWorldClauses ComparisonPropagation

deriving instance ReflBEq, LawfulBEq for Call

def nominalValue (names : List Call) (nominal : (Nat → Bool) → Nat → Bool)
    (images : (Nat → Bool) → Call → Bool) (world : Nat → Bool) (v : Nat) : Bool :=
  if v%2=0 then nominal world (v/2)
  else ((names[v/2]?).map (images world)).getD false

@[simp] theorem nominal_even (names : List Call) (nominal : (Nat → Bool) → Nat → Bool)
    (images : (Nat → Bool) → Call → Bool) (world : Nat → Bool) (v : Nat) :
    nominalValue names nominal images world (2*v)=nominal world v := by simp [nominalValue]

theorem nominal_image {names : List Call} {call : Call} (hc : call∈names)
    (nominal : (Nat → Bool) → Nat → Bool) (images : (Nat → Bool) → Call → Bool)
    (world : Nat → Bool) :
    nominalValue names nominal images world (2*names.idxOf call+1)=images world call := by
  have hi:=List.idxOf_lt_length_of_mem hc
  have he : names[names.idxOf call]=call := by
    simpa only [List.idxOf,beq_iff_eq] using
      (List.findIdx_getElem (xs:=names) (p:=(·==call)) (w:=hi))
  have hd : (2*names.idxOf call+1)/2=names.idxOf call := by omega
  simp [nominalValue,hd,List.getElem?_eq_getElem hi,he]

def rawValue (decode : Nat → Nat × Nat) (nominal scalar : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (v : Nat) : Bool :=
  ComparisonWorldClauses.shared nominal scalar (decode v).1 (world (decode v).1) (decode v).2

theorem rawAtom_value (decode : Nat → Nat × Nat) (names : List Call)
    (nominal scalar : (Nat → Bool) → Nat → Bool) (images : (Nat → Bool) → Call → Bool)
    (world : Nat → Nat → Bool) (v : Nat) :
    ComparisonWorldClauses.shared (nominalValue names nominal images) scalar
      (rawAtom decode v).1 (world (rawAtom decode v).1) (rawAtom decode v).2=
        rawValue decode nominal scalar world v := by
  by_cases h:(decode v).1=0
  · simp [rawAtom,h,rawValue,ComparisonWorldClauses.shared]
  · simp [rawAtom,h,rawValue,ComparisonWorldClauses.shared]

theorem holds_append (realize : Nat → (Nat → Bool) → Nat → Bool)
    (left right : WorldClause) (world : Nat → Nat → Bool) :
    Holds realize (left++right) world ↔ Holds realize left world ∨ Holds realize right world := by
  simp only [Holds,List.mem_append]
  aesop

theorem rawClause_correct (decode : Nat → Nat × Nat) (names : List Call)
    (nominal scalar : (Nat → Bool) → Nat → Bool) (images : (Nat → Bool) → Call → Bool)
    (world : Nat → Nat → Bool) (clause : ModalityInference.Clause) :
    Holds (ComparisonWorldClauses.shared (nominalValue names nominal images) scalar)
      (rawClause decode clause) world ↔ ClauseHolds (rawValue decode nominal scalar world) clause := by
  simp only [Holds,rawClause,List.mem_map]
  constructor
  · rintro ⟨literal,⟨⟨v,p⟩,hp,rfl⟩,hv⟩
    exact ⟨v,p,hp,(rawAtom_value decode names nominal scalar images world v).symm.trans hv⟩
  · rintro ⟨v,p,hp,hv⟩
    exact ⟨_,⟨(v,p),hp,rfl⟩,(rawAtom_value decode names nominal scalar images world v).trans hv⟩

theorem imageClause_correct {names : List Call} {literals : List (Call × Bool)}
    (hc : ∀l∈literals,l.1∈names)
    (nominal scalar : (Nat → Bool) → Nat → Bool) (images : (Nat → Bool) → Call → Bool)
    (world : Nat → Nat → Bool) :
    Holds (ComparisonWorldClauses.shared (nominalValue names nominal images) scalar)
      (imageClause names literals) world ↔ ∃l∈literals,images (world 0) l.1=l.2 := by
  simp only [Holds,imageClause,List.mem_map]
  constructor
  · rintro ⟨literal,⟨⟨call,p⟩,hp,rfl⟩,hv⟩
    exact ⟨(call,p),hp,(nominal_image (hc (call,p) hp) nominal images (world 0)).symm.trans hv⟩
  · rintro ⟨⟨call,p⟩,hp,hv⟩
    exact ⟨_,⟨(call,p),hp,rfl⟩,(nominal_image (hc (call,p) hp) nominal images (world 0)).trans hv⟩

theorem call_mem {clauses : List CompiledClause} {clause : CompiledClause}
    (hc : clause∈clauses) {literal : Call × Bool} (hl : literal∈clause.literals) :
    literal.1∈calls clauses := by
  exact List.mem_dedup.mpr (List.mem_flatMap.mpr
    ⟨clause,hc,List.mem_map.mpr ⟨literal,hl,rfl⟩⟩)

theorem query_correct (decode : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause)
    (nominal scalar : (Nat → Bool) → Nat → Bool) (images : (Nat → Bool) → Call → Bool)
    (world : Nat → Nat → Bool) :
    (∀clause∈query decode theory clauses,
      Holds (ComparisonWorldClauses.shared (nominalValue (calls clauses) nominal images) scalar) clause world) ↔
      ∀clause∈clauses,CNFHolds (rawValue decode nominal scalar world) theory →
        clause.Holds (rawValue decode nominal scalar world) (images (world 0)) := by
  classical
  simp only [query,List.forall_mem_flatMap,List.forall_mem_map]
  apply forall_congr' fun clause => imp_congr_right fun hc => ?_
  simp only [holds_append,rawClause_correct,imageClause_correct (fun l hl => call_mem hc hl)]
  by_cases hi:∃l∈clause.literals,images (world 0) l.1=l.2
  · simp only [hi,or_true,implies_true,CompiledClause.Holds]
  · simp only [hi,or_false,CompiledClause.Holds]
    change CNFHolds (rawValue decode nominal scalar world) (implies theory [clause.guard]) ↔ _
    rw [implies_correct]
    simp only [CNFHolds,List.mem_singleton,forall_eq]

/-- The implication is compiled before its raw atoms are assigned to worlds.
In particular, equations relating independent image points to actual basis
observations remain part of the same antecedent. -/
theorem query_valid (decode : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause)
    (nominal scalar : (Nat → Bool) → Nat → Bool) (images : (Nat → Bool) → Call → Bool) :
    ComparisonWorldClauses.Valid (nominalValue (calls clauses) nominal images) scalar
      (query decode theory clauses) ↔
      ∀world,∀clause∈clauses,CNFHolds (rawValue decode nominal scalar world) theory →
        clause.Holds (rawValue decode nominal scalar world) (images (world 0)) := by
  exact forall_congr' fun world => query_correct decode theory clauses nominal scalar images world

theorem query_selectors_iff (decode : Nat → Nat × Nat) (theory : CNF) (clauses : List CompiledClause)
    (nominal scalar : (Nat → Bool) → Nat → Bool) (images : (Nat → Bool) → Call → Bool) :
    (∀world,∀clause∈clauses,CNFHolds (rawValue decode nominal scalar world) theory →
        clause.Holds (rawValue decode nominal scalar world) (images (world 0))) ↔
      ∃choice,ComparisonWorldClauses.SelectedValid
        (nominalValue (calls clauses) nominal images) scalar (query decode theory clauses) choice := by
  rw [←query_valid,ComparisonWorldClauses.selectors_iff]

end ModalityInference.ComparisonSignedWorlds
