import ModalityInference.ComparisonJointClauses
import ModalityInference.Proofs.ComparisonBoundaryPropagation
import ModalityInference.Proofs.ComparisonJointModes

namespace ModalityInference.ComparisonJointClauses

open ComparisonPropagation ComparisonSelectorPropagation ComparisonBoundaryPropagation

def HeadClause.Holds (store : Store count) (world : Nat → Bool) : HeadClause heads count → Prop
  | .lower target guard => ClauseHolds world (literals guard) ∨ CNFHolds world store[target]
  | .edge source target guard => CNFHolds (fun i => world (2 * i)) store[source] →
      ClauseHolds world (literals guard) ∨ CNFHolds (fun i => world (2 * i + 1)) store[target]
  | .upper source guard => CNFHolds world store[source] → ClauseHolds world (literals guard)
  | .check guard => ClauseHolds world (literals guard)

/-- The scalar strategy depends on its legal input axis, while every nominal
state is one polynomial of the rigid type heads. -/
def Holds (store : Store count) (strategy : (Nat → Bool) → Nat → Bool)
    (clauses : List (JointClause heads count)) : Prop :=
  ∀ headWorld modeWorld, ∀ clause ∈ clauses,
    clause.head.Holds store headWorld ∨ ClauseHolds (strategy modeWorld) clause.modes

def HeadClause.SliceHolds (heads parameters index : Nat) (choice : Nat → Bool)
    (store : Store count) : HeadClause heads count → Prop
  | .lower target guard => ∀ world, Slice heads parameters choice world →
      ClauseHolds world (headGuard heads index (literals guard)) ∨ CNFHolds world store[target]
  | .edge source target guard => ∀ world,
      Slice heads parameters choice (fun i => world (2 * i)) →
      Slice heads parameters choice (fun i => world (2 * i + 1)) →
      CNFHolds (fun i => world (2 * i)) store[source] →
      ClauseHolds world (edgeGuard heads index (literals guard)) ∨
        CNFHolds (fun i => world (2 * i + 1)) store[target]
  | .upper source guard => ∀ world, Slice heads parameters choice world →
      CNFHolds world store[source] → ClauseHolds world (headGuard heads index (literals guard))
  | .check guard => ∀ world, Slice heads parameters choice world →
      ClauseHolds world (headGuard heads index (literals guard))

theorem literals_congr (guard : List (HeadLiteral size)) {left right : Nat → Bool}
    (h : ∀ i < size, left i = right i) :
    ClauseHolds left (literals guard) ↔ ClauseHolds right (literals guard) := by
  simp only [ClauseHolds, literals, List.mem_map, Prod.exists]
  constructor
  · rintro ⟨v, b, ⟨i, p, hi, he⟩, hv⟩
    cases he
    exact ⟨i.val, b, ⟨i, b, hi, rfl⟩, (h i.val i.isLt).symm.trans hv⟩
  · rintro ⟨v, b, ⟨i, p, hi, he⟩, hv⟩
    cases he
    exact ⟨i.val, b, ⟨i, b, hi, rfl⟩, (h i.val i.isLt).trans hv⟩

theorem store_select {heads : Nat} {store : Store count} (hs : store.Supported heads)
    (choice world : Nat → Bool) (v : Fin count) :
    CNFHolds (select heads choice world) store[v] ↔ CNFHolds world store[v] := by
  apply CNFPropagation.holds_congr
  intro i hi
  simp only [select, if_pos (List.mem_range.mp (hs v i hi))]

def selectRelation (heads : Nat) (choice world : Nat → Bool) : Nat → Bool :=
  pairWorld (select heads choice (fun i => world (2 * i)))
    (select heads choice (fun i => world (2 * i + 1)))

theorem selectRelation_below {heads : Nat} (choice world : Nat → Bool) {i : Nat}
    (hi : i < 2 * heads) : selectRelation heads choice world i = world i := by
  unfold selectRelation pairWorld
  by_cases hp : i % 2 = 0
  · have hbelow : i / 2 < heads := by omega
    simp only [hp, BEq.rfl, ↓reduceIte, select, if_pos hbelow]
    congr 1; omega
  · have hbelow : i / 2 < heads := by omega
    have hb : (i % 2 == 0) = false := by simpa using hp
    simp only [hb, Bool.false_eq_true, ↓reduceIte, select, if_pos hbelow]
    congr 1; omega

theorem headGuard_correct {heads parameters index : Nat} {choice world : Nat → Bool}
    (h : Slice heads parameters choice world) (hi : 2 * index < parameters) (guard : Clause) :
    ClauseHolds world (headGuard heads index guard) ↔
      choice (2 * index) = false ∨ ClauseHolds world guard := by
  have hs := (h (2 * index) hi).2
  have he : heads + 2 * (2 * index) + 1 = heads + 4 * index + 1 := by omega
  rw [he] at hs
  simp only [headGuard, clauseHolds_cons, hs]
  cases choice (2 * index) <;> simp

theorem edgeGuard_correct {heads parameters index : Nat} {choice world : Nat → Bool}
    (h : Slice heads parameters choice (fun i => world (2 * i + 1)))
    (hi : 2 * index < parameters) (guard : Clause) :
    ClauseHolds world (edgeGuard heads index guard) ↔
      choice (2 * index) = false ∨ ClauseHolds world guard := by
  have hs := (h (2 * index) hi).2
  have he : heads + 2 * (2 * index) + 1 = heads + 4 * index + 1 := by omega
  rw [he] at hs
  simp only [edgeGuard, clauseHolds_cons, hs]
  cases choice (2 * index) <;> simp

def HeadClause.Admissible (heads parameters : Nat) (choice world : Nat → Bool) :
    HeadClause heads count → Prop
  | .edge _ _ _ => Slice heads parameters choice (fun i => world (2 * i)) ∧
      Slice heads parameters choice (fun i => world (2 * i + 1))
  | _ => Slice heads parameters choice world

def HeadClause.selectWorld (choice world : Nat → Bool) : HeadClause heads count → (Nat → Bool)
  | .edge _ _ _ => selectRelation heads choice world
  | _ => select heads choice world

theorem HeadClause.selected_admissible (parameters : Nat) (choice world : Nat → Bool)
    (clause : HeadClause heads count) :
    clause.Admissible heads parameters choice (clause.selectWorld choice world) := by
  cases clause <;> simp only [Admissible, selectWorld, selectRelation, pairWorld_even, pairWorld_odd]
  · exact select_slice _ _ _ _
  · exact ⟨select_slice _ _ _ _, select_slice _ _ _ _⟩
  · exact select_slice _ _ _ _
  · exact select_slice _ _ _ _

theorem literals_select (guard : List (HeadLiteral heads)) (choice world : Nat → Bool) :
    ClauseHolds (select heads choice world) (literals guard) ↔ ClauseHolds world (literals guard) :=
  literals_congr guard (fun i hi => by simp only [select, if_pos hi])

theorem HeadClause.selected_holds {store : Store count} (hs : store.Supported heads)
    (choice world : Nat → Bool) (clause : HeadClause heads count) :
    clause.Holds store (clause.selectWorld choice world) ↔ clause.Holds store world := by
  cases clause with
  | lower target guard =>
    exact or_congr (literals_select guard choice world) (store_select hs choice world target)
  | edge source target guard =>
    simp only [Holds, selectWorld, selectRelation, pairWorld_even, pairWorld_odd]
    exact imp_congr (store_select hs choice _ source)
      (or_congr (literals_congr guard (fun i hi => selectRelation_below choice world hi))
        (store_select hs choice _ target))
  | upper source guard =>
    exact imp_congr (store_select hs choice world source) (literals_select guard choice world)
  | check guard => exact literals_select guard choice world

theorem HeadClause.sliceHolds_normal {heads parameters index : Nat} {choice : Nat → Bool}
    (store : Store count) (clause : HeadClause heads count) (hi : 2 * index < parameters) :
    clause.SliceHolds heads parameters index choice store ↔
      ∀ world, clause.Admissible heads parameters choice world →
        choice (2 * index) = false ∨ clause.Holds store world := by
  cases clause with
  | lower target guard =>
    simp only [SliceHolds, Admissible, Holds]
    apply forall_congr' fun world => imp_congr_right fun hw => ?_
    rw [headGuard_correct hw hi]
    tauto
  | edge source target guard =>
    simp only [SliceHolds, Admissible, Holds, and_imp]
    apply forall_congr' fun world => imp_congr_right fun hl => imp_congr_right fun ht => ?_
    rw [edgeGuard_correct ht hi]
    tauto
  | upper source guard =>
    simp only [SliceHolds, Admissible, Holds]
    apply forall_congr' fun world => imp_congr_right fun hw => ?_
    rw [headGuard_correct hw hi]
    tauto
  | check guard =>
    simp only [SliceHolds, Admissible, Holds]
    exact forall_congr' fun world => imp_congr_right fun hw => headGuard_correct hw hi _

theorem HeadClause.sliceHolds_iff {heads parameters index : Nat} {choice : Nat → Bool}
    {store : Store count} (hs : store.Supported heads) (clause : HeadClause heads count)
    (hi : 2 * index < parameters) :
    clause.SliceHolds heads parameters index choice store ↔
      (choice (2 * index) = true → ∀ world, clause.Holds store world) := by
  rw [clause.sliceHolds_normal store hi]
  constructor
  · intro h hc world
    have hh := h (clause.selectWorld choice world) (clause.selected_admissible parameters choice world)
    exact (clause.selected_holds hs choice world).mp
      (hh.resolve_left (by simp [hc]))
  · intro h world _
    cases hc : choice (2 * index) with
    | false => exact Or.inl rfl
    | true => exact Or.inr (h hc world)

end ModalityInference.ComparisonJointClauses
