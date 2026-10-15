import ModalityInference.ComparisonSliceCNF
import ModalityInference.Proofs.ComparisonSelectorPropagation
import ModalityInference.Proofs.ComparisonSliceCNFCore

/-! Signed normalization preserves every existing parameter slice. Relational
normalization synchronizes only parameter coordinates, retaining independent heads. -/
namespace ModalityInference.ComparisonSliceCNF
open ComparisonPropagation ComparisonSelectorPropagation

def sync (heads parameters : Nat) (source target : Nat → Bool) (i : Nat) : Bool :=
  if heads ≤ i ∧ i < heads + 2 * parameters then source i else target i

def pair (source target : Nat → Bool) (i : Nat) : Bool :=
  if i % 2 = 0 then source (i / 2) else target (i / 2)

theorem pair_even (source target : Nat → Bool) (i : Nat) : pair source target (2 * i) = source i := by
  simp [pair]

theorem pair_odd (source target : Nat → Bool) (i : Nat) : pair source target (2 * i + 1) = target i := by
  simp [pair]

theorem pair_parameter {heads parameters : Nat} (source target : Nat → Bool) {i : Nat}
    (hi : heads ≤ i / 2 ∧ i / 2 < heads + 2 * parameters) :
    pair source (sync heads parameters source target) i = source (i / 2) := by
  simp [pair, sync, hi]

theorem point_value {heads parameters : Nat} {choice source : Nat → Bool}
    (hs : Slice heads parameters choice source) {i : Nat}
    (hi : heads ≤ i ∧ i < heads + 2 * parameters) :
    source i = if (i - heads) % 2 = 0 then source (heads + 2 * ((i - heads) / 2))
      else !source (heads + 2 * ((i - heads) / 2)) := by
  have hk : (i-heads)/2 < parameters := by omega
  have hh := hs ((i-heads)/2) hk
  by_cases he : (i-heads)%2=0
  · have hi : i=heads+2*((i-heads)/2) := by omega
    simp only [he, ↓reduceIte, ←hi]
  · have hi : i=heads+2*((i-heads)/2)+1 := by omega
    simp only [he, ↓reduceIte]
    rw [hh.1, ←hh.2]
    exact congrArg source hi

theorem relationLiteral_correct {heads parameters : Nat} {choice source : Nat → Bool}
    (hs : Slice heads parameters choice source) (target : Nat → Bool) (literal : Literal) :
    pair source target (relationLiteral heads parameters literal).1 =
        (relationLiteral heads parameters literal).2 ↔
      pair source (sync heads parameters source target) literal.1 = literal.2 := by
  unfold relationLiteral
  split
  · next hi =>
    simp only [pair_even, pair_parameter source target hi]
    rw [point_value hs hi]
    split <;> cases literal.2 <;>
      cases source (heads + 2 * ((literal.1 / 2 - heads) / 2)) <;> decide
  · next hi => simp only [pair, sync, hi, ↓reduceIte]


theorem pointLiteral_correct {heads parameters : Nat} {choice world : Nat → Bool}
    (hs : Slice heads parameters choice world) (literal : Literal) :
    world (pointLiteral heads parameters literal).1 = (pointLiteral heads parameters literal).2 ↔
      world literal.1 = literal.2 := by
  unfold pointLiteral
  split
  · next hi =>
    rw [point_value hs hi]
    split <;> cases literal.2 <;>
      cases world (heads + 2 * ((literal.1 - heads) / 2)) <;> simp
  · rfl


theorem point_correct {heads parameters : Nat} {choice world : Nat → Bool}
    (hs : Slice heads parameters choice world) (clauses : CNF) :
    CNFHolds world (point heads parameters clauses) ↔ CNFHolds world clauses :=
  mapped_correct _ clauses world world (pointLiteral_correct hs)

theorem relation_correct {heads parameters : Nat} {choice source : Nat → Bool}
    (hs : Slice heads parameters choice source) (target : Nat → Bool) (clauses : CNF) :
    CNFHolds (pair source target) (relation heads parameters clauses) ↔
      CNFHolds (pair source (sync heads parameters source target)) clauses :=
  mapped_correct _ clauses _ _ (relationLiteral_correct hs target)

theorem sync_slice {heads parameters : Nat} {choice source : Nat → Bool}
    (hs : Slice heads parameters choice source) (target : Nat → Bool) :
    Slice heads parameters choice (sync heads parameters source target) := by
  intro i hi
  simpa only [sync, show heads ≤ heads+2*i ∧ heads+2*i < heads+2*parameters by omega,
    show heads ≤ heads+2*i+1 ∧ heads+2*i+1 < heads+2*parameters by omega, ↓reduceIte] using hs i hi

theorem sync_of_slice {heads parameters : Nat} {choice source target : Nat → Bool}
    (hs : Slice heads parameters choice source) (ht : Slice heads parameters choice target) :
    sync heads parameters source target = target := by
  funext i
  unfold sync
  split
  · next hi => exact hs.agree ht (by simpa only [keepSelectors, decide_eq_true_eq] using hi)
  · rfl

theorem relation_implication_correct {heads parameters : Nat} {choice source : Nat → Bool}
    (hs : Slice heads parameters choice source) (left right : CNF) :
    (∀target, CNFHolds (pair source target)
      (implies (relation heads parameters left) (relation heads parameters right))) ↔
    ∀target, Slice heads parameters choice target →
      CNFHolds (pair source target) left → CNFHolds (pair source target) right := by
  simp_rw [implies_correct, relation_correct hs]
  constructor
  · intro h target ht
    simpa only [sync_of_slice hs ht] using h target
  · intro h target
    exact h _ (sync_slice hs target)


end ModalityInference.ComparisonSliceCNF
