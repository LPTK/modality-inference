import ModalityInference.ComparisonSliceCNF
import ModalityInference.Proofs.ComparisonPropagation

/-! Signed parameter normalization uses only the complement law, independent of
selector synthesis and its proof interfaces. -/
namespace ModalityInference.ComparisonSliceCNF

open ComparisonPropagation

theorem mapped_correct (f : Literal → Literal) (clauses : CNF) (world target : Nat → Bool)
    (h : ∀literal, world (f literal).1 = (f literal).2 ↔ target literal.1 = literal.2) :
    CNFHolds world (CompactCNF.clean (clauses.map (List.map f))) ↔ CNFHolds target clauses := by
  rw [CompactCNF.clean_correct]
  simp only [CNFHolds, List.forall_mem_map]
  apply forall_congr' fun c => imp_congr_right fun _ => ?_
  constructor
  · rintro ⟨i, p, hi, he⟩
    obtain ⟨literal, hl, eq⟩ := List.mem_map.mp hi
    exact ⟨literal.1, literal.2, hl, (h literal).mp (by simpa only [eq] using he)⟩
  · rintro ⟨i, p, hi, he⟩
    exact ⟨(f (i,p)).1, (f (i,p)).2, List.mem_map.mpr ⟨(i,p), hi, rfl⟩, (h (i,p)).mpr he⟩


theorem point_value_of_complement {heads parameters : Nat} {world : Nat → Bool}
    (hc : ∀i<parameters, world (heads+2*i+1) = !world (heads+2*i)) {i : Nat}
    (hi : heads ≤ i ∧ i < heads + 2 * parameters) :
    world i = if (i-heads)%2=0 then world (heads+2*((i-heads)/2))
      else !world (heads+2*((i-heads)/2)) := by
  have hk : (i-heads)/2 < parameters := by omega
  by_cases he : (i-heads)%2=0
  · have hi : i=heads+2*((i-heads)/2) := by omega
    simp only [he, ↓reduceIte, ←hi]
  · have hi : i=heads+2*((i-heads)/2)+1 := by omega
    simp only [he, ↓reduceIte]
    rw [←hc _ hk]
    exact congrArg world hi

theorem pointLiteral_correct_of_complement {heads parameters : Nat} {world : Nat → Bool}
    (hc : ∀i<parameters, world (heads+2*i+1) = !world (heads+2*i)) (literal : Literal) :
    world (pointLiteral heads parameters literal).1 = (pointLiteral heads parameters literal).2 ↔
      world literal.1 = literal.2 := by
  unfold pointLiteral
  split
  · next hi =>
    rw [point_value_of_complement hc hi]
    split <;> cases literal.2 <;>
      cases world (heads + 2 * ((literal.1 - heads) / 2)) <;> simp
  · rfl

theorem point_correct_of_complement {heads parameters : Nat} {world : Nat → Bool}
    (hc : ∀i<parameters, world (heads+2*i+1) = !world (heads+2*i)) (clauses : CNF) :
    CNFHolds world (point heads parameters clauses) ↔ CNFHolds world clauses :=
  mapped_correct _ clauses world world (pointLiteral_correct_of_complement hc)

theorem residual_correct_of_complement {heads parameters : Nat} {world : Nat → Bool}
    (hc : ∀i<parameters, world (heads+2*i+1) = !world (heads+2*i))
    (program : Program count) (store : Store count) :
    CNFHolds world (residual heads parameters program store) ↔
      CNFHolds world (ComparisonPropagation.residual program store) := by
  simp only [residual, ComparisonPropagation.residual_correct, Fin.getElem_fin,
    Vector.getElem_ofFn, point_correct_of_complement hc]

end ModalityInference.ComparisonSliceCNF
