import ModalityInference.ComparisonSliceCNF
import ModalityInference.Proofs.ComparisonPropagation

/-! Complementary-parameter normalization preserves the finite point and
relational observation namespaces. -/
namespace ModalityInference.ComparisonSliceCNF

open ComparisonPropagation

theorem pointLiteral_lt {heads parameters : Nat} {literal : Literal}
    (h : literal.1 < heads + 2 * parameters) :
    (pointLiteral heads parameters literal).1 < heads + 2 * parameters := by
  unfold pointLiteral
  split <;> omega

theorem relationLiteral_lt {heads parameters : Nat} {literal : Literal}
    (h : literal.1 < 2 * (heads + 2 * parameters)) :
    (relationLiteral heads parameters literal).1 < 2 * (heads + 2 * parameters) := by
  unfold relationLiteral
  split <;> omega

private theorem clean_map_supported {domain target : List Nat} {clauses : CNF}
    {f : Literal → Literal} (h : Supported domain clauses)
    (hf : ∀literal, literal.1 ∈ domain → (f literal).1 ∈ target) :
    Supported target (CompactCNF.clean (clauses.map (List.map f))) := by
  intro v hv
  obtain ⟨c, hc, p, hl⟩ := CNFPropagation.mem_atoms.mp (CompactCNF.clean_atoms hv)
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨⟨i, b⟩, hi, he⟩ := List.mem_map.mp hl
  simpa only [he] using hf (i, b) (h i (CNFPropagation.mem_atoms.mpr ⟨d, hd, b, hi⟩))

theorem point_supported {heads parameters : Nat} {clauses : CNF}
    (h : Supported (List.range (heads + 2 * parameters)) clauses) :
    Supported (List.range (heads + 2 * parameters)) (point heads parameters clauses) :=
  clean_map_supported h (fun _ hi => List.mem_range.mpr (pointLiteral_lt (List.mem_range.mp hi)))

theorem relation_supported {heads parameters : Nat} {clauses : CNF}
    (h : Supported (List.range (2 * (heads + 2 * parameters))) clauses) :
    Supported (List.range (2 * (heads + 2 * parameters))) (relation heads parameters clauses) :=
  clean_map_supported h (fun _ hi => List.mem_range.mpr (relationLiteral_lt (List.mem_range.mp hi)))

end ModalityInference.ComparisonSliceCNF
