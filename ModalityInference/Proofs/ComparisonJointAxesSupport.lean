import ModalityInference.Proofs.ComparisonJointAxes
import ModalityInference.Proofs.ComparisonJointHorn

/-! Axis separation preserves linear state clauses and finite input support.
Selectors occupy a bounded odd namespace; only original input atoms are copied. -/
namespace ModalityInference.ComparisonJointAxes

open ComparisonJointHorn ComparisonPropagation

theorem ownClauses_linear {state : Nat → Prop} {clauses : CNF}
    (h : Linear state clauses) (side : Nat → Bool) (component : Bool) (count heads : Nat) :
    Linear (EvenState state) (ownClauses side component count heads clauses) := by
  simpa [ModalSynthesis.component, ownClauses, ownPart] using
    component_linear h (own side component count heads) true

theorem ownClauses_atoms {side : Nat → Bool} {component : Bool} {count heads : Nat}
    {clauses : CNF} {v : Nat}
    (h : v ∈ CNFPropagation.atoms (ownClauses side component count heads clauses)) :
    (∃ i, i < clauses.length ∧ v = 2 * i + 1) ∨
      ∃ w, v = 2 * w ∧ own side component count heads w = true ∧
        w ∈ CNFPropagation.atoms clauses := by
  obtain ⟨clause, hc, polarity, hp⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨⟨source, index⟩, hi, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_cons.mp hp with he | hm
  · have he := congrArg Prod.fst he
    change v = 2 * index + 1 at he
    refine .inl ⟨index, ?_, he⟩
    exact (List.mem_zipIdx' hi).1
  · obtain ⟨⟨w, q⟩, hw, he⟩ := List.mem_map.mp hm
    cases he
    obtain ⟨hw, ho⟩ := List.mem_filter.mp hw
    exact .inr ⟨w, rfl, ho, CNFPropagation.mem_atoms.mpr
      ⟨source, List.fst_mem_of_mem_zipIdx hi, q, hw⟩⟩

theorem otherClauses_atoms {side : Nat → Bool} {component : Bool} {count heads : Nat}
    {clauses : CNF} {v : Nat}
    (h : v ∈ CNFPropagation.atoms (otherClauses side component count heads clauses)) :
    (∃ i, i < clauses.length ∧ v = 2 * i + 1) ∨
      ∃ w, v = 2 * w ∧ side w ≠ component ∧
        count + heads + w ∈ CNFPropagation.atoms clauses := by
  obtain ⟨clause, hc, polarity, hp⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨⟨source, index⟩, hi, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_cons.mp hp with he | hm
  · have he := congrArg Prod.fst he
    change v = 2 * index + 1 at he
    exact .inl ⟨index, (List.mem_zipIdx' hi).1, he⟩
  · obtain ⟨⟨w, q⟩, hw, he⟩ := List.mem_map.mp hm
    cases he
    obtain ⟨⟨original, q⟩, horiginal, he⟩ := List.mem_map.mp hw
    cases he
    obtain ⟨horiginal, ho⟩ := List.mem_filter.mp horiginal
    have ho : ¬original < count + heads ∧ side (original - (count + heads)) ≠ component := by
      simpa [own] using ho
    refine .inr ⟨original - (count + heads), rfl, ho.2, ?_⟩
    have he : count + heads + (original - (count + heads)) = original := by omega
    rw [he]
    exact CNFPropagation.mem_atoms.mpr
      ⟨source, List.fst_mem_of_mem_zipIdx hi, q, horiginal⟩

theorem ownClauses_supported {side : Nat → Bool} {component : Bool} {count heads : Nat}
    {clauses : CNF} {domain : List Nat} (h : Supported domain clauses) :
    Supported ((List.range clauses.length).map (fun i => 2 * i + 1) ++ domain.map (2 * ·))
      (ownClauses side component count heads clauses) := by
  intro v hv
  rcases ownClauses_atoms hv with ⟨i, hi, rfl⟩ | ⟨w, rfl, _, hw⟩
  · exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  · exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨w, h w hw, rfl⟩))

theorem otherClauses_supported {side : Nat → Bool} {component : Bool} {count heads modes : Nat}
    {clauses : CNF} (h : Supported (List.range (count + heads + modes)) clauses) :
    Supported ((List.range clauses.length).map (fun i => 2 * i + 1) ++ (List.range modes).map (2 * ·))
      (otherClauses side component count heads clauses) := by
  intro v hv
  rcases otherClauses_atoms hv with ⟨i, hi, rfl⟩ | ⟨w, rfl, _, hw⟩
  · exact List.mem_append.mpr (.inl (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
  · have hw : count + heads + w < count + heads + modes := List.mem_range.mp (h _ hw)
    exact List.mem_append.mpr (.inr (List.mem_map.mpr ⟨w, List.mem_range.mpr (by omega), rfl⟩))

/-- The non-selector outputs of the scalar half use only the opposite axis. -/
theorem otherClauses_side {side : Nat → Bool} {component : Bool} {count heads : Nat}
    {clauses : CNF} {v : Nat}
    (h : v ∈ CNFPropagation.atoms (otherClauses side component count heads clauses)) :
    ModalSynthesis.selector v = true ∨ ∃ w, v = 2 * w ∧ side w = !component := by
  rcases otherClauses_atoms h with ⟨i, _, rfl⟩ | ⟨w, rfl, hw, _⟩
  · exact .inl (ModalSynthesis.selector_odd i)
  · refine .inr ⟨w, rfl, ?_⟩
    cases component <;> cases he : side w <;> simp_all

end ModalityInference.ComparisonJointAxes
