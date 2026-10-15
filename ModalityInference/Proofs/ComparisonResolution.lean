import ModalityInference.ComparisonResolution
import ModalityInference.Proofs.CompactCNF
import ModalityInference.Proofs.CNFPropagation

/-! Incremental resolution has the same models as ordinary elimination and
retains only non-pivot literals from the input clauses. No normalization
invariant is required of the input. -/
namespace ModalityInference.ComparisonResolution

private theorem insertFold_correct (σ : Nat → Bool) (clauses rest : CNF) :
    CNFHolds σ (clauses.foldr
      (fun c acc => CompactCNF.insert (CompactCNF.canonical c) acc) rest) ↔
      CNFHolds σ clauses ∧ CNFHolds σ rest := by
  induction clauses with
  | nil => simp [CNFHolds]
  | cons c cs ih =>
    simp only [List.foldr_cons, CompactCNF.insert_correct, CompactCNF.canonical_correct, ih]
    simp [CNFHolds, and_assoc]

private theorem cross_fold (lower upper rest : CNF) :
    lower.foldr (fun l acc => upper.foldr
      (fun u acc => CompactCNF.insert (CompactCNF.canonical (l ++ u)) acc) acc) rest =
      (lower.flatMap fun l => upper.map (l ++ ·)).foldr
        (fun c acc => CompactCNF.insert (CompactCNF.canonical c) acc) rest := by
  induction lower with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.foldr_cons, List.flatMap_cons, List.foldr_append, List.foldr_map, ih]

/-- Incremental minimization preserves exactly the models of ordinary
resolution, even when the input clauses have not been normalized. -/
theorem eliminate_correct (cs : CNF) (v : Nat) (σ : Nat → Bool) :
    CNFHolds σ (eliminate cs v) ↔ CNFHolds σ (CNFPropagation.eliminate cs v) := by
  rw [eliminate, cross_fold, insertFold_correct, CNFPropagation.eliminate,
    cleanCNF_correct, cnfHolds_append]
  exact and_comm

private theorem insertFold_literal {clauses rest : CNF} {candidate : Clause} {literal : Literal}
    (hc : candidate ∈ clauses.foldr
      (fun c acc => CompactCNF.insert (CompactCNF.canonical c) acc) rest)
    (hl : literal ∈ candidate) : ∃original∈clauses ++ rest, literal ∈ original := by
  induction clauses generalizing candidate with
  | nil => exact ⟨candidate, hc, hl⟩
  | cons c cs ih =>
    rcases CompactCNF.mem_insert hc with rfl | hm
    · exact ⟨c, List.mem_cons_self, (CompactCNF.mem_canonical literal c).mp hl⟩
    · obtain ⟨original, ho, hl⟩ := ih hm hl
      exact ⟨original, List.mem_cons_of_mem c ho, hl⟩

private theorem eliminate_literal_info {cs : CNF} {v : Nat} {candidate : Clause} {literal : Literal}
    (hc : candidate ∈ eliminate cs v) (hl : literal ∈ candidate) :
    (∃original∈cs, literal ∈ original) ∧ literal.1 ≠ v := by
  rw [eliminate, cross_fold] at hc
  obtain ⟨original, ho, hl⟩ := insertFold_literal hc hl
  simp [CNFPropagation.lower, CNFPropagation.upper, CNFPropagation.unaffected,
    List.mem_flatMap, List.mem_map] at ho
  rcases ho with ⟨a, ha, b, hb, rfl⟩ | ⟨ho, hp, hn⟩
  · simp only [List.mem_append, CNFPropagation.without, List.mem_filter, bne_iff_ne] at hl
    rcases hl with ⟨hl, hne⟩ | ⟨hl, hne⟩
    · exact ⟨⟨a, ha.1, hl⟩, hne⟩
    · exact ⟨⟨b, hb.1, hl⟩, hne⟩
  · refine ⟨⟨original, ho, hl⟩, ?_⟩
    rcases literal with ⟨w, p⟩
    intro he
    change w = v at he
    subst w
    cases p <;> contradiction

theorem eliminate_literal {cs : CNF} {v : Nat} {candidate : Clause} {literal : Literal}
    (hc : candidate ∈ eliminate cs v) (hl : literal ∈ candidate) :
    ∃original∈cs, literal ∈ original :=
  (eliminate_literal_info hc hl).1

theorem eliminate_atoms {cs : CNF} {v w : Nat}
    (hw : w ∈ CNFPropagation.atoms (eliminate cs v)) :
    w ∈ CNFPropagation.atoms cs ∧ w ≠ v := by
  obtain ⟨candidate, hc, p, hl⟩ := CNFPropagation.mem_atoms.mp hw
  obtain ⟨⟨original, ho, hl⟩, hne⟩ := eliminate_literal_info hc hl
  exact ⟨CNFPropagation.mem_atoms.mpr ⟨original, ho, p, hl⟩, hne⟩

/-- The retained clauses hold exactly when the pivot can be assigned a value
that satisfies the original input. -/
theorem eliminate_iff (cs : CNF) (v : Nat) (σ : Nat → Bool) :
    CNFHolds σ (eliminate cs v) ↔ ∃b, CNFHolds (Function.update σ v b) cs :=
  (eliminate_correct cs v σ).trans (CNFPropagation.eliminate_iff cs v σ)

end ModalityInference.ComparisonResolution
