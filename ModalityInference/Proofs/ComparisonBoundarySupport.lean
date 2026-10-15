import ModalityInference.Proofs.ComparisonJointSummary
import ModalityInference.Proofs.ComparisonSliceCNFSupport

/-! The concrete boundary summary introduces no scalar or head observations
outside the finite namespace of its input program. -/
namespace ModalityInference.ComparisonBoundarySupport

open ComparisonPropagation ComparisonSelectorPropagation ComparisonBoundaryPropagation
open ComparisonJointSummary ComparisonJointClauses

theorem supported_iff (domain : List Nat) (cs : CNF) :
    Supported domain cs ↔ ∀c∈cs, ∀literal∈c, literal.1 ∈ domain := by
  constructor
  · intro h c hc literal hl
    exact h _ (CNFPropagation.mem_atoms.mpr ⟨c, hc, literal.2, hl⟩)
  · intro h v hv
    obtain ⟨c, hc, p, hp⟩ := CNFPropagation.mem_atoms.mp hv
    exact h c hc (v, p) hp

theorem append_supported {domain : List Nat} {a b : CNF}
    (ha : Supported domain a) (hb : Supported domain b) : Supported domain (a ++ b) := by
  rw [supported_iff] at ha hb ⊢
  intro c hc
  exact (List.mem_append.mp hc).elim (ha c) (hb c)

theorem meet_supported {domain : List Nat} {a b : CNF}
    (ha : Supported domain a) (hb : Supported domain b) : Supported domain (meet a b) :=
  fun v hv => append_supported ha hb v (CompactCNF.clean_atoms hv)

private theorem negateClause_supported {domain : List Nat} {c : Clause}
    (h : ∀literal∈c, literal.1 ∈ domain) : Supported domain (negateClause c) := by
  rw [supported_iff]
  intro d hd literal hl
  obtain ⟨⟨i, p⟩, hi, rfl⟩ := List.mem_map.mp hd
  simp only [List.mem_singleton] at hl
  cases hl
  exact h (i, p) hi

theorem negate_supported {domain : List Nat} {cs : CNF}
    (h : Supported domain cs) : Supported domain (negate cs) := by
  rw [supported_iff] at h
  induction cs with
  | nil => simp [negate, Supported, CNFPropagation.atoms]
  | cons c cs ih =>
    exact join_supported (negateClause_supported (h c List.mem_cons_self))
      (ih (fun d hd => h d (List.mem_cons_of_mem _ hd)))

private theorem implies_supported {domain : List Nat} {a b : CNF}
    (ha : Supported domain a) (hb : Supported domain b) : Supported domain (implies a b) :=
  join_supported (negate_supported ha) hb

theorem rename_supported {domain target : List Nat} {cs : CNF} {f : Nat → Nat}
    (h : Supported domain cs) (hf : ∀i∈domain, f i ∈ target) : Supported target (rename f cs) := by
  rw [supported_iff] at h ⊢
  intro c hc literal hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨⟨i, p⟩, hi, he⟩ := List.mem_map.mp hl
  cases he
  exact hf i (h d hd (i, p) hi)

private theorem allClauses_supported {domain : List Nat} {clauses : List CNF}
    (h : ∀c∈clauses, Supported domain c) : Supported domain (allClauses clauses) := by
  induction clauses with
  | nil => simp [allClauses, Supported, CNFPropagation.atoms]
  | cons c cs ih =>
    exact meet_supported (h c List.mem_cons_self) (ih (fun d hd => h d (List.mem_cons_of_mem _ hd)))

private theorem theory_supported (heads parameters : Nat) :
    Supported (List.range (heads + 2 * parameters)) (theory heads parameters) := by
  rw [supported_iff]
  intro c hc literal hl
  obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
  have hi := List.mem_range.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals rcases hl with rfl | rfl <;> simp only [List.mem_range] <;> omega

private theorem agreement_supported (heads parameters : Nat) :
    Supported (List.range (2 * (heads + 2 * parameters))) (agreement heads parameters) := by
  rw [supported_iff]
  intro c hc literal hl
  obtain ⟨i, hi, hc⟩ := List.mem_flatMap.mp hc
  have hi := List.mem_range.mp hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals rcases hl with rfl | rfl <;> simp only [List.mem_range] <;> omega

private theorem guardRelation_supported {heads parameters : Nat} {relation : CNF}
    (h : Supported (List.range (2 * (heads + 2 * parameters))) relation) :
    Supported (List.range (2 * (heads + 2 * parameters))) (guardRelation heads parameters relation) := by
  apply append_supported
  · apply append_supported
    · apply append_supported h
      exact rename_supported (theory_supported heads parameters) (by
        intro i hi; simp only [List.mem_range] at hi ⊢; omega)
    · exact rename_supported (theory_supported heads parameters) (by
        intro i hi; simp only [List.mem_range] at hi ⊢; omega)
  · exact agreement_supported heads parameters

/-- Path closure keeps the source head observation in a finite complementary
parameter block, and decoding puts it back in the relational head prefix. -/
theorem pathRelation_supported (heads parameters : Nat) (program : Program count)
    (source target : Fin count) :
    Supported (List.range (2 * (heads + 2 * parameters)))
      (pathRelation heads parameters program source target) := by
  have h := ComparisonParametricPropagation.closure_supported heads (parameters + heads)
    (sourceProgram heads parameters program source) target
  rw [supported_iff] at h ⊢
  intro c hc literal hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨value, hv, he⟩ := List.mem_map.mp hl
  cases he
  have hi := List.mem_range.mp (h d hd value hv)
  simp only [decodeLiteral, List.mem_range]
  split <;> dsimp only <;> omega

theorem guardedPath_supported (heads parameters : Nat) (program : Program count)
    (source target : Fin count) :
    Supported (List.range (2 * (heads + 2 * parameters)))
      (guardedPath heads parameters program source target) :=
  guardRelation_supported (pathRelation_supported heads parameters program source target)

private theorem allTargets_supported {size : Nat} {clauses : CNF}
    (h : Supported (List.range (2 * size)) clauses) :
    Supported (List.range size) (allTargets clauses) := by
  apply rename_supported (fun v hv => h v (SymbolicCNF.abstract_atoms hv).1)
  intro i hi
  simp only [List.mem_range] at hi ⊢
  omega

/-- The actual summary's lower, relational, upper, and checking guards all stay
inside the original finite observation namespace. -/
theorem summarize_supported {heads parameters : Nat} {program : Program count}
    (h : GuardsSupported (heads + 2 * parameters) program)
    (boundary : Vector (Fin count) retained) :
    GuardsSupported (heads + 2 * parameters) (summarize heads parameters program boundary) := by
  constructor
  · intro v
    simp only [summarize, Fin.getElem_fin, Vector.getElem_ofFn]
    exact ComparisonParametricPropagation.closure_supported heads parameters program boundary[v]
  · intro edge he
    obtain ⟨source, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨target, _, rfl⟩ := List.mem_map.mp he
    exact guardedPath_supported heads parameters program boundary[source] boundary[target]
  · intro source
    simp only [summarize, Fin.getElem_fin, Vector.getElem_ofFn]
    apply allClauses_supported
    intro c hc
    obtain ⟨target, _, rfl⟩ := List.mem_map.mp hc
    apply allTargets_supported
    apply implies_supported
      (ComparisonSliceCNF.relation_supported
        (pathRelation_supported heads parameters program boundary[source] target))
    apply ComparisonSliceCNF.relation_supported
    exact rename_supported (h.upper target) (by
      intro i hi; simp only [List.mem_range] at hi ⊢; omega)
  · apply meet_supported h.checks
    apply allClauses_supported
    intro c hc
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
    exact implies_supported
      (ComparisonSliceCNF.point_supported
        (ComparisonParametricPropagation.closure_supported heads parameters program v))
      (ComparisonSliceCNF.point_supported (h.upper v))

/-- Summary compilation needs only the original program's finite support. -/
theorem compile_summary_correct {heads parameters : Nat} (hparameters : 0 < parameters)
    (program : Program count) (boundary : Vector (Fin count) retained) (store : Store retained)
    (hs : GuardsSupported (heads + 2 * parameters) program)
    (hstore : store.Supported heads) (strategy : (Nat → Bool) → Nat → Bool) :
    Holds store strategy (compile heads (summarize heads parameters program boundary)) ↔
      ∃ full : Store count, full.Positive ∧ full.Supported (heads + 2 * parameters) ∧
        ∀ modeWorld, SliceValid heads parameters (strategy modeWorld) program full ∧
          BoundaryAgreement heads parameters (strategy modeWorld) boundary full store :=
  ComparisonJointSummary.compile_summary_correct hparameters program boundary store hs.edges
    (summarize_supported hs boundary) hstore strategy

end ModalityInference.ComparisonBoundarySupport
