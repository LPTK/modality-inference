import ModalityInference.ComparisonJointReindex
import ModalityInference.Proofs.ComparisonJointGuarded
import ModalityInference.Proofs.ComparisonBoundarySupport

namespace ModalityInference.ComparisonJointReindex

open ComparisonPropagation ComparisonJointClauses ComparisonJointGuarded

theorem literals_map (f : Fin size → Fin total) (guard : List (HeadLiteral size))
    (world : Nat → Bool) :
    ClauseHolds world (literals (guard.map fun l => (f l.1, l.2))) ↔
      ∃ l ∈ guard, world (f l.1).val = l.2 := by
  simp [ClauseHolds, literals, List.mem_map, Prod.exists]

theorem constants_map (f : Fin size → Fin total) (guard : List (Fin size × Bool))
    (choice : Fin total → Bool) :
    ConstantsHold choice (guard.map fun l => (f l.1, l.2)) ↔
      ConstantsHold (choice ∘ f) guard := by
  constructor
  · rintro ⟨l, hl, he⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
    exact ⟨k, hk, he⟩
  · rintro ⟨l, hl, he⟩
    exact ⟨(f l.1, l.2), List.mem_map.mpr ⟨l, hl, rfl⟩, he⟩

theorem store_correct (f : Nat → Nat) (states : Fin count → Fin totalCount)
    (full : Store totalCount) (i : Fin count) (world : Nat → Bool) :
    CNFHolds world (store f states full)[i] ↔ CNFHolds (world ∘ f) full[states i] := by
  simpa [store, Vector.get] using rename_correct f full[states i] world

theorem store_polynomial {heads totalHeads : Nat} {f : Nat → Nat}
    {states : Fin count → Fin totalCount} {full : Store totalCount}
    (h : full.Polynomial totalHeads) (hf : ∀ i < totalHeads, f i < heads) :
    (store f states full).Polynomial heads := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i c hc literal hl
    have hc' : c ∈ rename f full[states i] := by simpa [store] using hc
    change c ∈ List.map _ _ at hc'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hl
    exact h.1 (states i) d hd k hk
  · intro i
    simpa [store, Vector.get] using ComparisonBoundarySupport.rename_supported
      (h.2.1 (states i)) (fun v hv => List.mem_range.mpr (hf v (List.mem_range.mp hv)))
  · intro i
    exact (store_correct f states full i (fun _ => true)).mpr (h.2.2.1 (states i))
  · intro i hi
    exact h.2.2.2 (states i) ((store_correct f states full i (fun _ => false)).mp hi)

def world (f : Nat → Nat) (valuation : Nat → Bool) : HeadClause heads count → Nat → Bool
  | .edge _ _ _ => fun i => valuation (2 * f (i / 2) + i % 2)
  | _ => valuation ∘ f

theorem paired_project {f : Nat → Nat} {embedding : Fin heads → Fin totalHeads}
    (h : ∀ i, f (embedding i).val = i.val) (i : Fin (2 * heads)) :
    2 * f ((paired embedding i).val / 2) + (paired embedding i).val % 2 = i.val := by
  have hdiv : (paired embedding i).val / 2 = (embedding ⟨i.val / 2, by omega⟩).val := by
    simp only [paired]; omega
  have hmod : (paired embedding i).val % 2 = i.val % 2 := by
    simp only [paired]; omega
  rw [hdiv, hmod, h]
  change 2 * (i.val / 2) + i.val % 2 = i.val
  omega

theorem literals_project {f : Nat → Nat} {embedding : Fin heads → Fin totalHeads}
    (h : ∀ i, f (embedding i).val = i.val) (guard : List (HeadLiteral heads))
    (valuation : Nat → Bool) :
    ClauseHolds (valuation ∘ f) (literals (guard.map fun l => (embedding l.1, l.2))) ↔
      ClauseHolds valuation (literals guard) := by
  rw [literals_map]
  simp only [Function.comp_def, h]
  simp [ClauseHolds, literals, List.mem_map, Prod.exists]

theorem paired_literals_project {f : Nat → Nat} {embedding : Fin heads → Fin totalHeads}
    (h : ∀ i, f (embedding i).val = i.val) (guard : List (HeadLiteral (2 * heads)))
    (valuation : Nat → Bool) :
    ClauseHolds (fun i => valuation (2 * f (i / 2) + i % 2))
      (literals (guard.map fun l => (paired embedding l.1, l.2))) ↔
      ClauseHolds valuation (literals guard) := by
  rw [literals_map]
  simp only [paired_project h]
  simp [ClauseHolds, literals, List.mem_map, Prod.exists]

theorem headClause_project {f : Nat → Nat} {embedding : Fin heads → Fin totalHeads}
    (h : ∀ i, f (embedding i).val = i.val) (states : Fin count → Fin totalCount)
    (full : Store totalCount) (c : HeadClause heads count) (valuation : Nat → Bool) :
    (headClause embedding states c).Holds full (world f valuation c) ↔
      c.Holds (store f states full) valuation := by
  cases c with
  | lower target guard =>
    simp only [headClause, HeadClause.Holds, world, literals_project h, store_correct]
  | upper source guard =>
    simp only [headClause, HeadClause.Holds, world, literals_project h, store_correct]
  | check guard =>
    exact literals_project h guard valuation
  | edge source target guard =>
    have hsource : (fun i => valuation (2 * f ((2 * i) / 2) + (2 * i) % 2)) =
        (fun i => valuation (2 * f i)) := by funext i; simp
    have htarget : (fun i => valuation (2 * f ((2 * i + 1) / 2) + (2 * i + 1) % 2)) =
        (fun i => valuation (2 * f i + 1)) := by funext i; simp
    simp only [headClause, HeadClause.Holds, world, hsource, htarget,
      paired_literals_project h, store_correct, Function.comp_def]

/-- A single shared strategy restricts to each nominal group. Projecting its
head polynomials changes no constant choice or modality substitution. -/
theorem holds_project {f : Nat → Nat} {embedding : Fin heads → Fin totalHeads}
    (h : ∀ i, f (embedding i).val = i.val) (states : Fin count → Fin totalCount)
    (constantsMap : Fin constants → Fin totalConstants) (choice : Fin totalConstants → Bool)
    (full : Store totalCount) (strategy : (Nat → Bool) → Nat → Bool)
    (cs : List (GuardedClause heads count constants))
    (hc : Holds choice full strategy (clauses embedding states constantsMap cs)) :
    Holds (choice ∘ constantsMap) (store f states full) strategy cs := by
  intro headWorld modeWorld c hmem
  have hh := hc (world f headWorld c.head) modeWorld (clause embedding states constantsMap c)
    (List.mem_map.mpr ⟨c, hmem, rfl⟩)
  rcases hh with hk | hh | hm
  · exact Or.inl ((constants_map constantsMap c.constants choice).mp hk)
  · exact Or.inr (Or.inl ((headClause_project h states full c.head headWorld).mp hh))
  · exact Or.inr (Or.inr hm)

end ModalityInference.ComparisonJointReindex
