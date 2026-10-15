import ModalityInference.ComparisonSkeleton
import ModalityInference.Proofs.Substitution
import ModalityInference.Proofs.ComparisonShapeSolver

namespace ModalityInference.ComparisonSkeleton

theorem allocate_domain (p : SchemePreparation.Prepared) (s : ComparisonShapeSolver.Solved)
    (vs : List Nat) (nt nm : Nat) :
    ((allocate p s vs nt nm).substitution.types.map Prod.fst) = vs := by
  induction vs generalizing nt nm <;> simp_all [allocate]

theorem allocate_fixes (p : SchemePreparation.Prepared) (s : ComparisonShapeSolver.Solved)
    (vs : List Nat) (nt nm n : Nat) (h : n ∉ vs) :
    (allocate p s vs nt nm).substitution.type (.flex n) = .var (.flex n) := by
  have absent : (allocate p s vs nt nm).substitution.types.lookup n = none := by
    rw [List.lookup_eq_none_iff]
    rw [← allocate_domain p s vs nt nm] at h
    exact fun entry he => by
      simpa only [bne_iff_ne] using
        (fun (hn : n = entry.1) => h (List.mem_map.mpr ⟨entry, he, hn.symm⟩))
  simp [Substitution.type, absent]

theorem prepare_fixes (p : SchemePreparation.Prepared) (s : ComparisonShapeSolver.Solved)
    (v : TypeVar) (h : ComparisonShapeSolver.sourceAllowed p v = false) :
    (prepare p s).substitution.type v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply allocate_fixes
    simp only [List.mem_range']
    simp [ComparisonShapeSolver.sourceAllowed] at h
    omega

end ModalityInference.ComparisonSkeleton
