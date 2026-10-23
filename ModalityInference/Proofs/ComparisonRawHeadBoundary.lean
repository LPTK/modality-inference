import ModalityInference.Proofs.ComparisonRawHeadSupport

namespace ModalityInference.ComparisonRawHeadRestriction

def Covers (Δ : Bounds) (H : Set CompareTy) : Prop :=
  ∀ a b, .sub a b ∈ Δ →
    support Δ (.ofTy a) none ⊆ H ∧ support Δ (.ofTy b) none ⊆ H

def constraintBoundary : Constraint → List CompareTy
  | .sub a b => [.ofTy a, .ofTy b]
  | _ => []

def boundary (Δ : Bounds) (a b : CompareTy) : Set CompareTy :=
  boundarySupport Δ (a :: b :: Δ.flatMap constraintBoundary)

theorem boundary_finite (Δ : Bounds) (a b : CompareTy) : (boundary Δ a b).Finite :=
  boundarySupport_finite Δ _

theorem boundary_left (Δ : Bounds) (a b : CompareTy) : support Δ a none ⊆ boundary Δ a b :=
  support_subset_boundary (List.mem_cons_self)

theorem boundary_right (Δ : Bounds) (a b : CompareTy) : support Δ b none ⊆ boundary Δ a b :=
  support_subset_boundary (List.mem_cons_of_mem _ List.mem_cons_self)

theorem boundary_covers (Δ : Bounds) (a b : CompareTy) : Covers Δ (boundary Δ a b) := by
  intro x y hxy
  constructor
  · apply support_subset_boundary
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨.sub x y,hxy,by simp [constraintBoundary]⟩))
  · exact support_subset_boundary (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨.sub x y,hxy,by simp [constraintBoundary]⟩)))

end ModalityInference.ComparisonRawHeadRestriction
