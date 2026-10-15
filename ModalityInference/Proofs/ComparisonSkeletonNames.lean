import ModalityInference.Proofs.ComparisonWitnessShapes

namespace ModalityInference.ComparisonSkeleton

theorem leaves_names_nodup (p : SchemePreparation.Prepared) (shape : ComparisonShape) (nt : Nat) :
    ((leaves p shape nt).map (·.name)).Nodup := by
  induction shape generalizing nt with
  | var v => simp [leaves]; split <;> simp
  | unit | credit => simp [leaves]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [leaves, List.map_append, List.nodup_append]
    refine ⟨iha nt, ihb _, ?_⟩
    intro na ha nb hb heq
    obtain ⟨la, hla_mem, he_a⟩ := List.mem_map.mp ha
    obtain ⟨lb, hlb_mem, he_b⟩ := List.mem_map.mp hb
    have hla := (leaves_range p a nt la hla_mem).2
    have hlb := (leaves_range p b (nt + typeCount p a) lb hlb_mem).1
    omega

theorem allocate_leaf_names_nodup (p : SchemePreparation.Prepared)
    (shapes : ComparisonShapeSolver.Solved) (names : List Nat) (nt nm : Nat) :
    ((allocate p shapes names nt nm).leaves.map (·.name)).Nodup := by
  induction names generalizing nt nm with
  | nil => simp [allocate]
  | cons name names ih =>
    simp only [allocate, List.map_append, List.nodup_append]
    refine ⟨leaves_names_nodup p _ nt, ih _ _, ?_⟩
    intro na ha nb hb heq
    obtain ⟨la, hla_mem, he_a⟩ := List.mem_map.mp ha
    obtain ⟨lb, hlb_mem, he_b⟩ := List.mem_map.mp hb
    have hla := (leaves_range p (shapes.resolveAll (.flex name)) nt la hla_mem).2
    have hlb := (allocate_leaf_range p shapes names
      (nt + typeCount p (shapes.resolveAll (.flex name)))
      (nm + modeCount p (shapes.resolveAll (.flex name))) lb hlb_mem).1
    omega

end ModalityInference.ComparisonSkeleton
