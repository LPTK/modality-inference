import ModalityInference.Proofs.ComparisonGroupExtraction

/-! Collected shape classes partition the finite opaque-leaf substitution. -/
namespace ModalityInference.ComparisonGroups

theorem collect_classes_nodup {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups) :
    (groups.map Group.shapeClass).Nodup := by
  unfold collect at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first
    | contradiction
    | (split at h <;> try simp only at h)
  · cases h
    simp only [List.map_map, Function.comp_def]
    simpa using (List.nodup_dedup (α := TypeVar) _)
  · have hnone := RunResult.forIn_preserves
      (fun r : MProd (Option (List Group)) PUnit => r.fst = none) (by assumption) rfl (by
        intro pair hp before after hb hs
        repeat' first
          | contradiction
          | (cases hs; rfl)
          | (split at hs <;> try simp only at hs))
    simp_all

theorem collect_nodup {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups) : groups.Nodup :=
  List.Nodup.of_map _ (collect_classes_nodup h)

theorem collect_all_leaves_nodup {p : SchemePreparation.Prepared}
    {shapes : ComparisonShapeSolver.Solved} {templates : ComparisonSkeleton.Templates}
    {reduced : ComparisonReduction.State} {groups : List Group}
    (h : collect p shapes templates reduced = .success groups)
    (hn : (templates.leaves.map (·.name)).Nodup)
    (hname : ∀ a ∈ templates.leaves, ∀ b ∈ templates.leaves, a.name = b.name → a = b) :
    (groups.flatMap Group.leaves).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨collect_leaves_nodup h hn, ?_⟩
  apply (collect_nodup h).imp_of_mem
  intro a b ha hb hne
  exact List.disjoint_left.mpr (fun n hna hnb => hne (collect_leaf_shared h hname ha hb hna hnb))

end ModalityInference.ComparisonGroups
