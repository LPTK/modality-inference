import ModalityInference.ComparisonCapsuleContext
import ModalityInference.Proofs.ComparisonCapsuleIntervals

namespace ModalityInference.ComparisonCapsuleContext

private theorem requests_allowed (p : Prepared) (total : ModExpr → Bool)
    (fuel : Nat) (lower : Bool) (source target : Ty) (sm tm : ModExpr)
    {r : ComparisonCapsuleIntervals.Request}
    (hr : r ∈ requests p total fuel lower source target sm tm) :
    ComparisonInstance.typeAllowed p (.flex r.name) = true := by
  induction fuel generalizing lower source target sm tm with
  | zero => simp [requests] at hr
  | succ fuel ih =>
    simp only [requests] at hr
    repeat' first
      | (simp only [List.mem_nil_iff, List.mem_singleton] at hr; subst r; assumption)
      | contradiction
      | (exact ih _ _ _ _ _ hr)
      | (rcases List.mem_append.mp hr with hr | hr)
      | split at hr

theorem mem_bindings {p : Prepared} {total : ModExpr → Bool} {b : ComparisonCapsuleIntervals.Binding}
    (hb : b ∈ bindings p total) :
    ComparisonInstance.typeAllowed p (.flex b.name) = true ∧ p.nextMode ≤ b.fresh := by
  simp only [bindings, List.mem_filterMap] at hb
  obtain ⟨⟨name, offset⟩, hn, hp⟩ := hb
  have hspec := ComparisonCapsuleIntervals.plan_spec hp
  obtain ⟨r, hr, he⟩ := List.mem_map.mp (List.mem_dedup.mp (List.fst_mem_of_mem_zipIdx hn))
  refine ⟨?_, by omega⟩
  rw [hspec.1, ← he]
  exact requests_allowed p total _ _ _ _ _ _ hr

theorem mem_mixedBindings {p : Prepared} {total : ModExpr → Bool}
    {b : ComparisonCapsuleIntervals.Binding} (hb : b ∈ mixedBindings p total) :
    ComparisonInstance.typeAllowed p (.flex b.name) = true ∧ p.nextMode ≤ b.fresh :=
  mem_bindings (List.mem_filter.mp hb).1

end ModalityInference.ComparisonCapsuleContext
