import ModalityInference.ComparisonCapsuleContext
import ModalityInference.Proofs.ComparisonExactContext
import ModalityInference.Proofs.BoundedSupport
import ModalityInference.Proofs.SchemeModeWitness

namespace ModalityInference.ComparisonCapsuleContext

theorem bounded_iff (p : Prepared) (action : Substitution) :
    bounded p action = true ↔ action.Bounded p.nextType p.nextMode := by
  simp only [bounded, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    TypeExpr.mem_typeVariables, TypeExpr.mem_modeVariables, ModExpr.mem_freeVariables,
    Prod.forall, and_assoc]
  constructor
  · rintro ⟨ht, hm⟩
    exact ⟨fun n t h => ⟨(ht n t h).1, (TypeExpr.bounded_iff t _ _).mpr (ht n t h).2⟩,
      fun n m h => ⟨(hm n m h).1, (ModExpr.bounded_iff m _).mpr (hm n m h).2⟩⟩
  · intro h
    exact ⟨fun n t ht => ⟨(h.types n t ht).1, (TypeExpr.bounded_iff t _ _).mp (h.types n t ht).2⟩,
      fun n m hm => ⟨(h.modes n m hm).1, (ModExpr.bounded_iff m _).mp (h.modes n m hm).2⟩⟩

theorem prepare_scoped {fuel : Nat} {p : Prepared} {total : ModExpr → Bool}
    {action : Substitution} (h : prepare fuel p total = .success (some action)) :
    ComparisonExactContext.Scoped p action ∧ action.Bounded p.nextType p.nextMode := by
  simp only [prepare, bind, pure, RunResult.bind] at h
  split at h
  · cases h
  · split at h
    · split at h
      · next hc =>
        cases h
        exact ⟨(ComparisonExactContext.scopeCheck_iff _ _).mp (Bool.and_eq_true_iff.mp hc).1,
          (bounded_iff _ _).mp (Bool.and_eq_true_iff.mp hc).2⟩
      · cases h
    · contradiction
    · contradiction

end ModalityInference.ComparisonCapsuleContext
