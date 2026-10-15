import ModalityInference.ComparisonGuardedContextRegression
import ModalityInference.Proofs.ComparisonContextWitnesses

namespace ModalityInference.ComparisonGuardedContextRegression

def witness : Substitution := { types := [(0, .modal base bad)], modes := [(0, .bottom)] }

theorem ordinary_witness : Subsumes [] source target := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · simp [Instantiates, source, witness]
  · intro c hc
    simp only [Substitution.bounds, List.mem_map, source, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    obtain ⟨d, hd, rfl⟩ := hc
    rcases hd with rfl | rfl
    all_goals exact Submode.valid fun _ _ => ⟨Mode.bottom, Mode.bottom, rfl, rfl, by decide⟩
  · change Subtype [] (.modal (.modal base bad) (.leftResidual .bottom .bottom)) (.modal base bad)
    exact (Subtype.congr .refl (.valid fun _ _ =>
      ⟨Mode.bottom, Mode.identity, rfl, rfl, by decide⟩)).trans .identity

theorem algebra_witness : AlgebraSubsumes [] source target := ordinary_witness.to_algebra

theorem conditional_total : Entails source.bounds.assumptions
    (.defined (.leftResidual mu .bottom)) := by
  intro η hη
  have h := hη (.mode mu .bottom) (by simp [source, Bounds.assumptions, Constraint.assumptions])
  simp [ModeSatisfies, ModExpr.Below, mu, ModExpr.bottom, ModExpr.eval,
    Mode.le, Mode.bottom] at h
  simp [ModExpr.WellFormed, ModExpr.eval, mu, ModExpr.bottom, Mode.bottom,
    Mode.leftResidual, h.1.1, h.1.2]

end ModalityInference.ComparisonGuardedContextRegression
