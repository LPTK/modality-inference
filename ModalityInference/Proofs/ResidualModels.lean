import ModalityInference.Proofs.SolverResidual
import ModalityInference.Proofs.ModeSearch

/-! Ground witnesses for guarded residual type bounds. -/
namespace ModalityInference

def residualAssignment (η : ModVar → Mode) : GroundAssignment :=
  ⟨fun _ => .unit Mode.absorbing, η⟩

theorem TypeExpr.realize_residual {a : Ty} {v η}
    (ha : a.outer.1 = .var v) (hw : ModeModels a.wellFormedBounds η) :
    a.realize (residualAssignment η) = some (.unit Mode.absorbing) := by
  induction a <;> simp only [TypeExpr.outer] at ha
  all_goals try contradiction
  case var => rfl
  case modal a m ih =>
    have hm := hw (.defined m) (by simp [TypeExpr.wellFormedBounds])
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hm
    have hi := ih ha (fun c hc => hw c (by simp [TypeExpr.wellFormedBounds, hc]))
    simp only [TypeExpr.realize, hi]
    simp [residualAssignment, hn, GroundTy.modal,
      Mode.compose, Mode.absorbing]

theorem Residual.groundModels {cs η} (hr : Residual cs) (hm : ModeModels cs η)
    (hw : ∀ a b, Constraint.sub a b ∈ cs →
      ModeModels a.wellFormedBounds η ∧ ModeModels b.wellFormedBounds η) :
    GroundModels (residualAssignment η) cs := by
  intro c hc
  have hrc := (List.forall_iff_forall_mem.mp hr) c hc
  cases c
  case sub a b =>
    obtain ⟨x, y, m, n, ha, hb⟩ := hrc
    exact ⟨_, _, a.realize_residual (congrArg Prod.fst ha) (hw a b hc).1,
      b.realize_residual (congrArg Prod.fst hb) (hw a b hc).2, .refl⟩
  case mode | defined => exact hm _ hc
  case equal | equiv => exact False.elim hrc

end ModalityInference
