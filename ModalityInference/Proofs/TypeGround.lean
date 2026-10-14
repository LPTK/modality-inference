import ModalityInference.Proofs.ModeGround
import ModalityInference.Proofs.SolverShape
import ModalityInference.Proofs.SolverFlexible

/-! Ground solutions prevent rejection of flexible type constraints. -/
namespace ModalityInference

theorem TypeExpr.shapeUnder_structural_occurs_lt (a : Ty) (ρ : TypeVar → Ty) {v}
    (hv : v ∈ a.typeVars) (hvar : ∀ w, a ≠ .var w) (hmodal : ∀ b m, a ≠ .modal b m) :
    (ρ v).shapeSize < (a.shapeUnder ρ).shapeSize := by
  cases a <;> simp_all [TypeExpr.typeVars, TypeExpr.shapeUnder, TypeExpr.shapeSize]
  all_goals rcases hv with hv | hv
  all_goals have hh := TypeExpr.shapeUnder_occurs_le _ ρ hv
  all_goals omega

namespace SolverShape

theorem stepType_succeeds {ρ : TypeVar → Ty} {s : SolverState} {a b : Ty}
    (ha : a.Flexible) (hb : b.Flexible) (hc : a.shapeUnder ρ = b.shapeUnder ρ) :
    ∃ t, stepType s a b = .success t := by
  have ho : a.outer.1.shapeUnder ρ = b.outer.1.shapeUnder ρ := by simpa using hc
  have hfa := ha.outer.1
  have hfb := hb.outer.1
  have hma := a.outer_not_modal
  have hmb := b.outer_not_modal
  simp only [stepType, bind, pure, RunResult.bind]
  repeat' split
  all_goals try exact ⟨_, rfl⟩
  case h_2.isTrue =>
    rename_i x y n he hnv hocc
    have hlt := b.outer.1.shapeUnder_structural_occurs_lt ρ (by simpa using hocc) hnv hmb
    have heq : ρ (.flex n) = b.outer.1.shapeUnder ρ := by simpa only [he, TypeExpr.shapeUnder] using ho
    rw [← heq] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)
  case h_3.isTrue =>
    rename_i x y n he hnv hnf hocc
    have hlt := a.outer.1.shapeUnder_structural_occurs_lt ρ (by simpa using hocc) hnv hma
    have heq : ρ (.flex n) = a.outer.1.shapeUnder ρ := by simpa only [he, TypeExpr.shapeUnder] using ho.symm
    rw [← heq] at hlt
    exact False.elim (Nat.lt_irrefl _ hlt)
  case h_9 =>
    have hnva : ∀ v, a.outer.1 ≠ .var v := by
      intro v hv
      cases v <;> simp_all [TypeExpr.Flexible]
    have hnvb : ∀ v, b.outer.1 ≠ .var v := by
      intro v hv
      cases v <;> simp_all [TypeExpr.Flexible]
    cases hea : a.outer.1 <;> cases heb : b.outer.1 <;>
      simp_all [TypeExpr.shapeUnder]
    all_goals grind

end SolverShape
end ModalityInference
