import ModalityInference.Proofs.ResourceRestriction
import Mathlib.Data.Finset.Preimage

/-! Restriction to the same used indices preserves all context relations. -/
namespace ModalityInference

@[simp] theorem Context.restrict_cons (s : Option Scheme) (Γ : Context) (used : Finset Nat) :
    Context.restrict (s :: Γ) used = (if 0 ∈ used then s else none) ::
      Γ.restrict (used.preimage Nat.succ Nat.succ_injective.injOn) := by
  simp [Context.restrict, List.mapIdx_cons]

@[simp] theorem Context.restrict_nil (used : Finset Nat) : Context.restrict [] used = [] := rfl

theorem Lock.restrict {Δ m Γ Γ'} (h : Lock Δ m Γ Γ') (used : Finset Nat) :
    Lock Δ m (Γ.restrict used) (Γ'.restrict used) := by
  induction h generalizing used
  all_goals simp only [Context.restrict_cons, Context.restrict_nil]
  all_goals try split_ifs
  all_goals solve_by_elim [Lock.nil, Lock.unused, Lock.keep, Lock.unavailable]

theorem ContextLe.restrict {Δ Γ Γ'} (h : ContextLe Δ Γ Γ') (used : Finset Nat) :
    ContextLe Δ (Γ.restrict used) (Γ'.restrict used) := by
  induction h generalizing used
  all_goals simp only [Context.restrict_cons, Context.restrict_nil]
  all_goals try split_ifs
  all_goals solve_by_elim [ContextLe.nil, ContextLe.drop, ContextLe.keep]

theorem ContextJoin.restrict {Δ Γ Γ₁ Γ₂} (h : ContextJoin Δ Γ₁ Γ₂ Γ) (used : Finset Nat) :
    ContextJoin Δ (Γ₁.restrict used) (Γ₂.restrict used) (Γ.restrict used) := by
  induction h generalizing used
  all_goals simp only [Context.restrict_cons, Context.restrict_nil]
  all_goals try split_ifs
  all_goals solve_by_elim [ContextJoin.nil, ContextJoin.unused, ContextJoin.left,
    ContextJoin.right, ContextJoin.shared]

end ModalityInference
