import ModalityInference.Proofs.GenerationInstantiation

/-! Identifier bounds and flexible support survive symbolic context operations. -/
namespace ModalityInference

def ContextEntry.Bounded (nt nm : Nat) : ContextEntry → Prop
  | .binding s => ∀ a ∈ s, a.Bounded nt nm
  | .lock m => m.Bounded nm

def ContextEntry.Flexible : ContextEntry → Prop
  | .binding s => ∀ a ∈ s, a.Flexible
  | .lock m => m.Flexible

def AlgorithmicContext.Bounded (nt nm : Nat) (Γ : AlgorithmicContext) : Prop :=
  ∀ e ∈ Γ, e.Bounded nt nm

def AlgorithmicContext.Flexible (Γ : AlgorithmicContext) : Prop :=
  ∀ e ∈ Γ, e.Flexible

@[simp] theorem AlgorithmicContext.bounded_nil (nt nm : Nat) :
    AlgorithmicContext.Bounded nt nm [] := by simp [Bounded]

@[simp] theorem AlgorithmicContext.bounded_cons {e : ContextEntry} {Γ : AlgorithmicContext} {nt nm} :
    AlgorithmicContext.Bounded nt nm (e :: Γ) ↔ e.Bounded nt nm ∧ Γ.Bounded nt nm := by
  simp [Bounded]

@[simp] theorem AlgorithmicContext.flexible_nil : AlgorithmicContext.Flexible [] := by
  simp [Flexible]

@[simp] theorem AlgorithmicContext.flexible_cons {e : ContextEntry} {Γ : AlgorithmicContext} :
    AlgorithmicContext.Flexible (e :: Γ) ↔ e.Flexible ∧ Γ.Flexible := by
  simp [Flexible]

theorem AlgorithmicContext.Bounded.mono {Γ : AlgorithmicContext} {nt nm nt' nm'}
    (hΓ : Γ.Bounded nt nm) (ht : nt ≤ nt') (hm : nm ≤ nm') : Γ.Bounded nt' nm' := by
  intro e he
  cases e with
  | binding s => exact fun a ha => (hΓ _ he a ha).mono ht hm
  | lock m => exact (hΓ _ he).mono hm

theorem lookupScheme_bounded {Γ i s nt nm} (hΓ : AlgorithmicContext.Bounded nt nm Γ)
    (h : lookupScheme Γ i = .success s) : s.Bounded nt nm := by
  have hh := lookupScheme_sound h
  clear h
  induction hh with
  | here => simpa [ContextEntry.Bounded] using (AlgorithmicContext.bounded_cons.mp hΓ).1
  | there h ih => exact ih (AlgorithmicContext.bounded_cons.mp hΓ).2
  | locked h ih =>
    exact (ih (AlgorithmicContext.bounded_cons.mp hΓ).2).lock
      (AlgorithmicContext.bounded_cons.mp hΓ).1

theorem lookupScheme_flexible {Γ i s} (hΓ : AlgorithmicContext.Flexible Γ)
    (h : lookupScheme Γ i = .success s) : s.Flexible := by
  have hh := lookupScheme_sound h
  clear h
  induction hh with
  | here => simpa [ContextEntry.Flexible] using (AlgorithmicContext.flexible_cons.mp hΓ).1
  | there h ih => exact ih (AlgorithmicContext.flexible_cons.mp hΓ).2
  | locked h ih =>
    exact (ih (AlgorithmicContext.flexible_cons.mp hΓ).2).lock
      (AlgorithmicContext.flexible_cons.mp hΓ).1

theorem UsageSplit.bounded {Γ Γ₁ Γ₂ nt nm} (h : UsageSplit Γ Γ₁ Γ₂)
    (hΓ : AlgorithmicContext.Bounded nt nm Γ) :
    AlgorithmicContext.Bounded nt nm Γ₁ ∧ AlgorithmicContext.Bounded nt nm Γ₂ := by
  induction h <;> simp_all [ContextEntry.Bounded, Scheme.Bounded, Constraint.Bounded,
    TypeExpr.Bounded, ModExpr.Bounded]

theorem UsageSplit.flexible {Γ Γ₁ Γ₂} (h : UsageSplit Γ Γ₁ Γ₂)
    (hΓ : AlgorithmicContext.Flexible Γ) :
    AlgorithmicContext.Flexible Γ₁ ∧ AlgorithmicContext.Flexible Γ₂ := by
  induction h <;> simp_all [ContextEntry.Flexible, Scheme.Flexible, Constraint.Flexible,
    TypeExpr.Flexible, ModExpr.Flexible]

end ModalityInference
