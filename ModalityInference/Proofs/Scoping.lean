import ModalityInference.Core.Scoping

/-! De Bruijn renaming and capture-avoiding substitution preserve term scope. -/
namespace ModalityInference

private def ScopedAt (n : Nat) : Term A → Prop
  | .var i => i < n
  | .unit => True
  | .lam _ t => ScopedAt (n + 1) t
  | .app a b | .pair a b | .stackPair a b => ScopedAt n a ∧ ScopedAt n b
  | .inl t | .inr t | .region t => ScopedAt n t
  | .defn a b => ScopedAt n a ∧ ScopedAt (n + 1) b
  | .split a b => ScopedAt n a ∧ ScopedAt (n + 3) b
  | .case a b c => ScopedAt n a ∧ ScopedAt (n + 1) b ∧ ScopedAt (n + 1) c
  | .reuse a b c => ScopedAt n a ∧ ScopedAt n b ∧ ScopedAt n c

private theorem scopedAt_iff (t : Term A) (n d : Nat) :
    ScopedAt (n + d) t ↔ ∀ i ∈ t.freeVars d, i < n := by
  induction t generalizing n d <;>
    simp_all [ScopedAt, Term.freeVars, Nat.add_assoc, or_imp, forall_and]
  split_ifs <;> simp_all <;> omega

private theorem liftRenaming_bound {ρ : Nat → Nat} {n k d : Nat}
    (hρ : ∀ i < n, ρ i < k) : ∀ i < n + d, Term.liftRenaming d ρ i < k + d := by
  intro i hi
  simp only [Term.liftRenaming]
  split_ifs with h
  · omega
  · have := hρ (i - d) (by omega)
    omega

private theorem scopedAt_rename {t : Term A} {n k : Nat} {ρ : Nat → Nat}
    (ht : ScopedAt n t) (hρ : ∀ i < n, ρ i < k) : ScopedAt k (t.rename ρ) := by
  induction t generalizing n k ρ <;> simp only [ScopedAt, Term.rename] at *
  all_goals aesop (add safe apply liftRenaming_bound)

private theorem liftSubstitution_scopedAt {σ : Nat → Term A} {n k d : Nat}
    (hσ : ∀ i < n, ScopedAt k (σ i)) :
    ∀ i < n + d, ScopedAt (k + d) (Term.liftSubstitution d σ i) := by
  intro i hi
  simp only [Term.liftSubstitution]
  split_ifs with h
  · change i < k + d
    omega
  · apply scopedAt_rename (hσ (i - d) (by omega))
    omega

private theorem scopedAt_subst {t : Term A} {n k : Nat} {σ : Nat → Term A}
    (ht : ScopedAt n t) (hσ : ∀ i < n, ScopedAt k (σ i)) : ScopedAt k (t.subst σ) := by
  induction t generalizing n k σ <;> simp only [ScopedAt, Term.subst] at *
  case var i => exact hσ i ht
  case lam a t ih => exact ih ht (liftSubstitution_scopedAt hσ)
  case app a b iha ihb => exact ⟨iha ht.1 hσ, ihb ht.2 hσ⟩
  case pair a b iha ihb => exact ⟨iha ht.1 hσ, ihb ht.2 hσ⟩
  case stackPair a b iha ihb => exact ⟨iha ht.1 hσ, ihb ht.2 hσ⟩
  case inl a ih => exact ih ht hσ
  case inr a ih => exact ih ht hσ
  case region a ih => exact ih ht hσ
  case defn a b iha ihb => exact ⟨iha ht.1 hσ, ihb ht.2 (liftSubstitution_scopedAt hσ)⟩
  case split a b iha ihb => exact ⟨iha ht.1 hσ, ihb ht.2 (liftSubstitution_scopedAt hσ)⟩
  case case a b c iha ihb ihc =>
    exact ⟨iha ht.1 hσ, ihb ht.2.1 (liftSubstitution_scopedAt hσ),
      ihc ht.2.2 (liftSubstitution_scopedAt hσ)⟩
  case reuse a b c iha ihb ihc => exact ⟨iha ht.1 hσ, ihb ht.2.1 hσ, ihc ht.2.2 hσ⟩

theorem Term.subst_scoped (t : Term A) (σ : Nat → Term A) (n k : Nat)
    (ht : t.Scoped n) (hσ : ∀ i < n, (σ i).Scoped k) : (t.subst σ).Scoped k := by
  exact (scopedAt_iff _ k 0).mp (scopedAt_subst ((scopedAt_iff t n 0).mpr ht)
    (fun i hi => (scopedAt_iff (σ i) k 0).mpr (hσ i hi)))

theorem Term.rename_scoped (t : Term A) (ρ : Nat → Nat) (n k : Nat)
    (ht : t.Scoped n) (hρ : ∀ i < n, ρ i < k) : (t.rename ρ).Scoped k := by
  exact (scopedAt_iff _ k 0).mp (scopedAt_rename ((scopedAt_iff t n 0).mpr ht) hρ)

end ModalityInference
