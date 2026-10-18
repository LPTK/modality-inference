import ModalityInference.Proofs.SymbolicReduction

namespace ModalityInference.SymbolicSolver

def TypeEquivalent (Δ : Bounds) (a b : Ty) : Prop := Subtype Δ a b ∧ Subtype Δ b a

theorem type_subst_equivalent {Δ : Bounds} (a : Ty) {ts us : TypeVar → Ty}
    {ms : ModVar → ModExpr} (ht : ∀ v, TypeEquivalent Δ (ts v) (us v))
    (hd : (a.subst ts ms).DefinedUnder Δ) :
    TypeEquivalent Δ (a.subst ts ms) (a.subst us ms) := by
  induction a with
  | var v => exact ht v
  | unit | credit => exact ⟨.refl, .refl⟩
  | prod a b iha ihb =>
    have hh := TypeExpr.definedUnder_prod.mp hd
    exact ⟨.prod_congr (iha hh.1).1 (ihb hh.2).1,
      .prod_congr (iha hh.1).2 (ihb hh.2).2⟩
  | sum a b iha ihb =>
    have hh := TypeExpr.definedUnder_sum.mp hd
    exact ⟨.sum_congr (iha hh.1).1 (ihb hh.2).1,
      .sum_congr (iha hh.1).2 (ihb hh.2).2⟩
  | fn a b iha ihb =>
    have hh := TypeExpr.definedUnder_fn.mp hd
    exact ⟨.fn_congr (iha hh.1).2 (ihb hh.2).1,
      .fn_congr (iha hh.1).1 (ihb hh.2).2⟩
  | modal a m ih =>
    have hh := TypeExpr.definedUnder_modal.mp hd
    exact ⟨.congr (ih hh.1).1 (.refl hh.2), .congr (ih hh.1).2 (.refl hh.2)⟩

theorem type_subst_defined {Δ : Bounds} (a : Ty) {ts us : TypeVar → Ty}
    {ms : ModVar → ModExpr} (hu : ∀ v, (us v).DefinedUnder Δ)
    (hd : (a.subst ts ms).DefinedUnder Δ) : (a.subst us ms).DefinedUnder Δ := by
  induction a with
  | var v => exact hu v
  | unit | credit => exact hd
  | prod a b iha ihb =>
    exact TypeExpr.definedUnder_prod.mpr
      ⟨iha (TypeExpr.definedUnder_prod.mp hd).1, ihb (TypeExpr.definedUnder_prod.mp hd).2⟩
  | sum a b iha ihb =>
    exact TypeExpr.definedUnder_sum.mpr
      ⟨iha (TypeExpr.definedUnder_sum.mp hd).1, ihb (TypeExpr.definedUnder_sum.mp hd).2⟩
  | fn a b iha ihb =>
    exact TypeExpr.definedUnder_fn.mpr
      ⟨iha (TypeExpr.definedUnder_fn.mp hd).1, ihb (TypeExpr.definedUnder_fn.mp hd).2⟩
  | modal a m ih =>
    exact TypeExpr.definedUnder_modal.mpr
      ⟨ih (TypeExpr.definedUnder_modal.mp hd).1, (TypeExpr.definedUnder_modal.mp hd).2⟩

theorem constraint_equivalent {Δ : Bounds} {σ τ : Substitution}
    (hw : τ.WellFormedUnder Δ) (ht : ∀ v, TypeEquivalent Δ (σ.type v) (τ.type v))
    (hm : σ.mode = τ.mode) {c : Constraint} (h : Entails Δ (σ.constraint c)) :
    Entails Δ (τ.constraint c) := by
  rw [σ.constraint_subst_entails] at h
  rw [τ.constraint_subst_entails]
  have he : ∀a : Ty, (a.subst σ.type σ.mode).DefinedUnder Δ →
      TypeEquivalent Δ (a.subst σ.type σ.mode) (a.subst τ.type τ.mode) := by
    intro a hd
    rw [← hm]
    exact type_subst_equivalent a ht hd
  have hd : ∀a : Ty, (a.subst σ.type σ.mode).DefinedUnder Δ →
      (a.subst τ.type τ.mode).DefinedUnder Δ := by
    intro a hd
    rw [← hm]
    exact type_subst_defined a hw.types hd
  cases c with
  | sub a b =>
    exact ⟨(he a h.2.1).2.trans (h.1.trans (he b h.2.2).1), hd a h.2.1, hd b h.2.2⟩
  | equiv a b | equal v b =>
    first
      | exact ⟨(he a h.2.2.1).2.trans (h.1.trans (he b h.2.2.2).1),
          (he b h.2.2.2).2.trans (h.2.1.trans (he a h.2.2.1).1),
          hd a h.2.2.1, hd b h.2.2.2⟩
      | exact ⟨(ht v).2.trans (h.1.trans (he b h.2.2.2).1),
          (he b h.2.2.2).2.trans (h.2.1.trans (ht v).1),
          hw.types v, hd b h.2.2.2⟩
  | mode a b | defined a => simpa only [Constraint.subst, hm] using h

theorem solution_equivalent {Δ cs : Bounds} {σ τ : Substitution}
    (hw : τ.WellFormedUnder Δ) (ht : ∀ v, TypeEquivalent Δ (σ.type v) (τ.type v))
    (hm : σ.mode = τ.mode) (h : Solution cs Δ σ) : Solution cs Δ τ := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact constraint_equivalent hw ht hm (h _ (List.mem_map.mpr ⟨d, hd, rfl⟩))

theorem singleType_equivalent {Δ : Bounds} {σ : Substitution} {n : Nat} {a : Ty}
    (he : Entails Δ (σ.constraint (.equal (.flex n) a))) :
    ∀v, TypeEquivalent Δ (σ.type v)
      ((σ.compose ({types := [(n, a)]} : Substitution)).type v) := by
  have hh := (σ.constraint_subst_entails _ Δ).mp he
  intro v
  rw [Substitution.type_compose]
  cases v with
  | rigid k => exact ⟨.refl, .refl⟩
  | flex k =>
    by_cases hk : k = n
    · subst k
      simpa [Substitution.type, List.lookup_cons, Substitution.ty, TypeExpr.subst] using
        (show TypeEquivalent Δ (σ.type (.flex n)) (σ.ty a) from ⟨hh.1, hh.2.1⟩)
    · simpa [Substitution.type, List.lookup_cons, Substitution.ty, TypeExpr.subst,
        beq_eq_false_iff_ne.mpr hk]
        using (show TypeEquivalent Δ (σ.type (.flex k)) (σ.type (.flex k)) from ⟨.refl, .refl⟩)

theorem singleType_wellFormed {Δ : Bounds} {σ : Substitution} {n : Nat} {a : Ty}
    (hw : σ.WellFormedUnder Δ) (ha : (σ.ty a).DefinedUnder Δ) :
    (σ.compose ({types := [(n, a)]} : Substitution)).WellFormedUnder Δ := by
  constructor
  · intro v
    rw [Substitution.type_compose]
    cases v with
    | rigid k => exact hw.types (.rigid k)
    | flex k =>
      by_cases hk : k = n
      · subst k
        simpa [Substitution.type, List.lookup_cons] using ha
      · simpa [Substitution.type, List.lookup_cons, Substitution.ty, TypeExpr.subst,
          beq_eq_false_iff_ne.mpr hk]
          using hw.types (.flex k)
  · intro v
    rw [Substitution.mode_compose]
    cases v <;> exact hw.modes _

end ModalityInference.SymbolicSolver
