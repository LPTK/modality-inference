import ModalityInference.Proofs.ConstraintSubstitution
import ModalityInference.Proofs.SubstitutionWellFormed

/-! A defined instantiated type or constraint supplies defined images for every
variable it actually mentions. Definedness of unused quantified images is a
separate requirement of admissible instantiation. -/
namespace ModalityInference

theorem ModExpr.eval_vars_defined (m : ModExpr) {η : ModVar → Option Mode} {n : Mode}
    (h : m.eval η = some n) {v : ModVar} (hv : v ∈ m.vars) : (η v).isSome = true := by
  induction m generalizing n <;> simp only [ModExpr.eval, bind, pure,
    Option.bind_eq_some_iff, ModExpr.vars, Finset.mem_singleton,
    Finset.mem_union] at *
  all_goals aesop

theorem ModExpr.WellFormed.subst_var {m : ModExpr} {ms : ModVar → ModExpr} {η v}
    (h : (m.subst ms).WellFormed η) (hv : v ∈ m.vars) : (ms v).WellFormed η := by
  exact let ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
    m.eval_vars_defined (η := fun v => (ms v).eval (some ∘ η))
      (by simpa only [ModExpr.eval_subst] using hn) hv

theorem TypeExpr.DefinedUnder.subst_types {a : Ty} {ts : TypeVar → Ty} {ms : ModVar → ModExpr} {Δ}
    (h : (a.subst ts ms).DefinedUnder Δ) : ∀ v ∈ a.typeVars, (ts v).DefinedUnder Δ := by
  induction a <;> simp_all [TypeExpr.subst, TypeExpr.typeVars, or_imp]

theorem TypeExpr.DefinedUnder.subst_modes {a : Ty} {ts : TypeVar → Ty} {ms : ModVar → ModExpr} {Δ}
    (h : (a.subst ts ms).DefinedUnder Δ) :
    ∀ v ∈ a.modVars, ∀ η, ModeModels Δ η → (ms v).WellFormed η := by
  induction a <;> simp_all [TypeExpr.subst, TypeExpr.modVars, or_imp]
  exact fun v hv η hη => (h.2 η hη).subst_var hv

theorem Entails.subst_types_defined {c : Constraint} {ts : TypeVar → Ty}
    {ms : ModVar → ModExpr} {Δ} (h : Entails Δ (c.subst ts ms)) :
    ∀ v ∈ c.typeVars, (ts v).DefinedUnder Δ := by
  cases c <;> simp_all [Constraint.typeVars, or_imp, forall_and]
  case sub => exact ⟨h.2.1.subst_types, h.2.2.subst_types⟩
  case equal => exact ⟨h.2.2.1, h.2.2.2.subst_types⟩
  case equiv => exact ⟨h.2.2.1.subst_types, h.2.2.2.subst_types⟩

theorem Entails.subst_modes_defined {c : Constraint} {ts : TypeVar → Ty}
    {ms : ModVar → ModExpr} {Δ} (h : Entails Δ (c.subst ts ms)) :
    ∀ v ∈ c.modVars, ∀ η, ModeModels Δ η → (ms v).WellFormed η := by
  cases c <;> simp_all [Constraint.modVars, or_imp, forall_and]
  case sub => exact ⟨h.2.1.subst_modes, h.2.2.subst_modes⟩
  case equal => exact h.2.2.2.subst_modes
  case equiv => exact ⟨h.2.2.1.subst_modes, h.2.2.2.subst_modes⟩
  case defined => exact fun v hv η hη => (h η hη).subst_var hv
  case mode =>
    constructor
    · intro v hv η hη
      obtain ⟨x, _, hx, _, _⟩ := h.denote hη
      exact (ModExpr.WellFormed.subst_var (Option.isSome_iff_exists.mpr ⟨x, hx⟩) hv)
    · intro v hv η hη
      obtain ⟨_, y, _, hy, _⟩ := h.denote hη
      exact (ModExpr.WellFormed.subst_var (Option.isSome_iff_exists.mpr ⟨y, hy⟩) hv)

theorem Scheme.instance_support_defined {s : Scheme} {θ : Substitution} {Δ}
    (hb : EntailsAll Δ (θ.bounds s.bounds)) (hd : (θ.ty s.body).DefinedUnder Δ) :
    (∀ v ∈ s.body.typeVars ∪ s.bounds.typeVars, (θ.type v).DefinedUnder Δ) ∧
    (∀ v ∈ s.body.modVars ∪ s.bounds.modVars, ∀ η, ModeModels Δ η → (θ.mode v).WellFormed η) := by
  exact ⟨fun v hv => (Finset.mem_union.mp hv).elim (hd.subst_types v)
    (fun hv => let ⟨c, hc, hv⟩ := (s.bounds.mem_typeVars_iff v).mp hv
      ((θ.constraint_subst_entails c Δ).mp (hb _ (List.mem_map.mpr ⟨c, hc, rfl⟩))).subst_types_defined v hv),
    fun v hv => (Finset.mem_union.mp hv).elim (hd.subst_modes v)
    (fun hv => let ⟨c, hc, hv⟩ := (s.bounds.mem_modVars_iff v).mp hv
      ((θ.constraint_subst_entails c Δ).mp (hb _ (List.mem_map.mpr ⟨c, hc, rfl⟩))).subst_modes_defined v hv)⟩

end ModalityInference
