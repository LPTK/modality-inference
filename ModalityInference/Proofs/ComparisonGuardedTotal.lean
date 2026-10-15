import ModalityInference.Proofs.ComparisonBoundDefinedness
import ModalityInference.Proofs.ComparisonBody
import ModalityInference.ComparisonGuardedTotal
import ModalityInference.Proofs.ComparisonReductionSupport
import ModalityInference.Proofs.ComparisonEliminationSoundness

/-! Totality classification under guarded source constraints. -/

namespace ModalityInference

theorem CompareTy.defined_ofTy_subst_guard {a : Ty} {ts : TypeVar → CompareTy}
    {ms : ModVar → ModExpr} {Δ : Bounds}
    (h : ((ofTy a).subst ts ms).DefinedUnder Δ) :
    ∀ m, Constraint.defined m ∈ a.wellFormedBounds →
      Entails Δ (.defined (m.subst ms)) := by
  induction a with
  | var | unit | credit => simp [TypeExpr.wellFormedBounds]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [ofTy, subst, definedUnder_prod_iff, definedUnder_sum_iff,
      definedUnder_fn_iff] at h
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact iha h.1 m hm
    · exact ihb h.2 m hm
  | modal a n ih =>
    rw [ofTy, subst, definedUnder_modal_iff] at h
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ih h.1 m hm
    · obtain rfl := Constraint.defined.inj (List.mem_singleton.mp hm)
      exact h.2

namespace ComparisonGuardedTotal

theorem scalarBounds_models (bounds : Bounds) (η : ModVar → Mode) :
    ModeModels (scalarBounds bounds) η ↔ ModeModels bounds.assumptions η := by
  constructor
  · intro h c hc
    cases c <;> try trivial
    all_goals exact h _ (List.mem_filter.mpr ⟨hc, rfl⟩)
  · exact fun h c hc => h c (List.mem_filter.mp hc).1

theorem scalarBounds_modVars (bounds : Bounds) :
    (scalarBounds bounds).modVars ⊆ bounds.modVars := by
  intro v hv
  obtain ⟨c, hc, hv⟩ := (Bounds.mem_modVars_iff _ _).mp hv
  obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp (List.mem_filter.mp hc).1
  exact d.assumptions_modeSupport
    (fun v hv => (bounds.mem_modVars_iff v).mpr ⟨d, hd, hv⟩) c hc v hv

theorem scalarBounds_modeSupport {bounds : Bounds} {Q : ModVar → Prop}
    (h : ∀ c ∈ bounds, ∀ v ∈ c.modVars, Q v) :
    ∀ c ∈ scalarBounds bounds, ∀ v ∈ c.modVars, Q v := by
  intro c hc v hv
  obtain ⟨d, hd, hv⟩ := (bounds.mem_modVars_iff v).mp
    (scalarBounds_modVars bounds ((Bounds.mem_modVars_iff _ _).mpr ⟨c, hc, hv⟩))
  exact h d hd v hv

def valuation (images : ModVar → ModExpr) (η : ModVar → Mode) : ModVar → Mode :=
  fun v => ((images v).eval (some ∘ η)).getD Mode.identity

theorem valuation_eval {images : ModVar → ModExpr} {η : ModVar → Mode} {v : ModVar}
    (h : (images v).WellFormed η) :
    (images v).eval (some ∘ η) = some (valuation images η v) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  simp [valuation, hx]

theorem eval_subst_valuation {images : ModVar → ModExpr} {η : ModVar → Mode}
    {m : ModExpr} (h : ∀ v ∈ m.vars, (images v).WellFormed η) :
    (m.subst images).eval (some ∘ η) = m.eval (some ∘ valuation images η) := by
  rw [ModExpr.eval_subst]
  exact m.eval_congr (fun v hv => valuation_eval (h v hv))

theorem valuation_original {Δ : Bounds} {images : ModVar → ModExpr}
    (hf : ∀ v ∈ Δ.modVars, images v = .var v)
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    ModeModels Δ (valuation images η) := by
  apply (ModeModels.congr Δ ?_).mp hη
  intro v hv
  simp [valuation, hf v hv, ModExpr.eval]

theorem wellFormed_valuation {images : ModVar → ModExpr} {η : ModVar → Mode}
    {m : ModExpr} (h : (m.subst images).WellFormed η) :
    m.WellFormed (valuation images η) := by
  change (m.eval (some ∘ valuation images η)).isSome = true
  rw [← eval_subst_valuation (fun v hv => h.subst_var hv)]
  exact h

theorem below_valuation {images : ModVar → ModExpr} {η : ModVar → Mode}
    {a b : ModExpr} (h : ModExpr.Below η (a.subst images) (b.subst images)) :
    ModExpr.Below (valuation images η) a b := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  have ha : (a.subst images).WellFormed η := by simp [ModExpr.WellFormed, hx]
  have hb : (b.subst images).WellFormed η := by simp [ModExpr.WellFormed, hy]
  refine ⟨x, y, ?_, ?_, hxy⟩
  · exact (eval_subst_valuation (fun v hv => ha.subst_var hv)).symm.trans hx
  · exact (eval_subst_valuation (fun v hv => hb.subst_var hv)).symm.trans hy

theorem type_guards_valuation {Δ : Bounds} {σ : CompareSubstitution} {a : Ty}
    (h : (σ.ty a).DefinedUnder Δ) {η : ModVar → Mode} (hη : ModeModels Δ η) :
    ModeModels a.wellFormedBounds (valuation σ.mode η) := by
  intro c hc
  obtain ⟨m, rfl⟩ := a.wellFormedBounds_is_defined c hc
  exact wellFormed_valuation (CompareTy.defined_ofTy_subst_guard h m hc η hη)

theorem constraint_guards_valuation {Δ : Bounds} {σ : CompareSubstitution} {c : Constraint}
    (h : AlgebraEntails Δ (σ.constraint c)) {η : ModVar → Mode} (hη : ModeModels Δ η) :
    ModeModels c.assumptions (valuation σ.mode η) := by
  cases c with
  | sub a b =>
    have ha := type_guards_valuation h.2.1 hη
    have hb := type_guards_valuation h.2.2 hη
    simpa [Constraint.assumptions, ModeModels, ModeSatisfies, or_imp, forall_and] using
      And.intro ha hb
  | equiv a b =>
    have ha := type_guards_valuation h.2.2.1 hη
    have hb := type_guards_valuation h.2.2.2 hη
    simpa [Constraint.assumptions, ModeModels, ModeSatisfies, or_imp, forall_and] using
      And.intro ha hb
  | equal v a =>
    have hh := (CompareSubstitution.algebra_equal_iff σ Δ v a).mp h
    simpa [Constraint.assumptions, ModeModels, ModeSatisfies] using
      type_guards_valuation hh.1.2.2 hη
  | mode a b =>
    simpa [Constraint.assumptions, ModeModels, ModeSatisfies] using
      below_valuation (h.denote hη)
  | defined m =>
    simpa [Constraint.assumptions, ModeModels, ModeSatisfies] using
      wellFormed_valuation (h η hη)

theorem bounds_guards_valuation {Δ guards : Bounds} {σ : CompareSubstitution}
    (h : AlgebraEntailsAll Δ (σ.bounds guards))
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    ModeModels guards.assumptions (valuation σ.mode η) := by
  intro c hc
  obtain ⟨d, hd, hc⟩ := List.mem_flatMap.mp hc
  exact constraint_guards_valuation (h _ (List.mem_map.mpr ⟨d, hd, rfl⟩)) hη c hc

/-- Adding the scalar projection preserves every original guarded witness,
including witnesses with partial images outside the source bounds. -/
theorem scalarBounds_entails {Δ guards : Bounds} {σ : CompareSubstitution}
    (h : AlgebraEntailsAll Δ (σ.bounds guards)) :
    AlgebraEntailsAll Δ (σ.bounds (scalarBounds guards)) := by
  intro d hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
  have hs : ∀ v ∈ c.modVars, Entails Δ (.defined (σ.mode v)) := by
    intro v hv
    exact h.bounds_support_defined.2 v
      (scalarBounds_modVars guards ((Bounds.mem_modVars_iff _ _).mpr ⟨c, hc, hv⟩))
  have hc := List.mem_filter.mp hc
  cases c with
  | sub | equiv | equal => simp at hc
  | mode a b =>
    apply Submode.valid
    intro η hη
    have hmodel := bounds_guards_valuation h hη (.mode a b) hc.1
    obtain ⟨x, y, hx, hy, hxy⟩ := hmodel
    refine ⟨x, y, ?_, ?_, hxy⟩
    · exact (eval_subst_valuation (fun v hv =>
        hs v (Finset.mem_union_left _ hv) η hη)).trans hx
    · exact (eval_subst_valuation (fun v hv =>
        hs v (Finset.mem_union_right _ hv) η hη)).trans hy
  | defined m =>
    intro η hη
    have hmodel := bounds_guards_valuation h hη (.defined m) hc.1
    change ((m.subst σ.mode).eval (some ∘ η)).isSome = true
    rw [eval_subst_valuation (fun v hv => hs v hv η hη)]
    exact hmodel

/-- Guarded source bounds justify scalar totality after the same shared
substitution. Body-only partial images outside the expression remain unrestricted. -/
theorem defined_subst {Δ guards : Bounds} {σ : CompareSubstitution} {m : ModExpr}
    (h : Entails (Δ ++ guards.assumptions) (.defined m))
    (hb : AlgebraEntailsAll Δ (σ.bounds guards))
    (hf : ∀ v ∈ Δ.modVars, σ.mode v = .var v)
    (hm : ∀ v ∈ m.vars, v ∉ guards.modVars → Entails Δ (.defined (σ.mode v))) :
    Entails Δ (.defined (m.subst σ.mode)) := by
  intro η hη
  have hvars : ∀ v ∈ m.vars, (σ.mode v).WellFormed η := by
    intro v hv
    by_cases hg : v ∈ guards.modVars
    · exact hb.bounds_support_defined.2 v hg η hη
    · exact hm v hv hg η hη
  have hmodel : ModeModels (Δ ++ guards.assumptions) (valuation σ.mode η) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact valuation_original hf hη c hc
    · exact bounds_guards_valuation hb hη c hc
  change ((m.subst σ.mode).eval (some ∘ η)).isSome = true
  rw [eval_subst_valuation hvars]
  exact h _ hmodel

theorem knownTotal_subst {fuel : Nat} {Δ guards : Bounds} {σ : CompareSubstitution}
    {expressions known : List ModExpr} {m : ModExpr}
    (hk : ComparisonBody.knownTotal fuel (Δ ++ guards.assumptions) expressions = .success known)
    (hb : AlgebraEntailsAll Δ (σ.bounds guards))
    (hf : ∀ v ∈ Δ.modVars, σ.mode v = .var v)
    (hm : ∀ v ∈ m.vars, v ∉ guards.modVars → Entails Δ (.defined (σ.mode v)))
    (ht : ComparisonBody.isTotal known m = true) :
    Entails Δ (.defined (m.subst σ.mode)) :=
  defined_subst (ComparisonBody.isTotal_defined (ComparisonBody.knownTotal_sound hk) ht)
    hb hf hm

/-- The scalar projection is checked before reconstructing the source type
bounds, so using it to justify totality introduces no circular proof obligation. -/
theorem isTotal_synthesized
    {fuel modeFuel totalFuel p shapes templates reduced result modeIds modes guards expressions known m}
    (hk : ComparisonBody.knownTotal totalFuel (p.assumptions ++ guards.assumptions)
      expressions = .success known)
    (he : ComparisonElimination.run fuel p shapes templates reduced = .success result)
    (hs : SchemeModeSynthesis.run modeFuel modeIds result.query = .success modes)
    (hf : ∀ v ∈ p.assumptions.modVars, modes.substitution.mode v = .var v)
    (hg : scalarBounds guards ⊆ reduced.modes)
    (ht : ComparisonBody.isTotal known m = true) :
    Submode p.assumptions (m.subst modes.substitution.mode) (m.subst modes.substitution.mode) := by
  apply Submode.refl
  apply ComparisonElimination.synthesized_label_defined ?_
    (ComparisonElimination.synthesized_actual hs)
  intro η hη
  have hmodels := ComparisonElimination.synthesized_guards he hs hf hη
  apply ComparisonBody.isTotal_defined (ComparisonBody.knownTotal_sound hk) ht
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hmodels.1 c hc
  · exact (scalarBounds_models guards _).mp (fun d hd => hmodels.2 d (hg hd)) c hc

end ComparisonGuardedTotal
end ModalityInference
