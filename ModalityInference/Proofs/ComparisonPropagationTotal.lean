import ModalityInference.Proofs.ComparisonEliminationSoundness
import ModalityInference.Proofs.ComparisonAbsorption

/-! Totality certificates used before composing partial annotation images. -/
namespace ModalityInference

namespace SchemeModeSynthesis

theorem run_mode_defined {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) (Δ : Bounds) (v : ModVar) :
    Entails Δ (.defined (result.substitution.mode v)) := by
  intro η _
  obtain ⟨τ, ht, _⟩ := run_actual h η
  simp only [ModExpr.WellFormed, ht v, Option.isSome_some]

theorem run_mode_submode {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) (Δ : Bounds) (v : ModVar) :
    Submode Δ (result.substitution.mode v) (result.substitution.mode v) :=
  .refl (run_mode_defined h Δ v)

theorem run_mode_fixed {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result) {n : Nat} (hn : n ∉ modeIds) :
    result.substitution.mode (.flex n) = .var (.flex n) :=
  result.substitution.mode_fresh (by simpa only [(run_domain h).2.1] using hn)

end SchemeModeSynthesis

namespace ComparisonBody

theorem isTotal_synthesized {fuel modeFuel modeIds formula result Δ expressions known m}
    (hk : knownTotal fuel Δ expressions = .success known)
    (hs : SchemeModeSynthesis.run modeFuel modeIds formula = .success result)
    (hf : ∀ v ∈ Δ.modVars, result.substitution.mode v = .var v)
    (hm : isTotal known m = true) :
    Submode Δ (m.subst result.substitution.mode) (m.subst result.substitution.mode) := by
  apply Submode.refl
  apply ComparisonElimination.synthesized_label_defined
  · intro η hη
    exact isTotal_defined (knownTotal_sound hk) hm _
      (ComparisonElimination.synthesized_original_models hs hf hη)
  · exact ComparisonElimination.synthesized_actual hs

end ComparisonBody

namespace ComparisonAbsorption

theorem transparent_support {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {m : ModExpr} (h : transparent p total m = true) :
    ∀ v ∈ m.vars, ∀ n, v = .flex n → sourceMode p n = false := by
  simp only [transparent, Bool.and_eq_true, List.all_eq_true] at h
  intro v hv n he
  subst v
  have ht := h.2 (.flex n) ((ModExpr.mem_freeVariables m (.flex n)).mpr hv)
  simpa using ht

theorem transparent_subst_eq {p : SchemePreparation.Prepared} {total : ModExpr → Bool}
    {m : ModExpr} {left right : ModVar → ModExpr} (h : transparent p total m = true)
    (he : ∀ v, (∀ n, v = .flex n → sourceMode p n = false) → left v = right v) :
    m.subst left = m.subst right :=
  m.subst_congr (fun v hv => he v (transparent_support h v hv))

theorem transparent_synthesized {fuel modeFuel modeIds formula result p expressions known m}
    (hk : ComparisonBody.knownTotal fuel p.assumptions expressions = .success known)
    (hs : SchemeModeSynthesis.run modeFuel modeIds formula = .success result)
    (hf : ∀ v ∈ p.assumptions.modVars, result.substitution.mode v = .var v)
    (hm : transparent p (ComparisonBody.isTotal known) m = true)
    (restored : ModVar → ModExpr)
    (he : ∀ v, (∀ n, v = .flex n → sourceMode p n = false) →
      restored v = result.substitution.mode v) :
    Submode p.assumptions (m.subst restored) (m.subst restored) := by
  rw [transparent_subst_eq hm he]
  simp only [transparent, Bool.and_eq_true] at hm
  exact ComparisonBody.isTotal_synthesized hk hs hf hm.1

end ComparisonAbsorption

end ModalityInference
