import ModalityInference.Proofs.GroundSubtyping

/-! Relating declarative entailment equivalence to ground constraint models.
Type equality assumptions are exposed as both subtype directions, and internal
type assumptions retain every written modality's definedness. -/
namespace ModalityInference

theorem TypeExpr.wellFormedBounds_ground (a : Ty) (ρ : GroundAssignment) :
    GroundModels ρ a.wellFormedBounds ↔ ModeModels a.wellFormedBounds ρ.modes := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, GroundModels, ModeModels,
    GroundSatisfies, ModeSatisfies, List.mem_append, or_imp, forall_and]

theorem Constraint.assumptions_ground {c ρ} (h : GroundSatisfies ρ c) :
    GroundModels ρ c.assumptions := by
  cases c
  case sub a b | equiv a b =>
    obtain ⟨x, y, hx, hy, hs⟩ := h
    have ha := (a.wellFormedBounds_ground ρ).mpr ((a.wellFormedBounds_spec ρ).mpr (by simp [hx]))
    have hb := (b.wellFormedBounds_ground ρ).mpr ((b.wellFormedBounds_spec ρ).mpr (by simp [hy]))
    all_goals
      simpa [Constraint.assumptions, GroundModels, GroundSatisfies, hx, hy, hs,
        List.mem_append, or_imp, forall_and] using And.intro ha hb
  case equal v t =>
    obtain ⟨x, hx, hs⟩ := h
    have ht := (t.wellFormedBounds_ground ρ).mpr ((t.wellFormedBounds_spec ρ).mpr (by simp [hx]))
    simpa [Constraint.assumptions, GroundModels, GroundSatisfies, TypeExpr.realize, hx, hs,
      List.mem_append, or_imp, forall_and] using ht
  all_goals simpa [Constraint.assumptions, GroundModels] using h

theorem GroundModels.assumptions {ρ cs} (h : GroundModels ρ cs) : GroundModels ρ cs.assumptions := by
  intro d hd
  obtain ⟨c, hc, hd⟩ := List.mem_flatMap.mp hd
  exact (Constraint.assumptions_ground (h c hc)) d hd

theorem GroundModels.assumptions_right {ρ Δ cs} (h : GroundModels ρ (Δ ++ cs)) :
    GroundModels ρ (Δ ++ cs.assumptions) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h c (List.mem_append_left _ hc)
  · exact (GroundModels.assumptions (fun d hd => h d (List.mem_append_right Δ hd))) c hc

theorem Constraint.assumptions_entail (c : Constraint) {Δ : Bounds}
    (h : ∀ d ∈ c.assumptions, d ∈ Δ) : Entails Δ c := by
  cases c
  case sub a b =>
    exact ⟨.bound (h _ (by simp [Constraint.assumptions])),
      fun σ hΔ d hd => hΔ d (h d (by simp [Constraint.assumptions, hd])),
      fun σ hΔ d hd => hΔ d (h d (by simp [Constraint.assumptions, hd]))⟩
  case equiv a b =>
    exact ⟨.bound (h _ (by simp [Constraint.assumptions])),
      .bound (h _ (by simp [Constraint.assumptions])),
      fun σ hΔ d hd => hΔ d (h d (by simp [Constraint.assumptions, hd])),
      fun σ hΔ d hd => hΔ d (h d (by simp [Constraint.assumptions, hd]))⟩
  case equal v t =>
    exact ⟨.bound (h _ (by simp [Constraint.assumptions])),
      .bound (h _ (by simp [Constraint.assumptions])),
      fun σ hΔ d hd => hΔ d (h d (by simp [Constraint.assumptions, hd]))⟩
  case mode a b => exact .valid fun σ hΔ => hΔ (.mode a b) (h _ (by simp [Constraint.assumptions]))
  case defined a => exact fun σ hΔ => hΔ (.defined a) (h _ (by simp [Constraint.assumptions]))

theorem Constraint.assumptions_ground_iff (c : Constraint) (ρ : GroundAssignment) :
    GroundModels ρ c.assumptions ↔ GroundSatisfies ρ c :=
  ⟨fun h => (c.assumptions_entail fun _ hd => hd).groundSatisfies h,
    Constraint.assumptions_ground⟩

theorem Bounds.assumptions_ground_iff (cs : Bounds) (ρ : GroundAssignment) :
    GroundModels ρ cs.assumptions ↔ GroundModels ρ cs := by
  constructor
  · intro h c hc
    exact (c.assumptions_ground_iff ρ).mp
      (fun d hd => h d (List.mem_flatMap.mpr ⟨c, hc, hd⟩))
  · exact GroundModels.assumptions

theorem GroundModels.entailment_implication {cs ds : Bounds}
    (h : ∀ Δ, EntailsAll Δ cs → EntailsAll Δ ds) {ρ} (hc : GroundModels ρ cs) :
    GroundModels ρ ds := by
  let Δ := cs.flatMap Constraint.assumptions
  have he : EntailsAll Δ cs := fun c hc => c.assumptions_entail
    (fun d hd => List.mem_flatMap.mpr ⟨c, hc, hd⟩)
  have hm : GroundModels ρ Δ := by
    intro d hd
    obtain ⟨c, hc', hd⟩ := List.mem_flatMap.mp hd
    exact Constraint.assumptions_ground (hc c hc') d hd
  exact (h Δ he).groundModels hm

theorem GroundModels.entailment_equivalence {cs ds : Bounds}
    (h : ∀ Δ, EntailsAll Δ cs ↔ EntailsAll Δ ds) (ρ) :
    GroundModels ρ cs ↔ GroundModels ρ ds :=
  ⟨GroundModels.entailment_implication (fun Δ => (h Δ).mp),
   GroundModels.entailment_implication (fun Δ => (h Δ).mpr)⟩

end ModalityInference
