import ModalityInference.Proofs.SchemeModeSynthesis
import ModalityInference.Proofs.ComparisonControls
import ModalityInference.Proofs.SkolemSubstitution

/-! A symbolic modality witness induces one uniform coordinate strategy. Its
projections extend partial expressions outside the declared assumptions without
changing their values where they are defined. -/
namespace ModalityInference.SchemeModeSynthesis

def coordinate (m : ModExpr) (axis : Nat) : BoolExpr :=
  match axis with
  | 0 => m.project.locality
  | 1 => m.project.affinity
  | _ => m.project.uniqueness

def strategy (images : ModVar → ModExpr) (ρ : Nat → Bool) (i : Nat) : Bool :=
  (coordinate (images (SymbolicModes.atomVariable i)) (i % 3)).eval ρ

theorem strategy_coordinate (images : ModVar → ModExpr) (ρ : Nat → Bool)
    (v : ModVar) (axis : Nat) (ha : axis < 3) :
    strategy images ρ (v.atomIndex axis) = (coordinate (images v) axis).eval ρ := by
  simp only [strategy, ComparisonControls.atomVariable_atomIndex v axis ha,
    ComparisonControls.atomIndex_mod v axis ha]

theorem coordinate_support (m : ModExpr) {axis i : Nat} (ha : axis < 3)
    (hi : i ∈ (coordinate m axis).atoms) :
    ModalSynthesis.locality i = (axis == 0) := by
  obtain rfl | rfl | rfl : axis = 0 ∨ axis = 1 ∨ axis = 2 := by omega
  · simpa only [ModalSynthesis.locality, beq_self_eq_true, beq_iff_eq] using
      (ComparisonControls.project_support m).1 i hi |>.1
  · simpa only [ModalSynthesis.locality, show (1 == 0) = false from rfl,
      beq_eq_false_iff_ne] using (ComparisonControls.project_support m).2.1 i hi |>.1
  · simpa only [ModalSynthesis.locality, show (2 == 0) = false from rfl,
      beq_eq_false_iff_ne] using (ComparisonControls.project_support m).2.2 i hi |>.1

theorem strategy_uniform {modeIds : List Nat} {images : ModVar → ModExpr}
    (hfixed : ∀ v, (∀ n ∈ modeIds, v ≠ .flex n) → images v = .var v) :
    ModalSynthesis.Uniform ModalSynthesis.locality (atoms modeIds) (strategy images) := by
  constructor
  · intro ρ i hi
    have hf : images (SymbolicModes.atomVariable i) = .var (SymbolicModes.atomVariable i) := by
      apply hfixed
      intro n hn he
      apply hi
      rw [← SymbolicSchemeModes.atomVariable_reencode i, he]
      exact (mem_atoms_flex (Nat.mod_lt _ (by decide))).mpr hn
    unfold strategy
    rw [hf]
    have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    all_goals simpa [coordinate, hr, ModExpr.project, BoolExpr.eval] using
      congrArg ρ (SymbolicSchemeModes.atomVariable_reencode i)
  · intro ρ τ i h
    apply SymbolicModes.eval_congr
    intro w hw
    apply h w
    exact coordinate_support _ (Nat.mod_lt _ (by decide)) hw

theorem strategy_eval (images : ModVar → ModExpr) (ρ : Nat → Bool) (v : ModVar)
    (h : (images v).WellFormed (projectedModes ρ)) :
    (images v).eval (some ∘ projectedModes ρ) =
      some (projectedModes (strategy images ρ) v) := by
  rw [← ModExpr.project_correct, Projection.eval, (ModExpr.project_defined _ _).mpr h]
  simp [projectedModes, strategy_coordinate, coordinate]

theorem strategy_fixed {modeIds : List Nat} {images : ModVar → ModExpr}
    (hfixed : ∀ v, (∀ n ∈ modeIds, v ≠ .flex n) → images v = .var v)
    (ρ : Nat → Bool) {v : ModVar} (hv : ∀ n ∈ modeIds, v ≠ .flex n) :
    projectedModes (strategy images ρ) v = projectedModes ρ v := by
  simp only [projectedModes, strategy_coordinate images ρ v 0 (by decide),
    strategy_coordinate images ρ v 1 (by decide), strategy_coordinate images ρ v 2 (by decide),
    hfixed v hv, coordinate, ModExpr.project, BoolExpr.eval]

/-- A shared symbolic witness, defined under the declared assumptions, suffices
for eventual successful synthesis. No global definedness assumption is needed. -/
theorem run_complete_witness {modeIds : List Nat} {Δ goals : Bounds}
    {images : ModVar → ModExpr}
    (hfixed : ∀ v, (∀ n ∈ modeIds, v ≠ .flex n) → images v = .var v)
    (hscope : ∀ v ∈ Δ.modVars, ∀ n ∈ modeIds, v ≠ .flex n)
    (hwitness : ∀ η, ModeModels Δ η → ∃ θ,
      (∀ v, (images v).eval (some ∘ η) = some (θ v)) ∧ ModeModels goals θ) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel modeIds
      (.imp (boundsModeFormula Δ) (boundsModeFormula goals)) = .success result := by
  apply run_complete (strategy_uniform hfixed)
  intro ρ
  rw [BoolExpr.eval_imp_true]
  intro hΔ
  have hmodels : ModeModels Δ (projectedModes ρ) :=
    (ModeModels.congr Δ (fun v hv => strategy_fixed hfixed ρ (hscope v hv))).mp
      ((boundsModeFormula_correct Δ _).mp hΔ)
  obtain ⟨θ, he, hg⟩ := hwitness (projectedModes ρ) hmodels
  have heq : projectedModes (strategy images ρ) = θ := by
    funext v
    have hd : (images v).WellFormed (projectedModes ρ) := by
      simp only [ModExpr.WellFormed, he v, Option.isSome_some]
    exact Option.some.inj ((strategy_eval images ρ v hd).symm.trans (he v))
  exact (boundsModeFormula_correct goals _).mpr (heq.symm ▸ hg)

/-- The witness contract may be given directly as validity of substituted
scalar obligations, retaining every original definedness guard. -/
theorem run_complete_substituted {modeIds : List Nat} {Δ goals : Bounds}
    {images : ModVar → ModExpr}
    (hfixed : ∀ v, (∀ n ∈ modeIds, v ≠ .flex n) → images v = .var v)
    (hscope : ∀ v ∈ Δ.modVars, ∀ n ∈ modeIds, v ≠ .flex n)
    (htotal : ∀ η, ModeModels Δ η → ∀ v, (images v).WellFormed η)
    (hgoals : ∀ η, ModeModels Δ η →
      ModeModels (goals.map (Constraint.subst TypeExpr.var images)) η) :
    ∃ n, ∀ fuel ≥ n, ∃ result, run fuel modeIds
      (.imp (boundsModeFormula Δ) (boundsModeFormula goals)) = .success result := by
  apply run_complete_witness hfixed hscope
  intro η hη
  let θ : ModVar → Mode := fun v => ((images v).eval (some ∘ η)).getD Mode.identity
  have he : ∀ v, (images v).eval (some ∘ η) = some (θ v) := by
    intro v
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (htotal η hη v)
    simp [θ, hm]
  refine ⟨θ, he, ?_⟩
  intro c hc
  exact (ModeSatisfies.subst_functions c TypeExpr.var images he).mp
    (hgoals η hη _ (List.mem_map.mpr ⟨c, hc, rfl⟩))

theorem run_fixed {fuel modeIds formula result}
    (h : run fuel modeIds formula = .success result)
    {v : ModVar} (hv : ∀ n ∈ modeIds, v ≠ .flex n) :
    result.substitution.mode v = .var v := by
  obtain ⟨images, _, ha, _, _⟩ := run_spec h
  cases v with
  | rigid n => rfl
  | flex n =>
    exact SymbolicSchemeModes.assemble_fixed ha
      (parameters_lookup_none (fun hn => hv n hn rfl))

/-- A successful run satisfies the original scalar obligations under its
actual returned substitution, with declared parameters fixed. -/
theorem run_substituted_models {fuel : Nat} {modeIds : List Nat} {Δ goals : Bounds}
    {result : Result}
    (h : run fuel modeIds (.imp (boundsModeFormula Δ) (boundsModeFormula goals)) =
      .success result)
    (hscope : ∀ v ∈ Δ.modVars, ∀ n ∈ modeIds, v ≠ .flex n)
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    ModeModels (goals.map (Constraint.subst TypeExpr.var result.substitution.mode)) η := by
  obtain ⟨θ, he, hvalid⟩ := run_actual h η
  have hθ : ModeModels Δ θ := by
    apply (ModeModels.congr Δ ?_).mp hη
    intro v hv
    have hh := he v
    rw [run_fixed h (hscope v hv)] at hh
    exact Option.some.inj hh
  have hg : ModeModels goals θ := by
    rw [BoolExpr.eval_imp_true, boundsModeFormula_correct,
      boundsModeFormula_correct, projectedModes_encodeModes] at hvalid
    exact hvalid hθ
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact (ModeSatisfies.subst_functions d TypeExpr.var result.substitution.mode he).mpr (hg d hd)

end ModalityInference.SchemeModeSynthesis
