import ModalityInference.Proofs.SolverLocalSoundness
import ModalityInference.Proofs.ModeWorklist

/-! Executable modality steps preserve every ground solution. -/
namespace ModalityInference
namespace SolverGround

def Models (ρ : GroundAssignment) (s : SolverState) : Prop :=
  GroundModels ρ (s.pending ++ s.bounds)

theorem Models.emit {ρ s} (hs : Models ρ s) (r : RewriteRule) {cs}
    (hc : GroundModels ρ cs) : Models ρ (s.emit r cs) := by
  intro c hh
  rcases List.mem_append.mp hh with hh | hh
  · exact (List.mem_append.mp hh).elim (hc c) (fun h => hs c (List.mem_append_left _ h))
  · exact hs c (List.mem_append_right _ hh)

theorem Models.retain {ρ s} (hs : Models ρ s) (r : RewriteRule) {c}
    (hc : GroundSatisfies ρ c) : Models ρ (s.retain r c) := by
  unfold SolverState.retain
  split
  · exact hs
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hs d (List.mem_append_left _ hd)
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hs d (List.mem_append_right _ hd)

theorem mode_guards {ρ a b} (h : GroundSatisfies ρ (.mode a b)) :
    GroundModels ρ [.defined a, .defined b] := by
  obtain ⟨x, y, hx, hy, _⟩ := h
  simp [GroundModels, GroundSatisfies, ModExpr.WellFormed, hx, hy]

theorem stepMode_models {ρ s a b t} (hs : Models ρ s)
    (hc : GroundSatisfies ρ (.mode a b)) (he : stepMode s a b = .success t) : Models ρ t := by
  have hsingle : GroundModels ρ [.mode a b] := by simpa [GroundModels] using hc
  have hg := mode_guards hc
  simp only [stepMode, bind, pure, RunResult.bind] at he
  repeat' split at he
  all_goals cases he
  all_goals first
    | exact hs.emit _ (cs := []) (by simp [GroundModels])
    | exact hs.emit _ hg
    | exact hs.retain _ hc
    | exact (hs.retain _ hc).emit _ hg
    | exact hs.emit _ (ConstraintReduction.join.groundModels.mp hsingle)
    | exact hs.emit _ (ConstraintReduction.meet.groundModels.mp hsingle)
    | exact hs.emit _ (ConstraintReduction.sub.groundModels.mp hsingle)
    | exact hs.emit _ (ConstraintReduction.imp.groundModels.mp hsingle)
    | exact hs.emit _ (ConstraintReduction.left.groundModels.mp hsingle)
    | exact hs.emit _ (ConstraintReduction.right.groundModels.mp hsingle)
    | exact hs.emit _ (ConstraintReduction.close.groundModels.mp hsingle)
    | skip
  all_goals apply hs.emit
  all_goals intro c hmem
  all_goals rcases List.mem_append.mp hmem with hmem | hmem
  all_goals try exact hg c hmem
  all_goals obtain rfl := List.mem_singleton.mp hmem
  all_goals simp only [GroundSatisfies, ModExpr.below_leftResidual, ModExpr.below_rightResidual] at hc ⊢
  all_goals simpa only [ModExpr.Below, ModExpr.eval_compose_comm] using hc

theorem eval_closed {a : ModExpr} (ha : a.freeVariables.isEmpty = true)
    (η : ModVar → Option Mode) : a.eval (fun _ => none) = a.eval η := by
  apply a.eval_congr
  intro v hv
  have hm := (a.mem_freeVariables v).mpr hv
  have he : a.freeVariables = [] := List.isEmpty_iff.mp ha
  simp [he] at hm

theorem constant_mode_check {ρ a b} (hc : GroundSatisfies ρ (.mode a b))
    (ha : a.freeVariables.isEmpty = true) (hb : b.freeVariables.isEmpty = true) :
    checkModeConstraint (fun _ => none) (.mode a b) = true := by
  obtain ⟨x, y, hx, hy, hxy⟩ := hc
  simp [checkModeConstraint, eval_closed ha (some ∘ ρ.modes),
    eval_closed hb (some ∘ ρ.modes), hx, hy, hxy]

theorem stepMode_succeeds {ρ s a b} (hc : GroundSatisfies ρ (.mode a b)) :
    ∃ t, stepMode s a b = .success t := by
  simp only [stepMode, bind, pure, RunResult.bind]
  repeat' split
  all_goals try exact ⟨_, rfl⟩
  rename_i hclosed hfalse
  have hh : a.freeVariables.isEmpty = true ∧ b.freeVariables.isEmpty = true := by simpa using hclosed
  exact False.elim (hfalse (constant_mode_check hc hh.1 hh.2))

end SolverGround
end ModalityInference
