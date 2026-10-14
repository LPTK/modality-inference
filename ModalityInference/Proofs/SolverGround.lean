import ModalityInference.Proofs.GroundFresh
import ModalityInference.Proofs.SolverTermination
import ModalityInference.Proofs.SolverCounters

/-! Preservation of original ground solutions by the executable worklist. -/
namespace ModalityInference

def SolverState.config (s : SolverState) : RewriteConfig :=
  ⟨s.pending, s.bounds, s.substitution⟩

def Scope.Bounded (scope : Scope) (nt nm : Nat) : Prop :=
  (∀ v ∈ scope.types, v.index < nt) ∧ (∀ v ∈ scope.modes, v.index < nm)

namespace SolverGround

theorem AgreesBelow.realize {η ρ nt nm} (h : AgreesBelow η ρ nt nm) {a : Ty}
    (ha : a.Bounded nt nm) : a.realize η = a.realize ρ :=
  a.realize_congr (fun v hv => h.1 v (((a.bounded_iff nt nm).mp ha).1 v hv))
    (fun v hv => h.2 v (((a.bounded_iff nt nm).mp ha).2 v hv))

theorem AgreesBelow.eval {η ρ nt nm} (h : AgreesBelow η ρ nt nm) {a : ModExpr}
    (ha : a.Bounded nm) : a.eval (some ∘ η.modes) = a.eval (some ∘ ρ.modes) :=
  a.eval_congr (fun v hv => congrArg some (h.2 v ((a.bounded_iff nm).mp ha v hv)))

theorem stepType_configModels {scope ρ s a b t} (hs : SolverState.Fresh s)
    (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (hscope : scope.Bounded s.nextType s.nextMode) (he : stepType s a b = .success t)
    (hm : Deferred.ConfigModels scope {s.config with pending := .sub a b :: s.pending} ρ) :
    Deferred.ConfigModels scope t.config ρ := by
  obtain ⟨η, hη, ht, hmode⟩ := hm
  have hc : GroundSatisfies η (.sub a b) := hη _ (by simp [RewriteConfig.constraints])
  have hbase : Models η s := fun c hh => hη c (List.mem_cons_of_mem _ hh)
  obtain ⟨ζ, hζ, hagree⟩ := stepType_models hs ha hb hbase hc he
  refine ⟨ζ, hζ, ?_, ?_⟩
  · intro v hv
    have hh := hagree.realize (hs.substitution.type v (hscope.1 v hv))
    simpa only [SolverState.config, stepType_substitution he, hh] using ht v hv
  · intro v hv
    have hh := hagree.eval (hs.substitution.mode v (hscope.2 v hv))
    simpa only [SolverState.config, stepType_substitution he, hh] using hmode v hv

theorem stepMode_configModels {scope ρ s a b t} (he : stepMode s a b = .success t)
    (hm : Deferred.ConfigModels scope {s.config with pending := .mode a b :: s.pending} ρ) :
    Deferred.ConfigModels scope t.config ρ := by
  obtain ⟨η, hη, ht, hmode⟩ := hm
  have hc : GroundSatisfies η (.mode a b) := hη _ (by simp [RewriteConfig.constraints])
  have hbase : Models η s := fun c hh => hη c (List.mem_cons_of_mem _ hh)
  refine ⟨η, stepMode_models hbase hc he, ?_, ?_⟩
  · simpa only [SolverState.config, stepMode_substitution he] using ht
  · simpa only [SolverState.config, stepMode_substitution he] using hmode

theorem solverStep_complete {scope ρ s} (hs : SolverState.Fresh s) (hu : s.Unbound)
    (hσ : s.substitution.Acyclic) (hf : s.Flexible)
    (hscope : scope.Bounded s.nextType s.nextMode) (hm : Deferred.ConfigModels scope s.config ρ) :
    ∃ t, solverStep s = .success t ∧ Deferred.ConfigModels scope t.config ρ := by
  obtain ⟨η, hη, ht, hmode⟩ := hm
  have hnorm : ∀ c rest, s.pending = c :: rest →
      GroundSatisfies η (s.substitution.constraint c).normalize := by
    intro c rest he
    rw [(hu.pending c (by simp [he])).fixed hu.modes]
    exact (c.normalize_ground η).mpr (hη c (by simp [SolverState.config, RewriteConfig.constraints, he]))
  have htail : ∀ c rest seen, s.pending = c :: rest → Models η {s with pending := rest, seen := seen} := by
    intro c rest seen he d hd
    apply hη d
    change d ∈ s.pending ++ s.bounds
    rw [he]
    exact List.mem_cons_of_mem _ hd
  have hcons : ∀ c rest seen, s.pending = c :: rest → Deferred.ConfigModels scope
      ({s with pending := (s.substitution.constraint c).normalize :: rest, seen := seen}).config ρ := by
    intro c rest seen he
    refine ⟨η, ?_, ht, hmode⟩
    intro d hd
    exact (List.mem_cons.mp hd).elim (fun hh => hh ▸ hnorm c rest he) (htail c rest seen he d)
  simp only [solverStep, bind, pure, RunResult.bind]
  repeat' split
  case h_2 =>
    rename_i pending c rest hpend hseen normalized a b he
    have hground : GroundSatisfies η (.sub a b) := he ▸ hnorm c rest hpend
    have hshape := SolverShape.models_of_ground
      (show GroundModels η [.sub a b] by simpa [GroundModels] using hground)
      (.sub a b) (List.mem_singleton_self _)
    have hflex : (Constraint.sub a b).Flexible := he ▸ hf.normalized_head hpend
    obtain ⟨t, hstep⟩ := SolverShape.stepType_succeeds
      (s := {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen})
      hflex.1 hflex.2 hshape
    refine ⟨t, hstep, stepType_configModels (hs.advance hpend (by simp))
      (he ▸ hs.normalized_head hpend).1 (he ▸ hs.normalized_head hpend).2 hscope hstep ?_⟩
    simpa only [SolverState.config, he] using hcons c rest [] hpend
  case h_3 =>
    rename_i pending c rest hpend hseen normalized a b he
    have hground : GroundSatisfies η (.mode a b) := he ▸ hnorm c rest hpend
    obtain ⟨t, hstep⟩ := stepMode_succeeds
      (s := {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen}) hground
    refine ⟨t, hstep, stepMode_configModels hstep ?_⟩
    simpa only [SolverState.config, he] using hcons c rest [] hpend
  case h_2.isFalse.isFalse =>
    rename_i pending c rest hpend hseen normalized a v n he hrefl hocc
    refine ⟨_, rfl, ?_⟩
    apply (Deferred.ConfigModels.substitute (s := ⟨rest, s.bounds, s.substitution⟩) (by simpa using hocc)
      (s.substitution.normalized_equal_fresh hσ he).1).mp
    simpa only [SolverState.config, he] using hcons c rest [] hpend
  case h_4.isTrue.isFalse =>
    rename_i pending c rest hpend hseen normalized a he hclosed hundefined
    have hc : a.WellFormed η.modes := by simpa only [he, GroundSatisfies] using hnorm c rest hpend
    exact False.elim (hundefined (by simpa only [eval_closed hclosed (some ∘ η.modes)] using hc))
  case h_1.isFalse =>
    have hc := hf.normalized_head ‹s.pending = _ :: _›
    simp [‹(s.substitution.constraint _).normalize = .equal _ _›, Constraint.Flexible] at hc
  all_goals refine ⟨_, rfl, η, ?_, ht, hmode⟩
  all_goals first
    | exact hη
    | exact htail _ _ [] ‹s.pending = _ :: _›
    | exact (htail _ _ [] ‹s.pending = _ :: _›).emit _ (cs := []) (by simp [GroundModels])
    | exact (htail _ _ [] ‹s.pending = _ :: _›).retain _ (hnorm _ _ ‹s.pending = _ :: _›)
    | skip
  case h_1 =>
    rename_i pending c rest hpend hseen normalized a b he
    have hg : GroundSatisfies η (.equiv a b) := he ▸ hnorm c rest hpend
    obtain ⟨x, y, hx, hy, hxy, hyx⟩ := hg
    apply (htail c rest [] hpend).emit .substitute
    simp [GroundModels, GroundSatisfies, hx, hy, hxy, hyx]
  case h_4.isFalse =>
    rename_i pending c rest hpend hseen normalized a he hclosed
    exact (htail c rest [] hpend).retain .defined (hnorm c rest hpend)
  case h_2.isFalse.isTrue =>
    rename_i pending c rest hpend hseen normalized a v n he hrefl hocc
    have hg : GroundSatisfies η (.equal (.flex n) a) := he ▸ hnorm c rest hpend
    obtain ⟨y, hy, hvy, hyv⟩ := hg
    apply (htail c rest [] hpend).emit .substitute
    simp [GroundModels, GroundSatisfies, TypeExpr.realize, hy, hvy, hyv]

theorem runWorklist_complete {scope ρ s} (fuel : Nat) (hs : SolverState.Fresh s)
    (hu : s.Unbound) (hσ : s.substitution.Acyclic) (hf : s.Flexible)
    (hscope : scope.Bounded s.nextType s.nextMode) (hm : Deferred.ConfigModels scope s.config ρ) :
    runWorklist fuel s = .exhausted ∨
      ∃ t, runWorklist fuel s = .success t ∧ Deferred.ConfigModels scope t.config ρ := by
  induction fuel generalizing s with
  | zero => exact Or.inl rfl
  | succ fuel ih =>
    simp only [runWorklist]
    split
    · exact Or.inr ⟨s, rfl, hm⟩
    · obtain ⟨t, he, ht⟩ := solverStep_complete hs hu hσ hf hscope hm
      simp only [he, bind, RunResult.bind]
      apply ih (solverStep_fresh hs he) (solverStep_unbound hu hs hσ he)
        (solverStep_acyclic hσ he) (solverStep_flexible hf he) _ ht
      have hc := solverStep_counters he
      exact ⟨fun v hv => (hscope.1 v hv).trans_le hc.1,
        fun v hv => (hscope.2 v hv).trans_le hc.2⟩

theorem runSolver_complete {scope ρ s} (fuel : Nat) (hs : SolverState.Fresh s)
    (hu : s.Unbound) (hσ : s.substitution.Acyclic) (hf : s.Flexible)
    (hscope : scope.Bounded s.nextType s.nextMode) (hm : Deferred.ConfigModels scope s.config ρ) :
    runSolver fuel s = .exhausted ∨
      ∃ t, runSolver fuel s = .success t ∧ Deferred.ConfigModels scope t.config ρ := by
  have hfix : s.substitution.bounds (s.pending ++ s.bounds) = s.pending ++ s.bounds :=
    Substitution.bounds_fixed hu.modes (fun c hc =>
      (List.mem_append.mp hc).elim (hu.pending c) (hu.bounds c))
  obtain ⟨η, hη⟩ := hm.imp (fun _ h => h.1)
  have hcheck := hη.checkShapes fuel
  simp only [runSolver, s.substitution.checkAcyclic_iff.mpr hσ, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, hfix, bind, RunResult.bind]
  rcases hcheck with he | he
  · simp [SolverState.config, RewriteConfig.constraints] at he
    simp [he]
  · simp [SolverState.config, RewriteConfig.constraints] at he
    simpa only [he, RunResult.bind] using runWorklist_complete fuel hs hu hσ hf hscope hm

theorem runSolver_eventual_complete {scope ρ s} (hs : SolverState.Fresh s)
    (hu : s.Unbound) (hσ : s.substitution.Acyclic) (hf : s.Flexible)
    (hscope : scope.Bounded s.nextType s.nextMode) (hm : Deferred.ConfigModels scope s.config ρ) :
    ∃ n t, Deferred.ConfigModels scope t.config ρ ∧
      ∀ fuel ≥ n, runSolver fuel s = .success t := by
  obtain ⟨n, result, hn, hr⟩ := runSolver_eventually hs hu
  rcases runSolver_complete n hs hu hσ hf hscope hm with he | ⟨t, he, ht⟩
  · exact False.elim (hn ((hr n le_rfl).symm.trans he))
  · exact ⟨n, t, ht, fun fuel hf => (hr fuel hf).trans ((hr n le_rfl).symm.trans he)⟩

end SolverGround
end ModalityInference
