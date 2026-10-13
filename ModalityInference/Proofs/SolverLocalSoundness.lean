import ModalityInference.Proofs.ReductionEntailment

/-! Declarative justification of executable local solver transitions. -/
namespace ModalityInference

theorem TypeExpr.outer_realize (a : Ty) (ρ : GroundAssignment) :
    (.modal a.outer.1 a.outer.2 : Ty).realize ρ = a.realize ρ := by
  induction a <;> simp_all [TypeExpr.outer, TypeExpr.realize, ModExpr.epsilon,
    ModExpr.eval, bind, pure, Option.bind_assoc]
  case modal a m ih => simp only [← ih, Option.bind_assoc, Option.bind_some,
    GroundTy.modal_compose]

theorem TypeExpr.outer_definedUnder (a : Ty) (Δ : Bounds) :
    (.modal a.outer.1 a.outer.2 : Ty).DefinedUnder Δ ↔ a.DefinedUnder Δ := by
  constructor <;> intro h η hη
  all_goals
    simpa only [TypeExpr.wellFormedBounds_spec
      (GroundAssignment.mk (fun _ => .unit Mode.identity) η), TypeExpr.outer_realize] using h η hη

theorem TypeExpr.outer_subtype {Δ} (a : Ty) (ha : a.DefinedUnder Δ) :
    Subtype Δ (.modal a.outer.1 a.outer.2) a ∧
      Subtype Δ a (.modal a.outer.1 a.outer.2) := by
  induction a <;> try exact ⟨.identity, .identityRev⟩
  case modal a m ih =>
    obtain ⟨ha, hm⟩ := TypeExpr.definedUnder_modal.mp ha
    exact ⟨Subtype.composeRev.trans (.congr (ih ha).1 (.refl hm)),
      (Subtype.congr (ih ha).2 (.refl hm)).trans .compose⟩

theorem TypeExpr.outer_normalize_definedUnder (a : Ty) (Δ : Bounds) :
    (.modal a.outer.1 a.outer.2.normalize : Ty).DefinedUnder Δ ↔ a.DefinedUnder Δ := by
  simpa only [TypeExpr.definedUnder_modal, ModExpr.WellFormed, ModExpr.normalize_eval] using
    a.outer_definedUnder Δ

theorem TypeExpr.outer_normalize_subtype {Δ} (a : Ty) (ha : a.DefinedUnder Δ) :
    Subtype Δ (.modal a.outer.1 a.outer.2.normalize) a ∧
      Subtype Δ a (.modal a.outer.1 a.outer.2.normalize) := by
  have hm := a.outer.2.normalize_submode
    (TypeExpr.definedUnder_modal.mp ((a.outer_definedUnder Δ).mpr ha)).2
  exact ⟨(Subtype.congr .refl hm.1).trans (a.outer_subtype ha).1,
    (a.outer_subtype ha).2.trans (.congr .refl hm.2)⟩

theorem SolverState.entails_emitted {Δ r cs} {s : SolverState}
    (h : EntailsAll Δ ((s.emit r cs).pending ++ (s.emit r cs).bounds)) :
    EntailsAll Δ cs :=
  fun c hc => h c (by simp [SolverState.emit, hc])

theorem stepType_entails_exposed {s a b t Δ} (h : stepType s a b = .success t)
    (ht : EntailsAll Δ (t.pending ++ t.bounds)) :
    Entails Δ (.sub (.modal a.outer.1 a.outer.2.normalize)
      (.modal b.outer.1 b.outer.2.normalize)) := by
  simp only [stepType, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals simp_all only
  all_goals first
    | exact ConstraintReduction.pair.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.sum.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.fn.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.unit.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.credit.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | skip
  all_goals apply ht
  all_goals simp [SolverState.emit, SolverState.retain]
  split <;> simp_all

theorem stepType_entails {s a b t Δ} (h : stepType s a b = .success t)
    (ht : EntailsAll Δ (t.pending ++ t.bounds)) : Entails Δ (.sub a b) :=
  let he := stepType_entails_exposed h ht
  let ha := (a.outer_normalize_definedUnder Δ).mp he.2.1
  let hb := (b.outer_normalize_definedUnder Δ).mp he.2.2
  ⟨(a.outer_normalize_subtype ha).2.trans (he.1.trans (b.outer_normalize_subtype hb).1), ha, hb⟩

theorem checkModeConstraint_empty_entails {a b Δ}
    (h : checkModeConstraint (fun _ => none) (.mode a b) = true) : Entails Δ (.mode a b) := by
  cases ha : a.eval (fun _ => none) <;> cases hb : b.eval (fun _ => none) <;>
    simp [checkModeConstraint, ha, hb] at h
  exact .valid fun _ _ => ⟨_, _, a.eval_refinement (by simp) ha,
    b.eval_refinement (by simp) hb, h⟩

theorem stepMode_entails {s a b t Δ} (h : stepMode s a b = .success t)
    (ht : EntailsAll Δ (t.pending ++ t.bounds)) : Entails Δ (.mode a b) := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals first
    | exact ConstraintReduction.join.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.meet.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.sub.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.imp.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.left.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.right.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | exact ConstraintReduction.close.entails_backward (SolverState.entails_emitted ht) _ (List.mem_singleton_self _)
    | skip
  case h_5.isFalse.isTrue.refl | h_6.isFalse.isTrue.refl |
      h_7.isFalse.isTrue.refl | h_8.isFalse.isTrue.refl =>
    apply Submode.valid
    intro η hη
    have hh := ((SolverState.entails_emitted ht) _
      (List.mem_append_right _ (List.mem_singleton_self _))).denote hη
    simp only [ModExpr.below_leftResidual, ModExpr.below_rightResidual] at hh ⊢
    simpa only [ModExpr.Below, ModExpr.eval_compose_comm] using hh
  case isTrue.isTrue.refl => exact checkModeConstraint_empty_entails ‹_›
  case isFalse.isTrue.refl =>
    cases beq_iff_eq.mp ‹(a == b) = true›
    exact .refl ((SolverState.entails_emitted ht) _ (List.mem_cons_self))
  all_goals apply ht
  all_goals simp only [recordModeBound, SolverState.emit, SolverState.retain, List.mem_append]
  all_goals right
  all_goals split <;> simp_all only [List.contains_iff_mem, List.mem_cons, true_or]

end ModalityInference
