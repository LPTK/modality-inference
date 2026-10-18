import ModalityInference.Proofs.WorklistDeferred

namespace ModalityInference.WorklistCorrespondence

theorem stepType_append {s a b t} (h : stepType s a b = .success t) (cs : Bounds) :
    stepType {s with pending := s.pending ++ cs} a b =
      .success {t with pending := t.pending ++ cs} := by
  simp only [stepType, bind, pure, RunResult.bind, SolverState.skeleton_with_pending] at h ⊢
  repeat' split at h
  all_goals cases h
  all_goals try simp_all only
  all_goals simp [SolverState.emit, SolverState.retain,
    (s.skeleton_frame a.outer.1).1, (s.skeleton_frame b.outer.1).1]

theorem stepMode_append {s a b t} (h : stepMode s a b = .success t) (cs : Bounds) :
    stepMode {s with pending := s.pending ++ cs} a b =
      .success {t with pending := t.pending ++ cs} := by
  simp only [stepMode, bind, pure, RunResult.bind] at h ⊢
  repeat' split at h
  all_goals cases h
  all_goals try simp_all only
  all_goals simp [SolverState.emit, SolverState.retain, recordModeBound]

end ModalityInference.WorklistCorrespondence

namespace ModalityInference.WorklistCorrespondence

theorem retain (s : SolverState) (r : RewriteRule) (c : Constraint)
    (hc : Residual [c]) :
    RewriteStar ⟨c :: s.pending, s.bounds, s.substitution⟩
      ⟨c.typeGuards ++ s.pending, (s.retain r c).bounds, s.substitution⟩ := by
  by_cases hmem : c ∈ s.bounds
  · simpa only [SolverState.retain, List.contains_iff_mem.mpr hmem, ↓reduceIte] using
      single (Rewrites.hyp (s := ⟨s.pending, s.bounds, s.substitution⟩) hc hmem)
  · have hn : s.bounds.contains c = false := by simpa using hmem
    simpa only [SolverState.retain, hn, Bool.false_eq_true, ↓reduceIte] using
      single (Rewrites.record (s := ⟨s.pending, s.bounds, s.substitution⟩) hc hmem)

theorem expose (a b : Ty) (s : RewriteConfig) :
    RewriteStar {s with pending := .sub a b :: s.pending}
      {s with pending := (.sub (.modal a.outer.1 a.outer.2.normalize)
        (.modal b.outer.1 b.outer.2.normalize)) :: s.pending} := by
  apply equivalent (cs := [.sub a b])
    (ds := [.sub (.modal a.outer.1 a.outer.2.normalize) (.modal b.outer.1 b.outer.2.normalize)])
  intro Δ
  simp only [EntailsAll, List.mem_singleton, forall_eq]
  constructor
  · intro h
    exact ⟨(a.outer_normalize_subtype h.2.1).1.trans
      (h.1.trans (b.outer_normalize_subtype h.2.2).2),
      (a.outer_normalize_definedUnder Δ).mpr h.2.1,
      (b.outer_normalize_definedUnder Δ).mpr h.2.2⟩
  · intro h
    have ha := (a.outer_normalize_definedUnder Δ).mp h.2.1
    have hb := (b.outer_normalize_definedUnder Δ).mp h.2.2
    exact ⟨(a.outer_normalize_subtype ha).2.trans
      (h.1.trans (b.outer_normalize_subtype hb).1), ha, hb⟩

theorem reduce {cs ds : Bounds} (h : ConstraintReduction cs ds) (s : RewriteConfig) :
    RewriteStar {s with pending := cs ++ s.pending} {s with pending := ds ++ s.pending} :=
  single (.reduce h)

theorem stepType_rewrites {s a b t} (hf : SolverState.Fresh s)
    (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (h : stepType s a b = .success t) :
    RewriteStar ⟨.sub a b :: s.pending, s.bounds, s.substitution⟩
      ⟨t.pending, t.bounds, t.substitution⟩ := by
  refine trans (expose a b ⟨s.pending, s.bounds, s.substitution⟩) ?_
  have hla := ha.outer
  have hrb := hb.outer
  simp only [stepType, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals simp_all only
  all_goals first
    | exact reduce ConstraintReduction.unit ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.credit ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.pair ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.sum ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.fn ⟨s.pending, s.bounds, s.substitution⟩
    | skip
  case h_1.refl =>
    simpa only [SolverState.emit, SolverState.retain, Constraint.typeGuards,
      TypeExpr.wellFormedBounds, List.nil_append, List.cons_append] using
      retain s .variableBound
        (.sub (.modal (.var _) a.outer.2.normalize) (.modal (.var _) b.outer.2.normalize))
        (by simp [Residual, TypeExpr.outer])
  case h_2.isFalse.refl =>
    have hshape := s.skeleton_shape ‹∀ v, b.outer.1 = .var v → False› b.outer_not_modal
    have hbound : (Constraint.sub (.modal (.var _) a.outer.2.normalize)
        (.modal b.outer.1 b.outer.2.normalize)).Bounded s.nextType s.nextMode :=
      ⟨⟨by simpa only [‹a.outer.1 = _›] using hla.1, hla.2.normalize⟩,
       hrb.1, hrb.2.normalize⟩
    simpa only [SolverState.emit, SolverState.skeleton_substitution,
      (s.skeleton_frame b.outer.1).1, (s.skeleton_frame b.outer.1).2.1] using
      single (hf.skeleton_expandLeft hshape hbound)
  case h_3.isFalse.refl =>
    have hshape := s.skeleton_shape ‹∀ v, a.outer.1 = .var v → False› a.outer_not_modal
    have hbound : (Constraint.sub (.modal a.outer.1 a.outer.2.normalize)
        (.modal (.var _) b.outer.2.normalize)).Bounded s.nextType s.nextMode :=
      ⟨⟨hla.1, hla.2.normalize⟩,
       by simpa only [‹b.outer.1 = _›] using hrb.1, hrb.2.normalize⟩
    simpa only [SolverState.emit, SolverState.skeleton_substitution,
      (s.skeleton_frame a.outer.1).1, (s.skeleton_frame a.outer.1).2.1] using
      single (hf.skeleton_expandRight hshape hbound)

end ModalityInference.WorklistCorrespondence

namespace ModalityInference.WorklistCorrespondence

theorem retain_mode_guards (s : SolverState) (a b : ModExpr) :
    RewriteStar ⟨.mode a b :: s.pending, s.bounds, s.substitution⟩
      ⟨[.defined a, .defined b] ++ s.pending,
        (recordModeBound s a b).bounds, s.substitution⟩ := by
  have he : ∀ Δ, EntailsAll Δ [.mode a b] ↔
      EntailsAll Δ [.mode a b, .defined a, .defined b] := by
    intro Δ
    simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Entails]
    exact ⟨fun h => ⟨h, h.defined⟩, And.left⟩
  refine trans (equivalent he ⟨s.pending, s.bounds, s.substitution⟩) ?_
  simpa only [Constraint.typeGuards, List.nil_append, SolverState.retain, recordModeBound] using
    retain {s with pending := [.defined a, .defined b] ++ s.pending} .modeBound
      (.mode a b) (by simp [Residual])

theorem guarded_mode_equivalence (s : RewriteConfig) {a b c d : ModExpr}
    (he : ∀ η, ModExpr.Below η a b ↔ ModExpr.Below η c d) :
    RewriteStar {s with pending := .mode a b :: s.pending}
      {s with pending := [.defined a, .defined b, .mode c d] ++ s.pending} := by
  apply equivalent (cs := [.mode a b]) (ds := [.defined a, .defined b, .mode c d])
  intro Δ
  simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Entails]
  exact ⟨fun h => ⟨h.defined.1, h.defined.2, .valid fun η hη => (he η).mp (h.denote hη)⟩,
    fun h => .valid fun η hη => (he η).mpr (h.2.2.denote hη)⟩

theorem stepMode_rewrites {s a b t} (h : stepMode s a b = .success t) :
    RewriteStar ⟨.mode a b :: s.pending, s.bounds, s.substitution⟩
      ⟨t.pending, t.bounds, t.substitution⟩ := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals first
    | exact reduce ConstraintReduction.join ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.meet ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.sub ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.imp ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.left ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.right ⟨s.pending, s.bounds, s.substitution⟩
    | exact reduce ConstraintReduction.close ⟨s.pending, s.bounds, s.substitution⟩
    | exact retain_mode_guards s _ _
    | exact retain s .projection (.mode _ _) (by simp [Residual])
    | skip
  case isTrue.isTrue.refl =>
    apply equivalent (cs := [.mode a b]) (ds := []) (s := ⟨s.pending, s.bounds, s.substitution⟩)
    intro Δ
    simp only [EntailsAll, List.mem_singleton, forall_eq, List.not_mem_nil, IsEmpty.forall_iff]
    exact ⟨fun _ _ => trivial, fun _ => checkModeConstraint_empty_entails ‹_›⟩
  case isFalse.isTrue.refl =>
    cases beq_iff_eq.mp ‹(a == b) = true›
    apply equivalent (cs := [.mode a a]) (ds := [.defined a, .defined a]) (s := ⟨s.pending, s.bounds, s.substitution⟩)
    intro Δ
    simp only [EntailsAll, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, Entails]
    exact ⟨Submode.defined, fun h => .refl h.1⟩
  case h_5.isFalse.isTrue.refl | h_6.isFalse.isTrue.refl |
      h_7.isFalse.isTrue.refl | h_8.isFalse.isTrue.refl =>
    apply guarded_mode_equivalence ⟨s.pending, s.bounds, s.substitution⟩
    intro η
    simp only [ModExpr.below_leftResidual, ModExpr.below_rightResidual]
    all_goals simp only [ModExpr.Below, ModExpr.eval_compose_comm]

end ModalityInference.WorklistCorrespondence
