import ModalityInference.Proofs.SymbolicAssignments
import ModalityInference.Proofs.SymbolicCongruence
import ModalityInference.Proofs.SolverGround

namespace ModalityInference.SymbolicSolver

def Models (Δ : Bounds) (σ : Substitution) (s : SolverState) : Prop :=
  ∀ c ∈ s.pending ++ s.bounds, Entails Δ (σ.constraint c)

theorem Models.emit {Δ σ s} (hs : Models Δ σ s) (r : RewriteRule) {cs}
    (hc : EntailsAll Δ (σ.bounds cs)) : Models Δ σ (s.emit r cs) := by
  intro c hh
  rcases List.mem_append.mp hh with hh | hh
  · rcases List.mem_append.mp hh with hh | hh
    · exact hc _ (List.mem_map.mpr ⟨c, hh, rfl⟩)
    · exact hs c (List.mem_append_left _ hh)
  · exact hs c (List.mem_append_right _ hh)

theorem Models.retain {Δ σ s} (hs : Models Δ σ s) (r : RewriteRule) {c}
    (hc : Entails Δ (σ.constraint c)) : Models Δ σ (s.retain r c) := by
  unfold SolverState.retain
  split
  · exact hs
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hs d (List.mem_append_left _ hd)
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact hc
      · exact hs d (List.mem_append_right _ hd)

theorem Models.of_solution {Δ σ s} (hs : Solution (s.pending ++ s.bounds) Δ σ) :
    Models Δ σ s := fun c hc => hs _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

theorem Models.solution {Δ σ s} (hs : Models Δ σ s) :
    Solution (s.pending ++ s.bounds) Δ σ := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact hs d hd

theorem mode_guards {Δ : Bounds} {σ : Substitution} {a b}
    (h : Entails Δ (σ.constraint (.mode a b))) :
    EntailsAll Δ (σ.bounds [.defined a, .defined b]) := by
  simpa only [Substitution.bounds, List.map_cons, List.map_nil, EntailsAll,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Substitution.constraint, Constraint.subst] using h.defined

theorem stepMode_models {Δ σ s a b t} (hΔ : Residual Δ) (hs : Models Δ σ s)
    (hc : Entails Δ (σ.constraint (.mode a b))) (he : stepMode s a b = .success t) :
    Models Δ σ t := by
  have hsingle : EntailsAll Δ (σ.bounds [.mode a b]) := by
    simpa [Substitution.bounds, EntailsAll] using hc
  have hg := mode_guards hc
  simp only [stepMode, bind, pure, RunResult.bind] at he
  repeat' split at he
  all_goals cases he
  all_goals first
    | exact hs.emit _ (cs := []) (by simp [Substitution.bounds, EntailsAll])
    | exact hs.emit _ hg
    | exact hs.retain _ hc
    | exact (hs.retain _ hc).emit _ hg
    | exact hs.emit _ ((ConstraintReduction.join.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hs.emit _ ((ConstraintReduction.meet.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hs.emit _ ((ConstraintReduction.sub.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hs.emit _ ((ConstraintReduction.imp.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hs.emit _ ((ConstraintReduction.left.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hs.emit _ ((ConstraintReduction.right.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hs.emit _ ((ConstraintReduction.close.substitute σ).entails_forward_residual hΔ hsingle)
    | skip
  all_goals apply hs.emit
  all_goals intro c hmem
  all_goals obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmem
  all_goals rcases List.mem_append.mp hd with hd | hd
  all_goals try exact hg _ (List.mem_map.mpr ⟨d, hd, rfl⟩)
  all_goals obtain rfl := List.mem_singleton.mp hd
  all_goals apply Submode.valid
  all_goals intro η hη
  all_goals have hh := hc.denote hη
  all_goals simp only [ModExpr.subst,
    ModExpr.below_leftResidual, ModExpr.below_rightResidual] at hh ⊢
  all_goals simpa only [ModExpr.Below, ModExpr.eval_compose_comm] using hh

theorem sub_outer_normalize (a b : Ty) (Δ : Bounds) :
    Entails Δ (.sub a b) ↔
      Entails Δ (.sub (.modal a.outer.1 a.outer.2.normalize)
        (.modal b.outer.1 b.outer.2.normalize)) := by
  constructor
  · rintro ⟨h, ha, hb⟩
    exact ⟨(a.outer_normalize_subtype ha).1.trans (h.trans (b.outer_normalize_subtype hb).2),
      (a.outer_normalize_definedUnder Δ).mpr ha, (b.outer_normalize_definedUnder Δ).mpr hb⟩
  · rintro ⟨h, ha, hb⟩
    have ha' := (a.outer_normalize_definedUnder Δ).mp ha
    have hb' := (b.outer_normalize_definedUnder Δ).mp hb
    exact ⟨(a.outer_normalize_subtype ha').2.trans (h.trans (b.outer_normalize_subtype hb').1), ha', hb'⟩

theorem tag_subst_structural (σ : Substitution) {a : Ty}
    (ha : ∀v, a ≠ .var v) (hm : ∀t m, a ≠ .modal t m) :
    SymbolicInversion.tag (σ.ty a) = SymbolicInversion.tag a := by
  cases a <;> first | rfl | exact False.elim (ha _ rfl) | exact False.elim (hm _ _ rfl)

theorem expansion_models {Δ σ s a v old} (hs : s.Fresh)
    (hw : σ.WellFormedUnder Δ) (ha : ∀ w, a ≠ .var w) (ham : ∀ t m, a ≠ .modal t m)
    (hh : SymbolicInversion.tag (σ.type v) = SymbolicInversion.tag a)
    (hv : v.index < s.nextType) (hm : Models Δ σ s)
    (ho : Entails Δ (σ.constraint old)) (hb : old.Bounded s.nextType s.nextMode) :
    ∃ τ, τ.WellFormedUnder Δ ∧
      Models Δ τ ((s.skeleton a).2.emit .expand [.equal v (s.skeleton a).1, old]) ∧
      AgreesBelow τ σ s.nextType s.nextMode := by
  obtain ⟨τ, hτ, ht, hagree⟩ := skeleton_assign hw (hw.types v) ha ham hh
  refine ⟨τ, hτ, ?_, hagree⟩
  apply Models.emit
  · have hh' := hagree.solution (Bounds.bounded_append.mpr ⟨hs.pending, hs.bounds⟩) hm.solution
    simpa only [Models, (s.skeleton_frame a).1, (s.skeleton_frame a).2.1]
      using Models.of_solution hh'
  · simp only [Substitution.bounds, List.map_cons, List.map_nil, EntailsAll,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, (hagree.constraint hb).mpr ho⟩
    rw [τ.constraint_subst_entails]
    change Subtype Δ (τ.type v) (τ.ty (s.skeleton a).1) ∧
      Subtype Δ (τ.ty (s.skeleton a).1) (τ.type v) ∧
      (τ.type v).DefinedUnder Δ ∧ (τ.ty (s.skeleton a).1).DefinedUnder Δ
    rw [ht, hagree.1 v hv]
    exact ⟨((σ.type v).outer_subtype (hw.types v)).2,
      ((σ.type v).outer_subtype (hw.types v)).1, hw.types v,
      ((σ.type v).outer_definedUnder Δ).mpr (hw.types v)⟩

theorem stepType_models {Δ σ s a b t} (hΔ : Residual Δ) (hs : s.Fresh)
    (hw : σ.WellFormedUnder Δ)
    (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (hm : Models Δ σ s) (hc : Entails Δ (σ.constraint (.sub a b)))
    (he : stepType s a b = .success t) :
    ∃ τ, τ.WellFormedUnder Δ ∧ Models Δ τ t ∧ AgreesBelow τ σ s.nextType s.nextMode := by
  have ho : Entails Δ (σ.constraint (.sub (.modal a.outer.1 a.outer.2.normalize)
      (.modal b.outer.1 b.outer.2.normalize))) :=
    Entails.consequence_substitute (cs := [.sub a b])
      (fun Γ hΓ => (sub_outer_normalize a b Γ).mp (hΓ _ (by simp))) hw
      (by simpa [Substitution.bounds, EntailsAll] using hc)
  have hg : EntailsAll Δ (σ.bounds [.defined a.outer.2.normalize, .defined b.outer.2.normalize]) := by
    have hh := And.intro (TypeExpr.definedUnder_modal.mp ho.2.1).2
      (TypeExpr.definedUnder_modal.mp ho.2.2).2
    simpa only [Substitution.bounds, List.map_cons, List.map_nil, EntailsAll,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Substitution.constraint, Constraint.subst] using hh
  have hsingle : EntailsAll Δ (σ.bounds
      [.sub (.modal a.outer.1 a.outer.2.normalize) (.modal b.outer.1 b.outer.2.normalize)]) := by
    simpa only [Substitution.bounds, List.map_cons, List.map_nil, EntailsAll,
      List.mem_singleton, forall_eq] using ho
  have hbound : (Constraint.sub (.modal a.outer.1 a.outer.2.normalize)
      (.modal b.outer.1 b.outer.2.normalize)).Bounded s.nextType s.nextMode :=
    ⟨⟨ha.outer.1, ha.outer.2.normalize⟩, ⟨hb.outer.1, hb.outer.2.normalize⟩⟩
  simp only [stepType, bind, pure, RunResult.bind] at he
  repeat' split at he
  all_goals cases he
  case h_2.isFalse.refl =>
    rename_i x y n hv hnv hocc
    apply expansion_models hs hw hnv b.outer_not_modal _
      (by simpa only [hv, TypeExpr.Bounded] using ha.outer.1) hm ho hbound
    have hh := SymbolicInversion.subtype_tag hΔ ho.1
    change SymbolicInversion.tag (σ.ty a.outer.1) = SymbolicInversion.tag (σ.ty b.outer.1) at hh
    rw [hv] at hh
    exact hh.trans (tag_subst_structural σ hnv b.outer_not_modal)
  case h_3.isFalse.refl =>
    rename_i x y n hv hnv hnf hocc
    apply expansion_models hs hw hnv a.outer_not_modal _
      (by simpa only [hv, TypeExpr.Bounded] using hb.outer.1) hm ho hbound
    have hh := SymbolicInversion.subtype_tag hΔ ho.1
    change SymbolicInversion.tag (σ.ty a.outer.1) = SymbolicInversion.tag (σ.ty b.outer.1) at hh
    rw [hv] at hh
    exact hh.symm.trans (tag_subst_structural σ hnv a.outer_not_modal)
  all_goals refine ⟨σ, hw, ?_, AgreesBelow.refl _ _ _⟩
  all_goals simp_all only
  all_goals first
    | exact (hm.retain _ ho).emit _ hg
    | exact hm.emit _ ((ConstraintReduction.pair.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hm.emit _ ((ConstraintReduction.sum.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hm.emit _ ((ConstraintReduction.fn.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hm.emit _ ((ConstraintReduction.unit.substitute σ).entails_forward_residual hΔ hsingle)
    | exact hm.emit _ ((ConstraintReduction.credit.substitute σ).entails_forward_residual hΔ hsingle)

end ModalityInference.SymbolicSolver
