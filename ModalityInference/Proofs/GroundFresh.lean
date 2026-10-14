import ModalityInference.Proofs.TypeGround
import ModalityInference.Proofs.ShapeExpansion

/-! Fresh ground witnesses preserve all previously allocated identifiers. -/
namespace ModalityInference

theorem TypeExpr.outer_normalize_realize (a : Ty) (ρ : GroundAssignment) :
    (.modal a.outer.1 a.outer.2.normalize : Ty).realize ρ = a.realize ρ := by
  simpa only [TypeExpr.realize, ModExpr.normalize_eval] using a.outer_realize ρ

namespace SolverGround

def AgreesBelow (η ρ : GroundAssignment) (nt nm : Nat) : Prop :=
  (∀ v, v.index < nt → η.types v = ρ.types v) ∧
    (∀ v, v.index < nm → η.modes v = ρ.modes v)

theorem AgreesBelow.refl (ρ : GroundAssignment) (nt nm : Nat) : AgreesBelow ρ ρ nt nm :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem AgreesBelow.satisfies {η ρ nt nm} (h : AgreesBelow η ρ nt nm) {c : Constraint}
    (hc : c.Bounded nt nm) : GroundSatisfies η c ↔ GroundSatisfies ρ c :=
  GroundSatisfies.congr c (fun v hv => h.1 v (((c.bounded_iff nt nm).mp hc).1 v hv))
    (fun v hv => h.2 v (((c.bounded_iff nt nm).mp hc).2 v hv))

theorem AgreesBelow.models {η ρ nt nm} (h : AgreesBelow η ρ nt nm) {cs : Bounds}
    (hc : cs.Bounded nt nm) (hm : GroundModels ρ cs) : GroundModels η cs :=
  fun c hh => (h.satisfies (hc c hh)).mpr (hm c hh)

theorem skeleton_agreesBelow {ρ : GroundAssignment} {s : SolverState} {a target ground}
    (ha : Shape a (s.skeleton a).1) (hr : a.realize ρ = some ground)
    (hh : target.head = ground.head) :
    ∃ η, (s.skeleton a).1.realize η = some target ∧
      AgreesBelow η ρ s.nextType s.nextMode := by
  obtain ⟨η, hη, ht, hm⟩ := ha.realize_fresh hr hh
  refine ⟨η, hη, ?_, ?_⟩
  · intro v hv
    apply ht v
    intro hh
    have := (s.skeleton_identifiers ha).1 v hh
    omega
  · intro v hv
    apply hm v
    intro hh
    have := (s.skeleton_identifiers ha).2 v hh
    omega

theorem expansion_models {ρ : GroundAssignment} {s : SolverState} (hs : s.Fresh)
    {a v old ground} (ha : Shape a (s.skeleton a).1)
    (hr : a.realize ρ = some ground) (hh : (ρ.types v).head = ground.head)
    (hv : v.index < s.nextType) (hm : Models ρ s) (ho : GroundSatisfies ρ old)
    (hb : old.Bounded s.nextType s.nextMode) :
    ∃ η, Models η ((s.skeleton a).2.emit .expand [.equal v (s.skeleton a).1, old]) ∧
      AgreesBelow η ρ s.nextType s.nextMode := by
  obtain ⟨η, hη, hagree⟩ := skeleton_agreesBelow ha hr hh
  refine ⟨η, ?_, hagree⟩
  apply Models.emit
  · simpa only [Models, (s.skeleton_frame a).1, (s.skeleton_frame a).2.1] using
      hagree.models (Bounds.bounded_append.mpr ⟨hs.pending, hs.bounds⟩) hm
  · simp only [GroundModels, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, (hagree.satisfies hb).mpr ho⟩
    refine ⟨_, hη, ?_, ?_⟩ <;> rw [hagree.1 v hv] <;> exact Subtype.refl

theorem type_mode_guards {ρ a b l r}
    (h : GroundSatisfies ρ (.sub (.modal a l) (.modal b r))) :
    GroundModels ρ [.defined l, .defined r] := by
  obtain ⟨x, y, hx, hy, _⟩ := h
  simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff] at hx hy
  obtain ⟨_, _, ml, hl, _⟩ := hx
  obtain ⟨_, _, mr, hr, _⟩ := hy
  simp [GroundModels, GroundSatisfies, ModExpr.WellFormed, hl, hr]

theorem stepType_models {ρ s a b t} (hs : SolverState.Fresh s)
    (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (hm : Models ρ s) (hc : GroundSatisfies ρ (.sub a b))
    (he : stepType s a b = .success t) :
    ∃ η, Models η t ∧ AgreesBelow η ρ s.nextType s.nextMode := by
  have ho : GroundSatisfies ρ (.sub (.modal a.outer.1 a.outer.2.normalize)
      (.modal b.outer.1 b.outer.2.normalize)) := by
    simpa only [GroundSatisfies, TypeExpr.outer_normalize_realize] using hc
  have hguard := type_mode_guards ho
  have hsingle : GroundModels ρ [.sub (.modal a.outer.1 a.outer.2.normalize)
      (.modal b.outer.1 b.outer.2.normalize)] := by simpa only [GroundModels, List.mem_singleton, forall_eq] using ho
  have hbound : (Constraint.sub (.modal a.outer.1 a.outer.2.normalize)
      (.modal b.outer.1 b.outer.2.normalize)).Bounded s.nextType s.nextMode :=
    ⟨⟨ha.outer.1, ha.outer.2.normalize⟩, ⟨hb.outer.1, hb.outer.2.normalize⟩⟩
  simp only [stepType, bind, pure, RunResult.bind] at he
  repeat' split at he
  all_goals cases he
  case h_2.isFalse.refl =>
    rename_i x y n hv hnv hocc
    obtain ⟨left, right, hl, hr, hsub⟩ := ho
    simp only [hv, TypeExpr.realize, bind, pure, Option.bind_some,
      Option.bind_eq_some_iff, Option.some.injEq] at hl hr
    obtain ⟨ml, hml, rfl⟩ := hl
    obtain ⟨ground, hground, mr, hmr, rfl⟩ := hr
    apply expansion_models hs (s.skeleton_shape hnv b.outer_not_modal) hground
      (by simpa using (GroundOrder.of_subtype hsub).head)
      (by simpa only [hv, TypeExpr.Bounded] using ha.outer.1) hm _ hbound
    simpa only [GroundModels, List.mem_singleton, forall_eq] using hsingle
  case h_3.isFalse.refl =>
    rename_i x y n hv hnv hnf hocc
    obtain ⟨left, right, hl, hr, hsub⟩ := ho
    simp only [hv, TypeExpr.realize, bind, pure, Option.bind_some,
      Option.bind_eq_some_iff, Option.some.injEq] at hl hr
    obtain ⟨ground, hground, ml, hml, rfl⟩ := hl
    obtain ⟨mr, hmr, rfl⟩ := hr
    apply expansion_models hs (s.skeleton_shape hnv a.outer_not_modal) hground
      (by simpa using (GroundOrder.of_subtype hsub).head.symm)
      (by simpa only [hv, TypeExpr.Bounded] using hb.outer.1) hm _ hbound
    simpa only [GroundModels, List.mem_singleton, forall_eq] using hsingle
  all_goals refine ⟨ρ, ?_, AgreesBelow.refl _ _ _⟩
  all_goals simp_all only
  all_goals first
    | exact (hm.retain _ ho).emit _ hguard
    | exact hm.emit _ (ConstraintReduction.pair.groundModels.mp hsingle)
    | exact hm.emit _ (ConstraintReduction.sum.groundModels.mp hsingle)
    | exact hm.emit _ (ConstraintReduction.fn.groundModels.mp hsingle)
    | exact hm.emit _ (ConstraintReduction.unit.groundModels.mp hsingle)
    | exact hm.emit _ (ConstraintReduction.credit.groundModels.mp hsingle)

end SolverGround
end ModalityInference
