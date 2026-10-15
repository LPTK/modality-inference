import ModalityInference.Proofs.ComparisonContextSupport
import ModalityInference.Proofs.SchemePreparedScope

/-! Preparation and positive context specialization preserve the finite
identifier bounds used by subsequent fresh comparison allocation. -/
namespace ModalityInference

theorem Constraint.Bounded.assumptions {c : Constraint} {nt nm : Nat}
    (h : c.Bounded nt nm) : c.assumptions.Bounded nt nm := by
  cases c <;>
    simp_all only [Constraint.assumptions, Bounds.bounded_append, Bounds.bounded_cons,
      Bounds.bounded_nil, Constraint.Bounded, TypeExpr.Bounded, and_true]
  all_goals aesop (add safe apply [TypeExpr.Bounded.wellFormedBounds])

theorem Bounds.Bounded.assumptions {bounds : Bounds} {nt nm : Nat}
    (h : bounds.Bounded nt nm) : bounds.assumptions.Bounded nt nm := by
  intro c hc
  obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hc
  exact (h b hb).assumptions c hc

theorem Scheme.freshSubstitution_bounded (s : Scheme) (nt nm : Nat) (rigid : Bool)
    (ht : ∀ n ∈ s.typeParams, n < nt) (hm : ∀ n ∈ s.modParams, n < nm) :
    (s.freshSubstitution nt nm rigid).Bounded
      (nt + s.typeParams.length) (nm + s.modParams.length) := by
  constructor
  · intro n a ha
    simp only [Scheme.freshSubstitution, List.mem_map, Prod.exists, Prod.mk.injEq] at ha
    obtain ⟨name, i, hi, rfl, rfl⟩ := ha
    have he := List.mk_mem_zipIdx_iff_getElem?.mp hi
    refine ⟨(ht name (List.mem_of_getElem? he)).trans_le (Nat.le_add_right _ _), ?_⟩
    have hi' := (List.getElem?_eq_some_iff.mp he).1
    cases rigid <;> exact Nat.add_lt_add_left hi' nt
  · intro n m ha
    simp only [Scheme.freshSubstitution, List.mem_map, Prod.exists, Prod.mk.injEq] at ha
    obtain ⟨name, i, hi, rfl, rfl⟩ := ha
    have he := List.mk_mem_zipIdx_iff_getElem?.mp hi
    refine ⟨(hm name (List.mem_of_getElem? he)).trans_le (Nat.le_add_right _ _), ?_⟩
    have hi' := (List.getElem?_eq_some_iff.mp he).1
    cases rigid <;> exact Nat.add_lt_add_left hi' nm

namespace SchemePreparation

theorem prepare_sourceRenaming_bounded (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).sourceRenaming.Bounded
      (prepare ambient source target).nextType (prepare ambient source target).nextMode := by
  apply Scheme.freshSubstitution_bounded
  · intro n hn
    exact original_type_lt_first (v := .flex n) (by simp [originalTypeIds, hn])
  · intro n hn
    exact original_mode_lt_first (v := .flex n) (by simp [originalModeIds, hn])

theorem prepare_targetRenaming_bounded (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).targetRenaming.Bounded
      (prepare ambient source target).firstType (prepare ambient source target).firstMode := by
  apply Scheme.freshSubstitution_bounded
  · intro n hn
    exact original_type_lt_start (v := .flex n) (by simp [originalTypeIds, hn])
  · intro n hn
    exact original_mode_lt_start (v := .flex n) (by simp [originalModeIds, hn])

theorem original_bounded (ambient : Bounds) (source target : Scheme) :
    let indices := source.subsumptionIndices ambient target
    source.body.Bounded indices.1 indices.2 ∧ source.bounds.Bounded indices.1 indices.2 ∧
      target.body.Bounded indices.1 indices.2 ∧ target.bounds.Bounded indices.1 indices.2 ∧
      ambient.Bounded indices.1 indices.2 := by
  simp only [TypeExpr.bounded_iff, Bounds.bounded_iff]
  repeat' constructor
  all_goals intro v hv
  all_goals first
    | exact original_type_lt_start (ambient := ambient) (source := source) (target := target)
        (by simp [originalTypeIds, TypeExpr.mem_typeVariables, Bounds.mem_typeVariables, hv])
    | exact original_mode_lt_start (ambient := ambient) (source := source) (target := target)
        (by simp [originalModeIds, TypeExpr.mem_modeVariables, Bounds.mem_modeVariables, hv])

theorem prepare_sourceType_bounded (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).sourceType.Bounded
      (prepare ambient source target).nextType (prepare ambient source target).nextMode :=
  (prepare_sourceRenaming_bounded ambient source target).ty
    ((original_bounded ambient source target).1.mono
      (by dsimp [prepare]; omega) (by dsimp [prepare]; omega))

theorem prepare_sourceBounds_bounded (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).sourceBounds.Bounded
      (prepare ambient source target).nextType (prepare ambient source target).nextMode :=
  (prepare_sourceRenaming_bounded ambient source target).bounds
    ((original_bounded ambient source target).2.1.mono
      (by dsimp [prepare]; omega) (by dsimp [prepare]; omega))

theorem prepare_targetType_bounded_first (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).targetType.Bounded
      (prepare ambient source target).firstType (prepare ambient source target).firstMode :=
  (prepare_targetRenaming_bounded ambient source target).ty
    ((original_bounded ambient source target).2.2.1.mono
      (Nat.le_add_right _ _) (Nat.le_add_right _ _))

theorem prepare_assumptions_bounded_first (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).assumptions.Bounded
      (prepare ambient source target).firstType (prepare ambient source target).firstMode := by
  apply Bounds.bounded_append.mpr
  refine ⟨(original_bounded ambient source target).2.2.2.2.mono
    (Nat.le_add_right _ _) (Nat.le_add_right _ _), ?_⟩
  exact ((prepare_targetRenaming_bounded ambient source target).bounds
    ((original_bounded ambient source target).2.2.2.1.mono
      (Nat.le_add_right _ _) (Nat.le_add_right _ _))).assumptions

theorem prepare_targetType_bounded (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).targetType.Bounded
      (prepare ambient source target).nextType (prepare ambient source target).nextMode :=
  (prepare_targetType_bounded_first ambient source target).mono
    (Nat.le_add_right _ _) (Nat.le_add_right _ _)

theorem prepare_assumptions_bounded (ambient : Bounds) (source target : Scheme) :
    (prepare ambient source target).assumptions.Bounded
      (prepare ambient source target).nextType (prepare ambient source target).nextMode :=
  (prepare_assumptions_bounded_first ambient source target).mono
    (Nat.le_add_right _ _) (Nat.le_add_right _ _)

end SchemePreparation

end ModalityInference
