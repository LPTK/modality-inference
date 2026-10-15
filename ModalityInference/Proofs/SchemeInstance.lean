import ModalityInference.SchemeInstance
import ModalityInference.Proofs.RefinedContexts

namespace ModalityInference.Scheme

private theorem guard_typeVariables (a : Ty) : a.wellFormedBounds.typeVariables = [] := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, Bounds.typeVariables, Constraint.typeVariables]

private theorem guard_modeVariables (a : Ty) (v : ModVar) :
    v ∈ a.wellFormedBounds.modeVariables ↔ v ∈ a.modeVariables := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, Bounds.modeVariables,
    Constraint.modeVariables, TypeExpr.modeVariables]

@[simp] theorem instanceGuards_typeVariables (s : Scheme) (v : TypeVar) :
    v ∈ s.instanceGuards.typeVariables ↔ v ∈ s.typeParams.map TypeVar.flex := by
  simp only [instanceGuards, Bounds.typeVariables, List.flatMap_append, List.mem_dedup,
    List.mem_append, List.flatMap_map, Constraint.typeVariables,
    TypeExpr.typeVariables]
  have he : v ∉ s.body.wellFormedBounds.flatMap Constraint.typeVariables := by
    simpa [Bounds.typeVariables] using
      congrArg (v ∈ ·) (guard_typeVariables s.body)
  simp [he, List.mem_flatMap, eq_comm]

@[simp] theorem instanceGuards_modeVariables (s : Scheme) (v : ModVar) :
    v ∈ s.instanceGuards.modeVariables ↔ v ∈ s.body.modeVariables ∨
      v ∈ s.modParams.map ModVar.flex := by
  simp only [instanceGuards, Bounds.modeVariables, List.flatMap_append, List.mem_dedup,
    List.mem_append, List.flatMap_map, Constraint.modeVariables, TypeExpr.modeVariables]
  have he : v ∈ s.body.wellFormedBounds.flatMap Constraint.modeVariables ↔
      v ∈ s.body.modeVariables := by
    simpa only [Bounds.modeVariables, List.mem_dedup] using guard_modeVariables s.body v
  simp [he, List.mem_flatMap, ModExpr.freeVariables, eq_comm]

private theorem typeVariables_append_mem (a b : Bounds) (v : TypeVar) :
    v ∈ (a ++ b).typeVariables ↔ v ∈ a.typeVariables ∨ v ∈ b.typeVariables := by
  simp only [Bounds.typeVariables, List.flatMap_append, List.mem_dedup, List.mem_append]

private theorem modeVariables_append_mem (a b : Bounds) (v : ModVar) :
    v ∈ (a ++ b).modeVariables ↔ v ∈ a.modeVariables ∨ v ∈ b.modeVariables := by
  simp only [Bounds.modeVariables, List.flatMap_append, List.mem_dedup, List.mem_append]

@[simp] theorem requireDefinedInstances_freshTypeIndex (s : Scheme) :
    s.requireDefinedInstances.freshTypeIndex = s.freshTypeIndex := by
  have he (n : Nat) : s.requireDefinedInstances.freshTypeIndex ≤ n ↔ s.freshTypeIndex ≤ n := by
    simp only [freshTypeIndex, requireDefinedInstances, freshFold_le_iff, List.mem_append,
      typeVariables_append_mem, instanceGuards_typeVariables, or_imp, forall_and]
    tauto
  exact Nat.le_antisymm ((he _).mpr (Nat.le_refl _)) ((he _).mp (Nat.le_refl _))

@[simp] theorem requireDefinedInstances_freshModeIndex (s : Scheme) :
    s.requireDefinedInstances.freshModeIndex = s.freshModeIndex := by
  have he (n : Nat) : s.requireDefinedInstances.freshModeIndex ≤ n ↔ s.freshModeIndex ≤ n := by
    simp only [freshModeIndex, requireDefinedInstances, freshFold_le_iff, List.mem_append,
      modeVariables_append_mem, instanceGuards_modeVariables, or_imp, forall_and]
    tauto
  exact Nat.le_antisymm ((he _).mpr (Nat.le_refl _)) ((he _).mp (Nat.le_refl _))

@[simp] theorem requireDefinedInstances_subsumptionIndices (s t : Scheme) (Δ : Bounds) :
    s.requireDefinedInstances.subsumptionIndices Δ t = s.subsumptionIndices Δ t := by
  simp only [subsumptionIndices, requireDefinedInstances_freshTypeIndex,
    requireDefinedInstances_freshModeIndex]

end ModalityInference.Scheme
