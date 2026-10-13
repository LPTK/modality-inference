import ModalityInference.Proofs.GroundAssignment

/-! The executable identifier lists and declarative finite supports agree. -/

namespace ModalityInference

@[simp] theorem ModExpr.mem_freeVariables (m : ModExpr) (v : ModVar) :
    v ∈ m.freeVariables ↔ v ∈ m.vars := by
  induction m <;> simp_all [ModExpr.freeVariables, ModExpr.vars]

@[simp] theorem TypeExpr.mem_typeVariables (a : Ty) (v : TypeVar) :
    v ∈ a.typeVariables ↔ v ∈ a.typeVars := by
  induction a <;> simp_all [TypeExpr.typeVariables, TypeExpr.typeVars]

@[simp] theorem TypeExpr.mem_modeVariables (a : Ty) (v : ModVar) :
    v ∈ a.modeVariables ↔ v ∈ a.modVars := by
  induction a <;> simp_all [TypeExpr.modeVariables, TypeExpr.modVars]

@[simp] theorem Constraint.mem_typeVariables (c : Constraint) (v : TypeVar) :
    v ∈ c.typeVariables ↔ v ∈ c.typeVars := by
  cases c <;> simp [Constraint.typeVariables, Constraint.typeVars]

@[simp] theorem Constraint.mem_modeVariables (c : Constraint) (v : ModVar) :
    v ∈ c.modeVariables ↔ v ∈ c.modVars := by
  cases c <;> simp [Constraint.modeVariables, Constraint.modVars]

@[simp] theorem Bounds.mem_typeVariables (cs : Bounds) (v : TypeVar) :
    v ∈ cs.typeVariables ↔ v ∈ cs.typeVars := by
  induction cs <;> simp_all [Bounds.typeVariables, show Bounds.typeVars [] = ∅ from rfl]

@[simp] theorem Bounds.mem_modeVariables (cs : Bounds) (v : ModVar) :
    v ∈ cs.modeVariables ↔ v ∈ cs.modVars := by
  induction cs <;> simp_all [Bounds.modeVariables, show Bounds.modVars [] = ∅ from rfl]

theorem Bounds.mem_typeVars_iff (cs : Bounds) (v : TypeVar) :
    v ∈ cs.typeVars ↔ ∃ c ∈ cs, v ∈ c.typeVars := by
  induction cs <;> simp_all [show Bounds.typeVars [] = ∅ from rfl]

theorem Bounds.mem_modVars_iff (cs : Bounds) (v : ModVar) :
    v ∈ cs.modVars ↔ ∃ c ∈ cs, v ∈ c.modVars := by
  induction cs <;> simp_all [show Bounds.modVars [] = ∅ from rfl]

end ModalityInference
