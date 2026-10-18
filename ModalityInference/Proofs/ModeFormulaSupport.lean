import ModalityInference.Proofs.ComparisonControls

/-! Boolean projection and guard compilation preserve the modality variables
of their source expressions and bounds. -/
namespace ModalityInference

theorem ModExpr.project_variables (m : ModExpr) :
    (∀i∈m.project.locality.atoms, SymbolicModes.atomVariable i∈m.vars) ∧
    (∀i∈m.project.affinity.atoms, SymbolicModes.atomVariable i∈m.vars) ∧
    (∀i∈m.project.uniqueness.atoms, SymbolicModes.atomVariable i∈m.vars) ∧
    (∀i∈m.project.defined.atoms, SymbolicModes.atomVariable i∈m.vars) := by
  induction m with
  | var v => simp [ModExpr.project,BoolExpr.atoms,ModExpr.vars,
      ComparisonControls.atomVariable_atomIndex]
  | const m => simp [ModExpr.project,BoolExpr.atoms]
  | compose a b iha ihb | meet a b iha ihb | join a b iha ihb | leftResidual a b iha ihb | rightResidual a b iha ihb =>
    simp_all only [ModExpr.project,BoolExpr.atoms,BoolExpr.all,List.foldr,
      ModExpr.vars,List.mem_dedup,List.mem_append,List.not_mem_nil,or_false,
      Finset.mem_union,or_imp,forall_and]
    aesop
  | close a ih | closeInv a ih | future a ih | capture a ih =>
    simp_all [ModExpr.project,BoolExpr.atoms,ModExpr.vars]

theorem ModExpr.project_defined_variables {m : ModExpr} {i : Nat}
    (h : i∈m.project.defined.atoms) : SymbolicModes.atomVariable i∈m.vars :=
  (m.project_variables).2.2.2 i h


theorem modeFormula_variables {a b : ModExpr} {i : Nat}
    (h : i∈(modeFormula a b).atoms) : SymbolicModes.atomVariable i∈a.vars∪b.vars := by
  have ha := a.project_variables
  have hb := b.project_variables
  simp only [modeFormula,BoolExpr.all,List.foldr,BoolExpr.atoms,
    List.mem_dedup,List.mem_append,List.not_mem_nil,or_false] at h
  simp only [Finset.mem_union]
  aesop

theorem constraintModeFormula_variables {c : Constraint} {i : Nat}
    (h : i∈(constraintModeFormula c).atoms) : SymbolicModes.atomVariable i∈c.modVars := by
  cases c with
  | mode a b => exact modeFormula_variables h
  | defined m => exact m.project_defined_variables h
  | sub a b | equal a b | equiv a b => simp [constraintModeFormula,BoolExpr.atoms] at h

theorem boundsModeFormula_variables {cs : Bounds} {i : Nat}
    (h : i∈(boundsModeFormula cs).atoms) : SymbolicModes.atomVariable i∈cs.modVars := by
  induction cs with
  | nil => simp [boundsModeFormula,BoolExpr.all,BoolExpr.atoms] at h
  | cons c cs ih =>
    have hh : i∈(constraintModeFormula c).atoms ∨ i∈(boundsModeFormula cs).atoms := by
      simpa [boundsModeFormula,BoolExpr.all,BoolExpr.atoms] using h
    apply (Bounds.mem_modVars_iff _ _).mpr
    rcases hh with hh|hh
    · exact ⟨c,List.mem_cons_self,constraintModeFormula_variables hh⟩
    · obtain ⟨d,hd,hi⟩ := (Bounds.mem_modVars_iff _ _).mp (ih hh)
      exact ⟨d,List.mem_cons_of_mem _ hd,hi⟩

end ModalityInference
