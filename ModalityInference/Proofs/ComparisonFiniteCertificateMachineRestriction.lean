import ModalityInference.ComparisonFiniteCertificateMachineRestriction
import ModalityInference.Proofs.ComparisonObserverBoundary
import ModalityInference.Proofs.VariableOccurrences
import ModalityInference.Proofs.ComparisonObserverMachineRestriction
import ModalityInference.Proofs.ComparisonFiniteCertificateEmbedding
import ModalityInference.Proofs.ComparisonFiniteCertificateChecks

/-! Restricting a certificate's machine to input atom names and its finite
control alphabet preserves original bounds and supported endpoint values. -/
namespace ModalityInference.ComparisonFiniteCertificate

open ComparisonObserverBoundary

theorem inputTypes_query {Δ : Bounds} {queries : List CompareTy} {a : CompareTy}
    (ha : a ∈ queries) : types a ⊆ (inputTypes Δ queries).toFinset := by
  intro v hv
  exact List.mem_toFinset.mpr (List.mem_dedup.mpr (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨a,ha,(mem_typeList a v).mpr hv⟩)))

theorem types_ofTy (a : Ty) : types (.ofTy a) = a.typeVars := by
  induction a <;> simp_all [types, CompareTy.ofTy, TypeExpr.typeVars]

theorem inputTypes_context (Δ : Bounds) (queries : List CompareTy) :
    Δ.typeVars ⊆ (inputTypes Δ queries).toFinset := by
  intro v hv
  exact List.mem_toFinset.mpr (List.mem_dedup.mpr
    (List.mem_append_left _ ((Bounds.mem_typeVariables Δ v).mpr hv)))

theorem inputTypes_bound {Δ : Bounds} (queries : List CompareTy) {a b : Ty}
    (hab : Constraint.sub a b ∈ Δ) :
    types (.ofTy a) ⊆ (inputTypes Δ queries).toFinset ∧
      types (.ofTy b) ⊆ (inputTypes Δ queries).toFinset := by
  rw [types_ofTy, types_ofTy]
  constructor
  · intro v hv
    exact inputTypes_context Δ queries ((Bounds.mem_typeVars_iff Δ v).mpr
      ⟨.sub a b,hab,Finset.mem_union_left _ hv⟩)
  · intro v hv
    exact inputTypes_context Δ queries ((Bounds.mem_typeVars_iff Δ v).mpr
      ⟨.sub a b,hab,Finset.mem_union_right _ hv⟩)

theorem shadow_modVars (Δ : Bounds) : (shadow Δ).modVars = Δ.modVars := by
  apply Finset.ext
  intro v
  simp only [Bounds.mem_modVars_iff, shadow, List.mem_map]
  constructor
  · rintro ⟨c,⟨d,hd,rfl⟩,hv⟩
    refine ⟨d,hd,?_⟩
    cases d <;> exact hv
  · rintro ⟨c,hc,hv⟩
    refine ⟨_,⟨c,hc,rfl⟩,?_⟩
    cases c <;> exact hv

namespace Candidate

open ComparisonFiniteControlEncoding ComparisonObserverMachineCheck

variable {Δ : Bounds} {names : List ModVar} (C : Candidate Δ names) (kept : List TypeVar)

theorem restrictMachine_vectors :
    ComparisonObserverRangeEncoding.vectors (C.restrictMachine kept).machine =
      ComparisonObserverRangeEncoding.vectors C.machine := rfl

theorem restrictMachine_operations : (C.restrictMachine kept).operations = C.operations := by
  unfold operations ComparisonExecutableRangeAgreement.rawOperations
  congr 1
  funext m x i
  exact ComparisonObserverMachineRestriction.action_restrict (C.machine i) (expression_support m) (x i)

theorem restrictMachine_embeddingCheck : (C.restrictMachine kept).embeddingCheck = C.embeddingCheck := by
  unfold embeddingCheck
  rw [C.restrictMachine_vectors kept, C.restrictMachine_operations kept]
  rfl

theorem restrictMachine_structureCheck (h : C.structureCheck = true) :
    (C.restrictMachine kept).structureCheck = true := by
  have hm := C.machine_checked h
  simp only [structureCheck, Bool.and_eq_true] at h ⊢
  have hn : (shadow Δ).modVars ⊆ names.toFinset := by
    rw [shadow_modVars]
    exact of_decide_eq_true h.1.1.1.1
  have hr := ComparisonObserverMachineRestriction.check_restrict
    (types' := kept) hn (fun a b => by
      simpa only [shadow_eq] using ComparisonBalancedProjection.sub_not_mem_shadow Δ a b) hm
  exact ⟨⟨⟨⟨h.1.1.1.1,hr⟩,h.1.1.2⟩,
    (C.restrictMachine_embeddingCheck kept).trans h.1.2⟩,h.2⟩

theorem restrictMachine_atom {v : TypeVar} (hv : v ∈ kept) :
    (C.restrictMachine kept).data.atom v = C.data.atom v :=
  congrArg C.defined (ComparisonObserverMachineRestriction.atom_restrict C.machine hv)

theorem restrictMachine_eval_eq (a : CompareTy) (p : Option ModExpr)
    (ha : ComparisonObserverBoundary.types a ⊆ kept.toFinset) :
    (C.restrictMachine kept).data.eval a p = C.data.eval a p := by
  induction a generalizing p
  case modal a m ih =>
    cases p with
    | some p => exact ih _ ha
    | none =>
      exact congrArg (C.data.shift (C.data.control
        (ComparisonExecutableSuffix.normalize C.data.total m).control)) (ih _ ha)
  case prod a b iha ihb =>
    exact congrArg₂ (C.data.prod p) (iha p (Finset.subset_union_left.trans ha))
      (ihb p (Finset.subset_union_right.trans ha))
  case sum a b iha ihb =>
    exact congrArg₂ (C.data.sum p) (iha p (Finset.subset_union_left.trans ha))
      (ihb p (Finset.subset_union_right.trans ha))
  case fn a b iha ihb =>
    cases p with
    | some p => rfl
    | none =>
      exact congrArg₂ C.data.fn (iha none (Finset.subset_union_left.trans ha))
        (ihb none (Finset.subset_union_right.trans ha))
  case join a b iha ihb =>
    cases p with
    | some p => rfl
    | none =>
      exact congrArg₂ C.data.join (iha none (Finset.subset_union_left.trans ha))
        (ihb none (Finset.subset_union_right.trans ha))
  case meet a b iha ihb =>
    cases p with
    | some p => rfl
    | none =>
      exact congrArg₂ C.data.meet (iha none (Finset.subset_union_left.trans ha))
        (ihb none (Finset.subset_union_right.trans ha))
  case var v =>
    cases p with
    | some p => rfl
    | none =>
      exact C.restrictMachine_atom kept
        (List.mem_toFinset.mp (ha (Finset.mem_singleton_self v)))
  case unit | credit => cases p <;> rfl

omit kept in
theorem restrictMachine_boundsCheck (queries : List CompareTy) :
    (C.restrictMachine (inputTypes Δ queries)).boundsCheck = C.boundsCheck := by
  apply Bool.eq_iff_iff.mpr
  simp only [boundsCheck, List.all_eq_true]
  apply forall_congr' fun c => imp_congr_right fun hc => ?_
  cases c with
  | sub a b =>
    obtain ⟨ha,hb⟩ := inputTypes_bound queries hc
    simp only [ComparisonExecutableSyntax.Data.evalRaw,
      C.restrictMachine_eval_eq _ (.ofTy a) none ha,
      C.restrictMachine_eval_eq _ (.ofTy b) none hb]
    rfl
  | mode | defined | equal | equiv => rfl

omit kept in
theorem restrictMachine_check (queries : List CompareTy) (h : C.check = true) :
    (C.restrictMachine (inputTypes Δ queries)).check = true := by
  simp only [check, Bool.and_eq_true] at h ⊢
  exact ⟨C.restrictMachine_structureCheck _ h.1,
    (C.restrictMachine_boundsCheck queries).trans h.2⟩

omit kept in
theorem restrictMachine_separates (queries : List CompareTy) {a b : CompareTy}
    (ha : a ∈ queries) (hb : b ∈ queries) (h : C.separates a b = true) :
    (C.restrictMachine (inputTypes Δ queries)).separates a b = true := by
  simp only [separates, Bool.and_eq_true] at h ⊢
  refine ⟨C.restrictMachine_check queries h.1, ?_⟩
  rw [C.restrictMachine_eval_eq _ a none (inputTypes_query ha),
    C.restrictMachine_eval_eq _ b none (inputTypes_query hb)]
  exact h.2

@[simp] theorem restrictMachine_states : (C.restrictMachine kept).states = C.states := rfl

@[simp] theorem restrictMachine_tags : (C.restrictMachine kept).tags = C.tags := rfl

@[simp] theorem restrictMachine_observations :
    (C.restrictMachine kept).observations = C.observations := rfl

@[simp] theorem restrictMachine_types : (C.restrictMachine kept).types = kept := rfl

@[simp] theorem restrictMachine_modes : (C.restrictMachine kept).modes = names := rfl

@[simp] theorem restrictMachine_atoms_length (i : Fin C.states) :
    ((C.restrictMachine kept).machine i).atoms.length = kept.length :=
  ComparisonObserverMachineRestriction.atoms_length _

@[simp] theorem restrictMachine_modes_length (i : Fin C.states) :
    ((C.restrictMachine kept).machine i).modes.length = names.length :=
  ComparisonObserverMachineRestriction.modes_length _

end Candidate
end ModalityInference.ComparisonFiniteCertificate
