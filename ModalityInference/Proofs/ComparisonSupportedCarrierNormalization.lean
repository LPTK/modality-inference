import ModalityInference.Proofs.ComparisonWitnessRestriction
import ModalityInference.Proofs.ComparisonCarrierBodyArity

namespace ModalityInference.ComparisonWitnessRestriction

open ComparisonPartialCarrier

theorem restrict_carrier {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes) {a : CompareTy}
    (h : Carrier Δ a) : Carrier Δ (restrictTy types modes a) := by
  induction a with
  | var v =>
    by_cases hv : v ∈ types <;>
      simp [restrictTy, CompareTy.subst, ComparisonTypeRestriction.restrict, hv, Carrier]
  | unit | credit => trivial
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | modal a m ih => exact ih h
  | join a b _ _ | meet a b _ _ =>
    exact ⟨restrictTy_defined ht hm h.1, restrictTy_defined ht hm h.2⟩

theorem restrict_join (types : Finset TypeVar) (modes : Finset ModVar)
    (a : CompareTy) (as : List CompareTy) :
    restrictTy types modes (ComparisonInterpolation.join a as) =
      ComparisonInterpolation.join (restrictTy types modes a) (as.map (restrictTy types modes)) := by
  induction as generalizing a <;> simp_all [ComparisonInterpolation.join, restrictTy, CompareTy.subst]

theorem restrict_meet (types : Finset TypeVar) (modes : Finset ModVar)
    (a : CompareTy) (as : List CompareTy) :
    restrictTy types modes (ComparisonInterpolation.meet a as) =
      ComparisonInterpolation.meet (restrictTy types modes a) (as.map (restrictTy types modes)) := by
  induction as generalizing a <;> simp_all [ComparisonInterpolation.meet, restrictTy, CompareTy.subst]

theorem restrict_family {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes) {a : CompareTy} {lower upper : Nat}
    (h : FamilyForm Δ lower upper a) : FamilyForm Δ lower upper (restrictTy types modes a) := by
  cases h with
  | carrier hc => exact .carrier (restrict_carrier ht hm hc)
  | @lower head rest hc hlen =>
    rw [restrict_join]
    refine .lower ?_ (by simpa only [List.length_cons, List.length_map] using hlen)
    simpa only [←List.map_cons, List.forall_mem_map] using
      (fun a ha => restrict_carrier ht hm (hc a ha))
  | @upper head rest hc hlen =>
    rw [restrict_meet]
    refine .upper ?_ (by simpa only [List.length_cons, List.length_map] using hlen)
    simpa only [←List.map_cons, List.forall_mem_map] using
      (fun a ha => restrict_carrier ht hm (hc a ha))

theorem restrict_type_cases (types : Finset TypeVar) (modes : Finset ModVar)
    (action : CompareSubstitution) (v : TypeVar) :
    (restrict types modes action).type v = restrictTy types modes (action.type v) ∨
      (restrict types modes action).type v = .var v := by
  cases v <;> simp only [restrict, CompareSubstitution.type, lookup_map_values]
  case flex n => cases action.types.lookup n <;> simp
  case rigid => exact Or.inr trivial

theorem restrict_family_type {Δ : Bounds} {types : Finset TypeVar} {modes : Finset ModVar}
    (ht : Δ.typeVars ⊆ types) (hm : Δ.modVars ⊆ modes) {action : CompareSubstitution}
    {v : TypeVar} {lower upper : Nat} (h : FamilyForm Δ lower upper (action.type v)) :
    FamilyForm Δ lower upper ((restrict types modes action).type v) := by
  rcases restrict_type_cases types modes action v with he | he
  · exact he.symm ▸ restrict_family ht hm h
  · exact he.symm ▸ FamilyForm.carrier (Δ := Δ) (a := .var v) trivial

/-- Every algebraic scheme witness has a simultaneous input-supported normal
form, with a finite carrier family per parameter. Carrier term size and the
modality expressions are not bounded by this theorem. -/
theorem algebra_supported_normalized {source target : Scheme}
    (h : AlgebraSubsumes [] source target) :
    let p := SchemePreparation.prepare [] source target
    ∃ action requests, ComparisonPreparation.PreparedWitness p action ∧ Supported p action ∧
      requests.length ≤ parameterOccurrences p.sourceType ∧
      ∀ v, FamilyForm p.assumptions (requestDemands requests v true).length
        (requestDemands requests v false).length (action.type v) := by
  obtain ⟨σ, hσ⟩ := ComparisonPreparation.prepare_algebra_complete h
  obtain ⟨plan, hsize, τ, hτ, _, _, _, hn⟩ := prepared_bounded_normalized_witness hσ
  refine ⟨restrict _ _ τ, plan.requests, prepared_restrict hτ, restrict_support _ _ τ, hsize, ?_⟩
  intro v
  exact restrict_family_type (fun v hv => by simp [inputTypes, hv])
    (fun v hv => by simp [inputModes, hv]) (hn v)

end ModalityInference.ComparisonWitnessRestriction
