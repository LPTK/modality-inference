import ModalityInference.ComparisonInputAction
import ModalityInference.Proofs.ComparisonTypeModeClosure
import ModalityInference.Proofs.ComparisonSelectedBases

/-! Discarding type assignments outside the actual prepared input retains all
source obligations and the body. Exact public quantified domains are restored
by ComparisonPreparation.reconstruct. -/
namespace ModalityInference.ComparisonSelectedBases

open ComparisonPreparation ComparisonWitnessRestriction

theorem mem_inputTypeKeys (p : SchemePreparation.Prepared) (n : Nat) :
    n∈inputTypeKeys p ↔ TypeVar.flex n∈inputNames p ∧ p.firstType≤n := by
  simp only [inputTypeKeys,List.mem_filterMap]
  constructor
  · rintro ⟨v,hv,he⟩
    cases v with
    | rigid => cases he
    | flex k =>
      change (if p.firstType≤k then some k else none)=some n at he
      by_cases hk : p.firstType≤k
      · simp only [if_pos hk,Option.some.injEq] at he
        subst k
        exact ⟨hv,hk⟩
      · simp [hk] at he
  · rintro ⟨hn,hk⟩
    exact ⟨.flex n,hn,by simp only [if_pos hk]⟩

theorem inputAction_keys (p : SchemePreparation.Prepared) (σ : CompareSubstitution) :
    (inputAction p σ).types.map Prod.fst=inputTypeKeys p := by
  simp [inputAction,List.map_map,Function.comp_def]

theorem inputAction_type {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (hσ : σ.DomainsAbove p.firstType p.firstMode) {v : TypeVar} (hv : v∈inputNames p) :
    (inputAction p σ).type v=σ.type v := by
  cases v with
  | rigid => rfl
  | flex n =>
    by_cases hn : p.firstType≤n
    · change (((inputTypeKeys p).map (fun k => (k,σ.type (.flex k)))).lookup n).getD _ = _
      rw [List.lookup_graph _ ((mem_inputTypeKeys p n).mpr ⟨hv,hn⟩)]
      rfl
    · have hk : n∉inputTypeKeys p := fun hk => hn ((mem_inputTypeKeys p n).mp hk).2
      have he : ((inputTypeKeys p).map (fun k => (k,σ.type (.flex k)))).lookup n=none := by
        apply List.lookup_eq_none_iff.mpr
        intro entry he
        obtain ⟨k,hk',rfl⟩ := List.mem_map.mp he
        exact bne_iff_ne.mpr (fun heq => hk (heq ▸ hk'))
      change (((inputTypeKeys p).map (fun k => (k,σ.type (.flex k)))).lookup n).getD _ = _
      rw [he]
      exact (hσ.type_fixed (.flex n) (by simpa only [TypeVar.index] using Nat.lt_of_not_ge hn)).symm

theorem inputAction_prepared {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (hw : PreparedWitnessUnder p σ) : PreparedWitnessUnder p (inputAction p σ) := by
  have hbody : (inputAction p σ).ty p.sourceType=σ.ty p.sourceType :=
    CompareSubstitution.ty_congr_on _ _ _
      (fun v hv => inputAction_type hw.1.1 ((mem_inputNames p v).mpr (by simp [inputTypes,hv])))
      (fun _ _ => rfl)
  refine ⟨⟨?_,?_,?_,hbody ▸ hw.1.2.2.2⟩,?_,hbody ▸ hw.2.2⟩
  · refine ⟨?_,hw.1.1.2⟩
    intro entry he
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
    exact ((mem_inputTypeKeys p n).mp hn).2
  · intro entry he
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp he
    exact σ.type_wellShaped hw.1.2.1 (.flex n)
  · apply (CompareSubstitution.algebra_bounds_congr (inputAction p σ) σ p.sourceBounds ?_ ?_).mpr hw.1.2.2.1
    · intro c hc v hv
      apply inputAction_type hw.1.1
      apply (mem_inputNames p v).mpr
      have hv' := (p.sourceBounds.mem_typeVars_iff v).mpr ⟨c,hc,hv⟩
      simp [inputTypes,hv']
    · intro _ _ _ _
      rfl
  · refine ⟨?_,hw.2.1.modes⟩
    apply (CompareSubstitution.wellFormedUnder_of_images
      (σ:={types:=(inputAction p σ).types}) ?_ (by simp)).types
    intro entry he
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp he
    exact hw.2.1.types (.flex n)

theorem inputAction_supported {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : Supported p σ) : Supported p (inputAction p σ) := by
  refine ⟨?_,h.2⟩
  intro entry he
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp he
  exact h.type ((mem_inputNames p _).mp ((mem_inputTypeKeys p n).mp hn).1)

theorem inputAction_modesIdempotent {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (h : σ.ModesIdempotent) : (inputAction p σ).ModesIdempotent :=
  h.of_modes_eq rfl

theorem inputAction_key_scope (p : SchemePreparation.Prepared) (σ : CompareSubstitution)
    {n : Nat} (hn : n∈(inputAction p σ).types.map Prod.fst) : TypeVar.flex n∈inputNames p :=
  ((mem_inputTypeKeys p n).mp (inputAction_keys p σ ▸ hn)).1

end ModalityInference.ComparisonSelectedBases
