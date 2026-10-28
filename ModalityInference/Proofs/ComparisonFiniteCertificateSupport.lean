import ModalityInference.Proofs.ComparisonFiniteCertificateQueries
import ModalityInference.ComparisonFiniteCertificateBounds

/-! The finite certificate diagram introduces fresh type names, but retains
only the input's modality names. Suffix normalization preserves this support. -/
namespace ModalityInference.ComparisonFiniteCertificateSupport

open ComparisonRawCarrierSuffix ComparisonRawHeadTrace ComparisonObserverBoundary
  ComparisonFiniteCertificateBounds

noncomputable section
attribute [local instance] Classical.propDecidable

def prefixModes : Option ModExpr → Finset ModVar
  | none => ∅
  | some m => m.vars

theorem normalize_support (Δ : Bounds) (m : ModExpr) :
    prefixModes (normalize Δ m).literal ∪ (normalize Δ m).control.vars ⊆ m.vars := by
  induction m with
  | compose l r ihl ihr =>
    simp only [normalize]
    split_ifs with h
    · simp [prefixModes]
    · cases hr : (normalize Δ r).literal <;> simp only [hr,prefixModes,ModExpr.vars,Finset.empty_union] at ihr ⊢
      · simpa only [prefixModes,Finset.union_assoc] using Finset.union_subset_union ihl ihr
      · simpa only [Finset.union_assoc] using Finset.union_subset_union (Finset.Subset.refl l.vars) ihr
  | _ => simp only [normalize]; split_ifs <;> simp [prefixModes,ModExpr.epsilon,ModExpr.vars]

theorem calls_support {Δ : Bounds} {N : Finset ModVar} (a : Ty) (p : Option ModExpr)
    (ha : a.modVars ⊆ N) (hp : prefixModes p ⊆ N) :
    ∀ s ∈ calls Δ a p, s.1.modVars ⊆ N ∧ prefixModes s.2 ⊆ N := by
  induction a generalizing p <;> cases p <;>
    simp only [calls,List.forall_mem_cons,List.forall_mem_append]
  all_goals refine ⟨⟨ha,hp⟩,?_⟩
  all_goals try exact fun _ h => False.elim (List.not_mem_nil h)
  all_goals simp only [TypeExpr.modVars,Finset.union_subset_iff] at ha
  case prod.none a b iha ihb | sum.none a b iha ihb | fn.none a b iha ihb =>
    exact ⟨iha _ ha.1 hp,ihb _ ha.2 hp⟩
  case prod.some a b iha ihb p | sum.some a b iha ihb p =>
    exact ⟨iha _ ha.1 hp,ihb _ ha.2 hp⟩
  case modal.none a m ih =>
    exact ih _ ha.1 ((Finset.subset_union_left.trans (normalize_support Δ m)).trans ha.2)
  case modal.some a m ih p =>
    exact ih _ ha.1 (Finset.union_subset ha.2 hp)

theorem applyPrefix_modes (a : Ty) (p : Option ModExpr) :
    (applyPrefix p a).modVars = a.modVars ∪ prefixModes p := by
  cases p <;> simp [applyPrefix,prefixModes,TypeExpr.modVars]

theorem controlNames_support {Δ : Bounds} {N : Finset ModVar} (s : Site)
    (hs : s.1.modVars ⊆ N) : (controlNames Δ s).toFinset ⊆ N := by
  rcases s with ⟨a,p⟩
  cases a <;> cases p <;> simp only [controlNames,List.toFinset_nil,Finset.empty_subset]
  case modal.none a m =>
    simpa only [Finset.toList_toFinset] using
      ((Finset.subset_union_right.trans (normalize_support Δ m)).trans
        (Finset.subset_union_right.trans hs))

theorem rawHeads_support {sites : List Site} {N : Finset ModVar}
    (hs : ∀ s ∈ sites, s.1.modVars ⊆ N ∧ prefixModes s.2 ⊆ N) :
    ∀ a ∈ rawHeads sites, a.modVars ⊆ N := by
  intro a ha
  obtain ⟨s,h,rfl⟩ := List.mem_map.mp ha
  rw [applyPrefix_modes]
  exact Finset.union_subset (hs s h).1 (hs s h).2

theorem modeNames_support {Δ : Bounds} {sites : List Site} {N : Finset ModVar}
    (hΔ : Δ.modVars ⊆ N)
    (hs : ∀ s ∈ sites, s.1.modVars ⊆ N ∧ prefixModes s.2 ⊆ N) :
    (modeNames Δ sites).toFinset ⊆ N := by
  intro v hv
  rcases List.mem_append.mp (List.mem_toFinset.mp hv) with hv | hv
  · rcases List.mem_append.mp hv with hv | hv
    · exact hΔ (Finset.mem_toList.mp hv)
    · obtain ⟨a,ha,hv⟩ := List.mem_flatMap.mp hv
      exact rawHeads_support hs a ha (Finset.mem_toList.mp hv)
  · obtain ⟨s,h,hv⟩ := List.mem_flatMap.mp hv
    exact controlNames_support s (hs s h).1 (List.mem_toFinset.mpr hv)

theorem ofTy_modes (a : Ty) : modes (.ofTy a) = a.modVars := by
  induction a <;> simp_all only [modes,CompareTy.ofTy,TypeExpr.modVars]

theorem rawInputs_support {raw : List Ty} {queries : List CompareTy} {N : Finset ModVar}
    (hr : ∀ a ∈ raw, a.modVars ⊆ N) (hq : ∀ a ∈ queries, modes a ⊆ N) :
    ∀ a ∈ ComparisonObserverShadowQuerySupport.rawInputs raw queries, a.modVars ⊆ N := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hr a ha
  · obtain ⟨q,hq',ha⟩ := List.mem_flatMap.mp ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
      exact Finset.empty_subset _
    · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
      simpa only [TypeExpr.modVars,ModExpr.vars,Finset.empty_union,Finset.singleton_subset_iff]
        using hq q hq' (Finset.mem_toList.mp hv)

theorem boundInputs_support (Δ : Bounds) :
    ∀ a ∈ ComparisonObserverShadowModel.RawInput.boundInputs Δ, a.modVars ⊆ Δ.modVars := by
  intro a ha
  obtain ⟨c,hc,ha⟩ := List.mem_flatMap.mp ha
  cases c <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  case sub x y =>
    rcases ha with rfl | rfl
    · exact fun v hv => (Δ.mem_modVars_iff v).mpr ⟨_,hc,Finset.mem_union_left _ hv⟩
    · exact fun v hv => (Δ.mem_modVars_iff v).mpr ⟨_,hc,Finset.mem_union_right _ hv⟩

theorem sites_support {Δ : Bounds} {raw : List Ty} {queries : List CompareTy} {N : Finset ModVar}
    (hΔ : Δ.modVars ⊆ N) (hr : ∀ a ∈ raw, a.modVars ⊆ N)
    (hq : ∀ a ∈ queries, modes a ⊆ N) :
    ∀ s ∈ ComparisonObserverShadowQuerySupport.sites Δ raw queries,
      s.1.modVars ⊆ N ∧ prefixModes s.2 ⊆ N := by
  intro s hs
  obtain ⟨a,ha,hs⟩ := List.mem_flatMap.mp hs
  apply calls_support a none ?_ (Finset.empty_subset _) s hs
  rcases List.mem_append.mp ha with ha | ha
  · exact (boundInputs_support Δ a ha).trans hΔ
  · exact rawInputs_support hr hq a ha

theorem sites_input_support (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    ∀ s ∈ ComparisonObserverShadowQuerySupport.sites Δ raw queries,
      s.1.modVars ⊆ inputModes Δ raw queries ∧ prefixModes s.2 ⊆ inputModes Δ raw queries := by
  apply sites_support Finset.subset_union_left
  · intro a ha
    rw [← ofTy_modes a]
    exact (modes_subset (List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩))).trans
      Finset.subset_union_right
  · intro a ha
    exact (modes_subset (List.mem_append_right _ ha)).trans Finset.subset_union_right

theorem controlNames_length {Δ : Bounds} {N : Finset ModVar} (s : Site)
    (hs : s.1.modVars ⊆ N) : (controlNames Δ s).length ≤ N.card := by
  have hnd : (controlNames Δ s).Nodup := by
    rcases s with ⟨a,p⟩
    cases a <;> cases p <;> simp [controlNames,Finset.nodup_toList]
  rw [← List.toFinset_card_of_nodup hnd]
  exact Finset.card_le_card (controlNames_support s hs)

theorem modeNames_length {Δ : Bounds} {sites : List Site} {N : Finset ModVar}
    (hΔ : Δ.modVars ⊆ N)
    (hs : ∀ s ∈ sites, s.1.modVars ⊆ N ∧ prefixModes s.2 ⊆ N) :
    (modeNames Δ sites).length ≤ (1 + 2 * sites.length) * N.card := by
  induction sites with
  | nil => simpa [modeNames,rawHeads] using Finset.card_le_card hΔ
  | cons s sites ih =>
    have ht := fun t (h : t ∈ sites) => hs t (List.mem_cons_of_mem s h)
    have hi := ih ht
    have hh := Finset.card_le_card
      (rawHeads_support hs _ (List.mem_map.mpr ⟨s,List.mem_cons_self,rfl⟩))
    have hc := controlNames_length (Δ := Δ) s (hs s List.mem_cons_self).1
    simp only [modeNames,rawHeads,List.map_cons,List.flatMap_cons,List.length_append,
      Finset.length_toList,List.length_cons] at hi ⊢
    simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one] at hi ⊢
    omega

theorem input_modeNames_support (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    (modeNames Δ (ComparisonObserverShadowQuerySupport.sites Δ raw queries)).toFinset ⊆
      inputModes Δ raw queries :=
  modeNames_support Finset.subset_union_left (sites_input_support Δ raw queries)

theorem input_modeNames_length (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    (modeNames Δ (ComparisonObserverShadowQuerySupport.sites Δ raw queries)).length ≤
      (1 + 2 * (ComparisonObserverShadowQuerySupport.sites Δ raw queries).length) *
        (inputModes Δ raw queries).card :=
  modeNames_length Finset.subset_union_left (sites_input_support Δ raw queries)

end
end ModalityInference.ComparisonFiniteCertificateSupport
