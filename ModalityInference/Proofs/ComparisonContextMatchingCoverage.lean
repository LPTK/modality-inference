import ModalityInference.Proofs.ComparisonExactMatchingCoverage
import ModalityInference.Proofs.ComparisonContextSpecialization

namespace ModalityInference.ComparisonContext

theorem closeComponent_pending_length (support : α → List Nat) (fuel : Nat)
    (group pending : List α) :
    (closeComponent support fuel group pending).2.length ≤ pending.length := by
  induction fuel generalizing group pending with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    simp only [closeComponent]
    split
    · exact Nat.le_refl _
    · exact (ih _ _).trans (List.length_filter_le _ _)

theorem closeComponent_covers (support : α → List Nat) (fuel : Nat)
    (group pending : List α) {request : α} (h : request ∈ group ∨ request ∈ pending) :
    request ∈ (closeComponent support fuel group pending).1 ∨
      request ∈ (closeComponent support fuel group pending).2 := by
  induction fuel generalizing group pending with
  | zero => exact h
  | succ fuel ih =>
    simp only [closeComponent]
    split
    · exact h
    · apply ih
      rcases h with h | h
      · exact Or.inl (List.mem_append_left _ h)
      · by_cases ht : (support request).any (fun name =>
          group.any fun member => (support member).contains name) = true
        · exact Or.inl (List.mem_append_right _ (List.mem_filter.mpr ⟨h, ht⟩))
        · exact Or.inr (List.mem_filter.mpr ⟨h, by simpa using ht⟩)

theorem componentsFuel_covers (support : α → List Nat) (fuel : Nat)
    (requests : List α) (hsize : requests.length ≤ fuel)
    {request : α} (h : request ∈ requests) :
    ∃ group ∈ componentsFuel support fuel requests, request ∈ group := by
  induction fuel generalizing requests with
  | zero =>
    cases requests with
    | nil => simp at h
    | cons first rest => simp at hsize
  | succ fuel ih =>
    cases requests with
    | nil => simp at h
    | cons first rest =>
      have hc := closeComponent_covers support rest.length [first] rest
        (request := request) (by simpa using h)
      rcases hc with hc | hc
      · exact ⟨_, List.mem_cons_self, hc⟩
      · have hp := closeComponent_pending_length support rest.length [first] rest
        obtain ⟨group, hg, hr⟩ := ih _ (by simpa using hp.trans (Nat.le_of_succ_le_succ hsize)) hc
        exact ⟨group, List.mem_cons_of_mem _ hg, hr⟩

theorem components_covers (support : α → List Nat) (requests : List α)
    {request : α} (h : request ∈ requests) :
    ∃ group ∈ components support requests, request ∈ group :=
  componentsFuel_covers support requests.length requests (Nat.le_refl _) h

end ModalityInference.ComparisonContext

namespace ModalityInference.ComparisonInstance

private def matchGroup (p : Prepared) (compound : Ty × Ty → Bool)
    (action : Substitution) (group : List (Ty × Ty)) : Substitution :=
  match (group.filter compound).foldlM
      (fun action request => matchType p request.1 request.2 action) action with
  | none => action
  | some selected =>
      ((group.filter fun request => !compound request).foldlM
        (fun action request => matchType p request.1 request.2 action) selected).getD selected

private theorem matchGroup_complete (p : Prepared) (compound : Ty × Ty → Bool)
    (group : List (Ty × Ty)) {before : Substitution}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (he : ∀ request ∈ group,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    AgreesWith (matchGroup p compound before group) ts ms ∧
      MatchingExtends before (matchGroup p compound before group) ∧
      ∀ request ∈ group, MatchingCovers p request.1 (matchGroup p compound before group) := by
  obtain ⟨middle, hl, hla, hle, hlc⟩ := matchTypes_complete_covers p (group.filter compound)
    ht hm ha (fun request hr => he request (List.mem_filter.mp hr).1)
  obtain ⟨after, hr, hra, hre, hrc⟩ := matchTypes_complete_covers p
    (group.filter fun request => !compound request)
    ht hm hla (fun request hr => he request (List.mem_filter.mp hr).1)
  simp only [matchGroup, hl, hr, Option.getD_some]
  refine ⟨hra, hle.trans hre, ?_⟩
  intro request hreq
  by_cases hc : compound request = true
  · exact (hlc request (List.mem_filter.mpr ⟨hreq, hc⟩)).mono hre
  · exact hrc request (List.mem_filter.mpr ⟨hreq, by simpa using hc⟩)

private theorem matchGroups_complete (p : Prepared) (compound : Ty × Ty → Bool)
    (groups : List (List (Ty × Ty))) {before : Substitution}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (he : ∀ group ∈ groups, ∀ request ∈ group,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    AgreesWith (groups.foldl (matchGroup p compound) before) ts ms ∧
      MatchingExtends before (groups.foldl (matchGroup p compound) before) ∧
      ∀ group ∈ groups, ∀ request ∈ group,
        MatchingCovers p request.1 (groups.foldl (matchGroup p compound) before) := by
  induction groups generalizing before with
  | nil => exact ⟨ha, .refl _, by simp⟩
  | cons group groups ih =>
    obtain ⟨hga, hge, hgc⟩ := matchGroup_complete p compound group ht hm ha
      (he group List.mem_cons_self)
    obtain ⟨hra, hre, hrc⟩ := ih hga (fun g hg => he g (List.mem_cons_of_mem _ hg))
    refine ⟨hra, hge.trans hre, ?_⟩
    intro g hg request hr
    rcases List.mem_cons.mp hg with rfl | hg
    · exact (hgc request hr).mono hre
    · exact hrc g hg request hr

/-- Priority partitioning and component grouping preserve completeness of a
simultaneously consistent family of exact context equations. -/
theorem solvePriorityComponents_complete (p : Prepared) (support : Ty × Ty → List Nat)
    (compound : Ty × Ty → Bool) (requests : List (Ty × Ty)) {before : Substitution}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (he : ∀ request ∈ requests,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    let after := ComparisonContext.solvePriorityComponents support compound
      (fun request action => matchType p request.1 request.2 action) requests before
    AgreesWith after ts ms ∧ MatchingExtends before after ∧
      ∀ request ∈ requests, MatchingCovers p request.1 after := by
  have hg := ComparisonContext.components_property support
    (fun request : Ty × Ty =>
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) requests he
  obtain ⟨hga, hge, hgc⟩ := matchGroups_complete p compound
    (ComparisonContext.components support requests) ht hm ha hg
  have heq : ComparisonContext.solvePriorityComponents support compound
      (fun request action => matchType p request.1 request.2 action) requests before =
      (ComparisonContext.components support requests).foldl (matchGroup p compound) before := by
    unfold ComparisonContext.solvePriorityComponents
    congr 1
    funext action group
    simp only [matchGroup]
    cases (group.filter compound).foldlM
      (fun action request => matchType p request.1 request.2 action) action <;>
      rfl
  dsimp only
  rw [heq]
  refine ⟨hga, hge, ?_⟩
  intro request hr
  obtain ⟨group, hg, hm⟩ := ComparisonContext.components_covers support requests hr
  exact hgc group hg request hm

end ModalityInference.ComparisonInstance

namespace ModalityInference.ComparisonFrozenContext

open ComparisonInstance

/-- When the collected equations are forced by one shared witness, the actual
component solver covers all of their source identifiers. -/
theorem independent_covers {p : Prepared} {total : ModExpr → Bool}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (hh : ∀ request ∈ collect p total,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    ∀ request ∈ collect p total, MatchingCovers p request.1 (independent p total) :=
  (solvePriorityComponents_complete p _ _ _ ht hm (AgreesWith.empty ts ms) hh).2.2

theorem prepare_covers {p : Prepared} {total : ModExpr → Bool} {before : Substitution}
    {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hp : prepare p total = some before)
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (hh : ∀ request ∈ collect p total,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    ∀ request ∈ collect p total, MatchingCovers p request.1 before :=
  (prepare_spec hp).2.1 ▸ independent_covers ht hm hh

end ModalityInference.ComparisonFrozenContext
