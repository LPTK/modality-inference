import ModalityInference.Proofs.ComparisonContextSpecialization
import ModalityInference.Proofs.ComparisonExactMatchingCoverage

namespace ModalityInference.ComparisonInstance

open ComparisonExactContext

/-- Matching a literal fixed target keeps all assignments in the prepared
source scope. -/
theorem bindType_scoped {p : Prepared} {name : Nat} {image : Ty} {before after : Substitution}
    (h : bindType name image before = some after) (hn : typeAllowed p (.flex name) = true)
    (ht : ∀ v ∈ image.typeVars, typeAllowed p v = false)
    (hm : ∀ v ∈ image.modVars, modeAllowed p v = false)
    (hb : Scoped p before) : Scoped p after := by
  unfold bindType at h
  split at h
  · cases h
    refine ⟨?_, hb.2⟩
    intro n t he
    rcases List.mem_cons.mp he with he | he
    · cases he; exact ⟨hn, ht, hm⟩
    · exact hb.1 n t he
  · split at h
    · cases h; exact hb
    · contradiction

theorem bindMode_scoped {p : Prepared} {name : Nat} {image : ModExpr} {before after : Substitution}
    (h : bindMode name image before = some after) (hn : modeAllowed p (.flex name) = true)
    (hm : ∀ v ∈ image.vars, modeAllowed p v = false)
    (hb : Scoped p before) : Scoped p after := by
  unfold bindMode at h
  split at h
  · cases h
    refine ⟨hb.1, ?_⟩
    intro n t he
    rcases List.mem_cons.mp he with he | he
    · cases he; exact ⟨hn, hm⟩
    · exact hb.2 n t he
  · split at h
    · cases h; exact hb
    · contradiction

theorem matchMode_scoped {p : Prepared} {source target : ModExpr} {before after : Substitution}
    (h : matchMode p source target before = some after)
    (ht : ∀ v ∈ target.vars, modeAllowed p v = false) (hb : Scoped p before) :
    Scoped p after := by
  induction source generalizing target before after
  case compose a b ia ib | meet a b ia ib | join a b ia ib |
      leftResidual a b ia ib | rightResidual a b ia ib =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    exact ib hr (fun v hv => ht v (Finset.mem_union_right _ hv))
      (ia hl (fun v hv => ht v (Finset.mem_union_left _ hv)) hb)
  case var v =>
    cases v with
    | flex n =>
      simp only [matchMode] at h
      split at h
      · next hn => exact bindMode_scoped h hn ht hb
      · split at h
        · cases h; exact hb
        · contradiction
    | rigid n =>
      cases target <;> (try simp only [matchMode] at h) <;> try contradiction
      next v =>
        cases v <;> simp only [matchMode] at h <;> try contradiction
        split at h
        · cases h; exact hb
        · contradiction
  case const m =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    split at h
    · cases h; exact hb
    · contradiction
  case close a ih | closeInv a ih | future a ih | capture a ih =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    exact ih h ht hb

theorem matchType_scoped {p : Prepared} {source target : Ty} {before after : Substitution}
    (h : matchType p source target before = some after)
    (ht : ∀ v ∈ target.typeVars, typeAllowed p v = false)
    (hm : ∀ v ∈ target.modVars, modeAllowed p v = false) (hb : Scoped p before) :
    Scoped p after := by
  induction source generalizing target before after
  case prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    exact ib hr (fun v hv => ht v (Finset.mem_union_right _ hv))
      (fun v hv => hm v (Finset.mem_union_right _ hv))
      (ia hl (fun v hv => ht v (Finset.mem_union_left _ hv))
        (fun v hv => hm v (Finset.mem_union_left _ hv)) hb)
  case modal a m ih =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    exact matchMode_scoped hr (fun v hv => hm v (Finset.mem_union_right _ hv))
      (ih hl ht (fun v hv => hm v (Finset.mem_union_left _ hv)) hb)
  case var v =>
    cases v with
    | flex n =>
      simp only [matchType] at h
      split at h
      · next hn => exact bindType_scoped h hn ht hm hb
      · split at h
        · cases h; exact hb
        · contradiction
    | rigid n =>
      cases target <;> (try simp only [matchType] at h) <;> try contradiction
      next v =>
        cases v <;> simp only [matchType] at h <;> try contradiction
        split at h
        · cases h; exact hb
        · contradiction
  case unit | credit =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    cases h; exact hb

theorem matchTypes_scoped {p : Prepared} (requests : List (Ty × Ty))
    {before after : Substitution}
    (h : requests.foldlM (fun action r => matchType p r.1 r.2 action) before = some after)
    (ht : ∀ r ∈ requests, ∀ v ∈ r.2.typeVars, typeAllowed p v = false)
    (hm : ∀ r ∈ requests, ∀ v ∈ r.2.modVars, modeAllowed p v = false)
    (hb : Scoped p before) : Scoped p after := by
  induction requests generalizing before with
  | nil => cases h; exact hb
  | cons r rs ih =>
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    exact ih hr (fun r hr => ht r (List.mem_cons_of_mem _ hr))
      (fun r hr => hm r (List.mem_cons_of_mem _ hr))
      (matchType_scoped hl (ht r List.mem_cons_self) (hm r List.mem_cons_self) hb)

/-- Exact shared requests produce an actual scoped matching action that covers
every requested source key and preserves the original witness assignments. -/
theorem matchTypes_complete_scoped_covers (p : Prepared) (requests : List (Ty × Ty))
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms) (hs : Scoped p before)
    (hfixed : ∀ r ∈ requests,
      (∀ v ∈ r.2.typeVars, typeAllowed p v = false) ∧
        ∀ v ∈ r.2.modVars, modeAllowed p v = false)
    (he : ∀ request ∈ requests,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    ∃ after, requests.foldlM (fun action request => matchType p request.1 request.2 action) before =
      some after ∧ AgreesWith after ts ms ∧ Scoped p after ∧ MatchingExtends before after ∧
      ∀ request ∈ requests, MatchingCovers p request.1 after := by
  obtain ⟨after, hh, ha, hx, hc⟩ := matchTypes_complete_covers p requests ht hm ha he
  exact ⟨after, hh, ha, matchTypes_scoped requests hh
    (fun r hr => (hfixed r hr).1) (fun r hr => (hfixed r hr).2) hs, hx, hc⟩

end ModalityInference.ComparisonInstance
