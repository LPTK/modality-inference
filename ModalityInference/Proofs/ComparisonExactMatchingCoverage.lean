import ModalityInference.Proofs.ComparisonExactMatchingCompleteness

namespace ModalityInference.ComparisonInstance

/-- Literal matching retains all bindings accumulated by earlier requests. -/
structure MatchingExtends (before after : Substitution) : Prop where
  types : before.types ⊆ after.types
  modes : before.modes ⊆ after.modes

theorem MatchingExtends.refl (action : Substitution) : MatchingExtends action action :=
  ⟨List.Subset.refl _, List.Subset.refl _⟩

theorem MatchingExtends.trans {a b c : Substitution}
    (hab : MatchingExtends a b) (hbc : MatchingExtends b c) : MatchingExtends a c :=
  ⟨hab.types.trans hbc.types, hab.modes.trans hbc.modes⟩

theorem MatchingExtends.typeKeys {before after : Substitution}
    (h : MatchingExtends before after) :
    before.types.map Prod.fst ⊆ after.types.map Prod.fst :=
  List.map_subset _ h.types

theorem MatchingExtends.modeKeys {before after : Substitution}
    (h : MatchingExtends before after) :
    before.modes.map Prod.fst ⊆ after.modes.map Prod.fst :=
  List.map_subset _ h.modes

/-- Every replaceable identifier in the matched source has an explicit image. -/
structure MatchingCovers (p : Prepared) (source : Ty) (after : Substitution) : Prop where
  types : ∀ n, TypeVar.flex n ∈ source.typeVars → typeAllowed p (.flex n) = true →
    n ∈ after.types.map Prod.fst
  modes : ∀ n, ModVar.flex n ∈ source.modVars → modeAllowed p (.flex n) = true →
    n ∈ after.modes.map Prod.fst

theorem bindType_extends_covers {name image before after}
    (h : bindType name image before = some after) :
    MatchingExtends before after ∧ name ∈ after.types.map Prod.fst := by
  unfold bindType at h
  split at h
  · cases h
    exact ⟨⟨List.subset_cons_of_subset _ (List.Subset.refl _), List.Subset.refl _⟩,
      List.mem_cons_self⟩
  · next previous hp =>
    split at h
    · cases h
      refine ⟨.refl _, ?_⟩
      obtain ⟨left, right, he, _⟩ := List.lookup_eq_some_iff.mp hp
      rw [he]
      simp
    · contradiction

theorem bindMode_extends_covers {name image before after}
    (h : bindMode name image before = some after) :
    MatchingExtends before after ∧ name ∈ after.modes.map Prod.fst := by
  unfold bindMode at h
  split at h
  · cases h
    exact ⟨⟨List.Subset.refl _, List.subset_cons_of_subset _ (List.Subset.refl _)⟩,
      List.mem_cons_self⟩
  · next previous hp =>
    split at h
    · cases h
      refine ⟨.refl _, ?_⟩
      obtain ⟨left, right, he, _⟩ := List.lookup_eq_some_iff.mp hp
      rw [he]
      simp
    · contradiction

theorem matchMode_extends_covers {p : Prepared} {source target : ModExpr}
    {before after : Substitution}
    (h : matchMode p source target before = some after) :
    MatchingExtends before after ∧
      ∀ n, ModVar.flex n ∈ source.vars → modeAllowed p (.flex n) = true →
        n ∈ after.modes.map Prod.fst := by
  induction source generalizing target before after with
  | compose a b ia ib | join a b ia ib | meet a b ia ib
  | leftResidual a b ia ib | rightResidual a b ia ib =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    obtain ⟨hel, hcl⟩ := ia hl
    obtain ⟨her, hcr⟩ := ib hr
    refine ⟨hel.trans her, ?_⟩
    intro n hn ha
    rcases Finset.mem_union.mp hn with hn | hn
    · exact her.modeKeys (hcl n hn ha)
    · exact hcr n hn ha
  | var v =>
    cases v with
    | flex name =>
      simp only [matchMode] at h
      split at h
      · obtain ⟨he, hc⟩ := bindMode_extends_covers h
        refine ⟨he, ?_⟩
        intro n hn _
        have hn : n = name := ModVar.flex.inj (Finset.mem_singleton.mp hn)
        simpa [hn] using hc
      · next ha =>
        split at h
        · cases h
          refine ⟨.refl _, ?_⟩
          intro n hn hb
          have hn : n = name := ModVar.flex.inj (Finset.mem_singleton.mp hn)
          subst n
          contradiction
        · contradiction
    | rigid name =>
      cases target <;> (try simp only [matchMode] at h) <;> try contradiction
      next v =>
        cases v <;> simp only [matchMode] at h <;> try contradiction
        split at h
        · cases h
          exact ⟨.refl _, by simp [ModExpr.vars]⟩
        · contradiction
  | const m =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    split at h
    · cases h
      exact ⟨.refl _, by simp [ModExpr.vars]⟩
    · contradiction
  | close a ia | closeInv a ia | future a ia | capture a ia =>
    cases target <;> simp only [matchMode] at h <;> try contradiction
    exact ia h

theorem matchType_extends_covers {p : Prepared} {source target : Ty}
    {before after : Substitution}
    (h : matchType p source target before = some after) :
    MatchingExtends before after ∧ MatchingCovers p source after := by
  induction source generalizing target before after with
  | modal a m ia =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    obtain ⟨hel, hcl⟩ := ia hl
    obtain ⟨her, hcr⟩ := matchMode_extends_covers hr
    refine ⟨hel.trans her, ⟨?_, ?_⟩⟩
    · intro n hn ha
      exact her.typeKeys (hcl.types n hn ha)
    · intro n hn ha
      rcases Finset.mem_union.mp hn with hn | hn
      · exact her.modeKeys (hcl.modes n hn ha)
      · exact hcr n hn ha
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hl, hr⟩ := h
    obtain ⟨hel, hcl⟩ := ia hl
    obtain ⟨her, hcr⟩ := ib hr
    refine ⟨hel.trans her, ⟨?_, ?_⟩⟩
    · intro n hn ha
      rcases Finset.mem_union.mp hn with hn | hn
      · exact her.typeKeys (hcl.types n hn ha)
      · exact hcr.types n hn ha
    · intro n hn ha
      rcases Finset.mem_union.mp hn with hn | hn
      · exact her.modeKeys (hcl.modes n hn ha)
      · exact hcr.modes n hn ha
  | var v =>
    cases v with
    | flex name =>
      simp only [matchType] at h
      split at h
      · obtain ⟨he, hc⟩ := bindType_extends_covers h
        refine ⟨he, ⟨?_, by simp [TypeExpr.modVars]⟩⟩
        intro n hn _
        have hn : n = name := TypeVar.flex.inj (Finset.mem_singleton.mp hn)
        simpa [hn] using hc
      · next ha =>
        split at h
        · cases h
          refine ⟨.refl _, ⟨?_, by simp [TypeExpr.modVars]⟩⟩
          intro n hn hb
          have hn : n = name := TypeVar.flex.inj (Finset.mem_singleton.mp hn)
          subst n
          contradiction
        · contradiction
    | rigid name =>
      cases target <;> (try simp only [matchType] at h) <;> try contradiction
      next v =>
        cases v <;> simp only [matchType] at h <;> try contradiction
        split at h
        · cases h
          exact ⟨.refl _, ⟨by simp [TypeExpr.typeVars], by simp [TypeExpr.modVars]⟩⟩
        · contradiction
  | unit | credit =>
    cases target <;> simp only [matchType] at h <;> try contradiction
    cases h
    exact ⟨.refl _, ⟨by simp [TypeExpr.typeVars], by simp [TypeExpr.modVars]⟩⟩

theorem MatchingCovers.mono {p : Prepared} {source : Ty} {before after : Substitution}
    (hc : MatchingCovers p source before) (he : MatchingExtends before after) :
    MatchingCovers p source after :=
  ⟨fun n hn ha => he.typeKeys (hc.types n hn ha),
    fun n hn ha => he.modeKeys (hc.modes n hn ha)⟩

/-- Shared literal requests are processed together, and their complete source
support remains present in the resulting substitution. -/
theorem matchTypes_extends_covers {p : Prepared} {requests : List (Ty × Ty)}
    {before after : Substitution}
    (h : requests.foldlM (fun action request => matchType p request.1 request.2 action) before =
      some after) :
    MatchingExtends before after ∧
      ∀ request ∈ requests, MatchingCovers p request.1 after := by
  induction requests generalizing before with
  | nil =>
    cases h
    exact ⟨.refl _, by simp⟩
  | cons request requests ih =>
    simp only [List.foldlM_cons, bind, Option.bind_eq_some_iff] at h
    obtain ⟨middle, hm, hh⟩ := h
    obtain ⟨hem, hcm⟩ := matchType_extends_covers hm
    obtain ⟨her, hcr⟩ := ih hh
    refine ⟨hem.trans her, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hcm.mono her
    · exact hcr r hr

/-- Exact whole-context equations yield one successful shared matching action
that both agrees with the witness and covers every equation's identifiers. -/
theorem matchTypes_complete_covers (p : Prepared) (requests : List (Ty × Ty))
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (he : ∀ request ∈ requests,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    ∃ after, requests.foldlM (fun action request => matchType p request.1 request.2 action) before =
      some after ∧ AgreesWith after ts ms ∧ MatchingExtends before after ∧
      ∀ request ∈ requests, MatchingCovers p request.1 after := by
  obtain ⟨after, hs, hw⟩ := matchTypes_complete p requests ht hm ha he
  exact ⟨after, hs, hw, matchTypes_extends_covers hs⟩

end ModalityInference.ComparisonInstance
