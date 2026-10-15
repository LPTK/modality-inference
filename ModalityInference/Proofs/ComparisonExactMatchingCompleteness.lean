import ModalityInference.Proofs.ComparisonPartialCancellation
import ModalityInference.Proofs.ComparisonInstance

namespace ModalityInference.ComparisonInstance

/-- Every selected image is the restriction of one shared witness assignment. -/
structure AgreesWith (action : Substitution) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) : Prop where
  types : ∀ entry ∈ action.types, ts (.flex entry.1) = CompareTy.ofTy entry.2
  modes : ∀ entry ∈ action.modes, ms (.flex entry.1) = entry.2

 theorem AgreesWith.empty (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr) : AgreesWith {} ts ms :=
  ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩

private theorem lookup_entry {α : Type} {entries : List (Nat × α)} {name : Nat} {image : α}
    (h : entries.lookup name = some image) : (name, image) ∈ entries := by
  obtain ⟨left, right, rfl, _⟩ := List.lookup_eq_some_iff.mp h
  exact List.mem_append_right _ List.mem_cons_self

 theorem bindType_complete {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ha : AgreesWith before ts ms) {name : Nat} {image : Ty} (hi : ts (.flex name) = CompareTy.ofTy image) :
    ∃ after, bindType name image before = some after ∧ AgreesWith after ts ms := by
  cases hl : before.types.lookup name with
  | none =>
    refine ⟨{before with types := (name, image) :: before.types}, by simp [bindType, hl], ?_⟩
    refine ⟨?_, ha.modes⟩
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact hi
    · exact ha.types entry he
  | some previous =>
    have hp := ha.types (name, previous) (lookup_entry hl)
    have he : previous = image := by
      have he := hp.symm.trans hi
      have inj (a b : Ty) : CompareTy.ofTy a = CompareTy.ofTy b ↔ a = b := by
        induction a generalizing b <;> cases b <;> simp_all [CompareTy.ofTy]
      exact (inj previous image).mp he
    subst previous
    exact ⟨before, by simp [bindType, hl], ha⟩

 theorem bindMode_complete {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ha : AgreesWith before ts ms) {name : Nat} {image : ModExpr} (hi : ms (.flex name) = image) :
    ∃ after, bindMode name image before = some after ∧ AgreesWith after ts ms := by
  cases hl : before.modes.lookup name with
  | none =>
    refine ⟨{before with modes := (name, image) :: before.modes}, by simp [bindMode, hl], ?_⟩
    refine ⟨ha.types, ?_⟩
    intro entry he
    rcases List.mem_cons.mp he with rfl | he
    · exact hi
    · exact ha.modes entry he
  | some previous =>
    have hp := ha.modes (name, previous) (lookup_entry hl)
    have he : previous = image := hp.symm.trans hi
    subst previous
    exact ⟨before, by simp [bindMode, hl], ha⟩

 theorem matchMode_subst_complete (p : Prepared) (source : ModExpr)
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hf : ∀ v, modeAllowed p v = false → ms v = .var v) (ha : AgreesWith before ts ms) :
    ∃ after, matchMode p source (source.subst ms) before = some after ∧ AgreesWith after ts ms := by
  induction source generalizing before with
  | var v =>
    cases v with
    | flex name =>
      by_cases hn : modeAllowed p (.flex name) = true
      · simpa only [matchMode, ModExpr.subst, hn, ↓reduceIte] using bindMode_complete ha (name := name) rfl
      · have hn' : modeAllowed p (.flex name) = false := Bool.eq_false_iff.mpr hn
        exact ⟨before, by simp [matchMode, ModExpr.subst, hn', hf _ hn'], ha⟩
    | rigid name =>
      exact ⟨before, by simp [matchMode, ModExpr.subst, hf (.rigid name) rfl], ha⟩
  | const mode => exact ⟨before, by simp [matchMode, ModExpr.subst], ha⟩
  | compose a b ia ib | join a b ia ib | meet a b ia ib
  | leftResidual a b ia ib | rightResidual a b ia ib =>
    obtain ⟨middle, hm, hmA⟩ := ia ha
    obtain ⟨after, hh, hhA⟩ := ib hmA
    exact ⟨after, by simp only [ModExpr.subst, matchMode, hm, bind, Option.bind_some, hh], hhA⟩
  | close a ia | closeInv a ia | future a ia | capture a ia => exact ia ha

 theorem matchMode_complete (p : Prepared) {source target : ModExpr}
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hf : ∀ v, modeAllowed p v = false → ms v = .var v) (ha : AgreesWith before ts ms)
    (he : source.subst ms = target) :
    ∃ after, matchMode p source target before = some after ∧ AgreesWith after ts ms := by
  subst target
  exact matchMode_subst_complete p source hf ha

/-- Literal matching reconstructs every exact internal instance. Earlier
bindings and repeated occurrences stay restrictions of the same witness. -/
 theorem matchType_complete (p : Prepared) {source target : Ty}
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (he : (CompareTy.ofTy source).subst ts ms = CompareTy.ofTy target) :
    ∃ after, matchType p source target before = some after ∧ AgreesWith after ts ms := by
  induction source generalizing target before with
  | var v =>
    cases v with
    | flex name =>
      by_cases hn : typeAllowed p (.flex name) = true
      · simpa only [matchType, hn, ↓reduceIte] using bindType_complete ha he
      · have hn' : typeAllowed p (.flex name) = false := Bool.eq_false_iff.mpr hn
        have he' : CompareTy.var (.flex name) = CompareTy.ofTy target := (ht _ hn').symm.trans he
        cases target <;> simp only [CompareTy.ofTy] at he' <;> try contradiction
        next v =>
          have hv : TypeVar.flex name = v := CompareTy.var.inj he'
          subst v
          exact ⟨before, by simp [matchType, hn'], ha⟩
    | rigid name =>
      have he' : CompareTy.var (.rigid name) = CompareTy.ofTy target := (ht (.rigid name) rfl).symm.trans he
      cases target <;> simp only [CompareTy.ofTy] at he' <;> try contradiction
      next v =>
        have hv : TypeVar.rigid name = v := CompareTy.var.inj he'
        subst v
        exact ⟨before, by simp [matchType], ha⟩
  | unit | credit =>
    cases target <;> simp only [CompareTy.ofTy, CompareTy.subst] at he <;> try contradiction
    exact ⟨before, rfl, ha⟩
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    cases target <;> simp only [CompareTy.ofTy, CompareTy.subst] at he <;> try contradiction
    all_goals
      injection he with he₁ he₂
      obtain ⟨middle, hl, hlA⟩ := ia ha he₁
      obtain ⟨after, hr, hrA⟩ := ib hlA he₂
      exact ⟨after, by simp only [matchType, hl, bind, Option.bind_some, hr], hrA⟩
  | modal a m ia =>
    cases target <;> simp only [CompareTy.ofTy, CompareTy.subst] at he <;> try contradiction
    case modal b n =>
      have hh := CompareTy.modal.inj he
      obtain ⟨middle, hl, hlA⟩ := ia ha hh.1
      obtain ⟨after, hr, hrA⟩ := matchMode_complete p hm hlA hh.2
      exact ⟨after, by simp only [matchType, hl, bind, Option.bind_some, hr], hrA⟩

 theorem matchType_frozen_complete (p : Prepared) {source target : Ty} {m : ModExpr}
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms) (hp : ¬Entails p.assumptions (.defined m))
    (h : AlgebraSubtype p.assumptions (.modal ((CompareTy.ofTy source).subst ts ms) m)
      (.modal (.ofTy target) m)) :
    ∃ after, matchType p source target before = some after ∧ AgreesWith after ts ms :=
  matchType_complete p ht hm ha
    ((ComparisonPartialStructuredCapsule.partial_public_context_iff hΔ hR hp).mp h)

 theorem matchType_frozen_complete_reverse (p : Prepared) {source target : Ty} {m : ModExpr}
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms) (hp : ¬Entails p.assumptions (.defined m))
    (h : AlgebraSubtype p.assumptions (.modal (.ofTy target) m)
      (.modal ((CompareTy.ofTy source).subst ts ms) m)) :
    ∃ after, matchType p source target before = some after ∧ AgreesWith after ts ms :=
  matchType_complete p ht hm ha
    ((ComparisonPartialStructuredCapsule.public_partial_context_iff hΔ hR hp).mp h)

/-- Every finite collection of exact contexts can be matched together. One
witness controls all repeated type and modality identifiers across requests. -/
 theorem matchTypes_complete (p : Prepared) (requests : List (Ty × Ty))
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (he : ∀ request ∈ requests,
      (CompareTy.ofTy request.1).subst ts ms = CompareTy.ofTy request.2) :
    ∃ after, requests.foldlM (fun action request => matchType p request.1 request.2 action) before =
      some after ∧ AgreesWith after ts ms := by
  induction requests generalizing before with
  | nil => exact ⟨before, rfl, ha⟩
  | cons request requests ih =>
    obtain ⟨middle, hl, hlA⟩ := matchType_complete p ht hm ha (he request List.mem_cons_self)
    obtain ⟨after, hr, hrA⟩ := ih hlA (fun r hr => he r (List.mem_cons_of_mem _ hr))
    exact ⟨after, by simp only [List.foldlM_cons, hl, bind, Option.bind_some, hr], hrA⟩

 theorem matchTypes_frozen_complete (p : Prepared) (requests : List (Ty × Ty))
    {before : Substitution} {ts : TypeVar → CompareTy} {ms : ModVar → ModExpr}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (ht : ∀ v, typeAllowed p v = false → ts v = .var v)
    (hm : ∀ v, modeAllowed p v = false → ms v = .var v)
    (ha : AgreesWith before ts ms)
    (hh : ∀ request ∈ requests, ∃ m, ¬Entails p.assumptions (.defined m) ∧
      (AlgebraSubtype p.assumptions (.modal ((CompareTy.ofTy request.1).subst ts ms) m)
        (.modal (.ofTy request.2) m) ∨
       AlgebraSubtype p.assumptions (.modal (.ofTy request.2) m)
        (.modal ((CompareTy.ofTy request.1).subst ts ms) m))) :
    ∃ after, requests.foldlM (fun action request => matchType p request.1 request.2 action) before =
      some after ∧ AgreesWith after ts ms := by
  apply matchTypes_complete p requests ht hm ha
  intro request hr
  obtain ⟨m, hp, hh⟩ := hh request hr
  exact hh.elim
    ((ComparisonPartialStructuredCapsule.partial_public_context_iff hΔ hR hp).mp)
    ((ComparisonPartialStructuredCapsule.public_partial_context_iff hΔ hR hp).mp)

end ModalityInference.ComparisonInstance
