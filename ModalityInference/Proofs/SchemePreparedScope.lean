import ModalityInference.SchemePreparation
import ModalityInference.Proofs.SchemeFreshening

/-! Preparation separates existing identifiers, fresh target skolems, and fresh
source binders. The scope facts include quantified identifiers that occur only
in a body or are unused, and do not require duplicate-free parameter lists. -/
namespace ModalityInference.SchemePreparation

def originalTypeIds (ambient : Bounds) (source target : Scheme) : List TypeVar :=
  ((source.typeParams.map TypeVar.flex ++ source.body.typeVariables ++ source.bounds.typeVariables) ++
    (target.typeParams.map TypeVar.flex ++ target.body.typeVariables ++ target.bounds.typeVariables)) ++
    ambient.typeVariables

def originalModeIds (ambient : Bounds) (source target : Scheme) : List ModVar :=
  ((source.modParams.map ModVar.flex ++ source.body.modeVariables ++ source.bounds.modeVariables) ++
    (target.modParams.map ModVar.flex ++ target.body.modeVariables ++ target.bounds.modeVariables)) ++
    ambient.modeVariables

private theorem fresh_type_param (s : Scheme) (nt nm : Nat) (rigid : Bool)
    {n : Nat} (hn : n ∈ s.typeParams) :
    ∃ i, i < s.typeParams.length ∧ (s.freshSubstitution nt nm rigid).type (.flex n) =
      .var (if rigid then .rigid (nt + i) else .flex (nt + i)) := by
  cases he : (s.freshSubstitution nt nm rigid).types.lookup n with
  | none =>
    exact False.elim ((lookup_fresh_none (by simpa [Scheme.freshSubstitution] using he)) hn)
  | some a =>
    obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.typeParams)
      (f := fun i => (.var (if rigid then .rigid (nt + i) else .flex (nt + i)) : Ty))
      (by simpa [Scheme.freshSubstitution] using he)
    exact ⟨i, (List.getElem?_eq_some_iff.mp hi).1,
      by simp only [Substitution.type, he, Option.getD_some]⟩

private theorem fresh_mode_param (s : Scheme) (nt nm : Nat) (rigid : Bool)
    {n : Nat} (hn : n ∈ s.modParams) :
    ∃ i, i < s.modParams.length ∧ (s.freshSubstitution nt nm rigid).mode (.flex n) =
      .var (if rigid then .rigid (nm + i) else .flex (nm + i)) := by
  cases he : (s.freshSubstitution nt nm rigid).modes.lookup n with
  | none =>
    exact False.elim ((lookup_fresh_none (by simpa [Scheme.freshSubstitution] using he)) hn)
  | some a =>
    obtain ⟨i, hi, rfl⟩ := lookup_fresh_some (xs := s.modParams)
      (f := fun i => (.var (if rigid then .rigid (nm + i) else .flex (nm + i)) : ModExpr))
      (by simpa [Scheme.freshSubstitution] using he)
    exact ⟨i, (List.getElem?_eq_some_iff.mp hi).1,
      by simp only [Substitution.mode, he, Option.getD_some]⟩

theorem original_type_lt_start {ambient : Bounds} {source target : Scheme} {v : TypeVar}
    (hv : v ∈ originalTypeIds ambient source target) :
    v.index < (source.subsumptionIndices ambient target).1 := by
  rcases List.mem_append.mp hv with hst | ha
  · rcases List.mem_append.mp hst with hs | ht
    · have hs : v.index < source.freshTypeIndex :=
        (freshFold_bounds TypeVar.index _ 0).2 v hs
      exact hs.trans_le ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))
    · have ht : v.index < target.freshTypeIndex :=
        (freshFold_bounds TypeVar.index _ 0).2 v ht
      exact ht.trans_le ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  · exact (Bounds.lt_freshTypeIndex ha).trans_le (Nat.le_max_right _ _)

theorem original_mode_lt_start {ambient : Bounds} {source target : Scheme} {v : ModVar}
    (hv : v ∈ originalModeIds ambient source target) :
    v.index < (source.subsumptionIndices ambient target).2 := by
  rcases List.mem_append.mp hv with hst | ha
  · rcases List.mem_append.mp hst with hs | ht
    · have hs : v.index < source.freshModeIndex :=
        (freshFold_bounds ModVar.index _ 0).2 v hs
      exact hs.trans_le ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))
    · have ht : v.index < target.freshModeIndex :=
        (freshFold_bounds ModVar.index _ 0).2 v ht
      exact ht.trans_le ((Nat.le_max_right _ _).trans (Nat.le_max_left _ _))
  · exact (Bounds.lt_freshModeIndex ha).trans_le (Nat.le_max_right _ _)

theorem original_type_lt_first {ambient : Bounds} {source target : Scheme} {v : TypeVar}
    (hv : v ∈ originalTypeIds ambient source target) :
    v.index < (prepare ambient source target).firstType :=
  (original_type_lt_start hv).trans_le (Nat.le_add_right _ _)

theorem original_mode_lt_first {ambient : Bounds} {source target : Scheme} {v : ModVar}
    (hv : v ∈ originalModeIds ambient source target) :
    v.index < (prepare ambient source target).firstMode :=
  (original_mode_lt_start hv).trans_le (Nat.le_add_right _ _)

theorem prepare_source_type_param (ambient : Bounds) (source target : Scheme)
    {n : Nat} (hn : n ∈ source.typeParams) :
    ∃ k, (prepare ambient source target).sourceRenaming.type (.flex n) = .var (.flex k) ∧
      (prepare ambient source target).firstType ≤ k ∧
      k < (prepare ambient source target).nextType := by
  obtain ⟨i, hi, he⟩ := fresh_type_param source
    (prepare ambient source target).firstType (prepare ambient source target).firstMode false hn
  exact ⟨_, he, Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩

theorem prepare_source_mode_param (ambient : Bounds) (source target : Scheme)
    {n : Nat} (hn : n ∈ source.modParams) :
    ∃ k, (prepare ambient source target).sourceRenaming.mode (.flex n) = .var (.flex k) ∧
      (prepare ambient source target).firstMode ≤ k ∧
      k < (prepare ambient source target).nextMode := by
  obtain ⟨i, hi, he⟩ := fresh_mode_param source
    (prepare ambient source target).firstType (prepare ambient source target).firstMode false hn
  exact ⟨_, he, Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩

/-- Every declared type quantifier is skolemized; no occurrence in the target's
bounds is required. The interval precedes all fresh source type binders. -/
theorem prepare_target_type_param (ambient : Bounds) (source target : Scheme)
    {n : Nat} (hn : n ∈ target.typeParams) :
    ∃ k, (prepare ambient source target).targetRenaming.type (.flex n) = .var (.rigid k) ∧
      (source.subsumptionIndices ambient target).1 ≤ k ∧
      k < (prepare ambient source target).firstType := by
  obtain ⟨i, hi, he⟩ := fresh_type_param target
    (source.subsumptionIndices ambient target).1 (source.subsumptionIndices ambient target).2 true hn
  exact ⟨_, he, Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩

/-- Body-only and unused modality quantifiers are skolemized by the same rule as
those occurring in declared bounds. -/
theorem prepare_target_mode_param (ambient : Bounds) (source target : Scheme)
    {n : Nat} (hn : n ∈ target.modParams) :
    ∃ k, (prepare ambient source target).targetRenaming.mode (.flex n) = .var (.rigid k) ∧
      (source.subsumptionIndices ambient target).2 ≤ k ∧
      k < (prepare ambient source target).firstMode := by
  obtain ⟨i, hi, he⟩ := fresh_mode_param target
    (source.subsumptionIndices ambient target).1 (source.subsumptionIndices ambient target).2 true hn
  exact ⟨_, he, Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩

theorem prepare_source_type_fixed (ambient : Bounds) (source target : Scheme)
    (v : TypeVar) (hv : v ∉ source.typeParams.map TypeVar.flex) :
    (prepare ambient source target).sourceRenaming.type v = .var v := by
  have hi : Instantiates source (prepare ambient source target).sourceRenaming :=
    source.freshSubstitution_instantiates _ _ false
  cases v with
  | rigid n => rfl
  | flex n =>
    apply Substitution.type_fresh
    intro hn
    exact hv (List.mem_map.mpr ⟨n, hi.1.mem_iff.mp hn, rfl⟩)

theorem prepare_source_mode_fixed (ambient : Bounds) (source target : Scheme)
    (v : ModVar) (hv : v ∉ source.modParams.map ModVar.flex) :
    (prepare ambient source target).sourceRenaming.mode v = .var v := by
  have hi : Instantiates source (prepare ambient source target).sourceRenaming :=
    source.freshSubstitution_instantiates _ _ false
  cases v with
  | rigid n => rfl
  | flex n =>
    apply Substitution.mode_fresh
    intro hn
    exact hv (List.mem_map.mpr ⟨n, hi.2.mem_iff.mp hn, rfl⟩)

theorem prepare_source_type_fresh (ambient : Bounds) (source target : Scheme)
    {n : Nat} (hn : n ∈ source.typeParams) :
    ∃ k, (prepare ambient source target).sourceRenaming.type (.flex n) = .var (.flex k) ∧
      .flex k ∉ originalTypeIds ambient source target := by
  obtain ⟨k, he, hlo, _⟩ := prepare_source_type_param ambient source target hn
  exact ⟨k, he, fun hk => (Nat.not_lt.mpr hlo) (original_type_lt_first hk)⟩

theorem prepare_source_mode_fresh (ambient : Bounds) (source target : Scheme)
    {n : Nat} (hn : n ∈ source.modParams) :
    ∃ k, (prepare ambient source target).sourceRenaming.mode (.flex n) = .var (.flex k) ∧
      .flex k ∉ originalModeIds ambient source target := by
  obtain ⟨k, he, hlo, _⟩ := prepare_source_mode_param ambient source target hn
  exact ⟨k, he, fun hk => (Nat.not_lt.mpr hlo) (original_mode_lt_first hk)⟩

theorem prepare_target_type_fresh (ambient : Bounds) (source target : Scheme)
    {n : Nat} (hn : n ∈ target.typeParams) :
    ∃ k, (prepare ambient source target).targetRenaming.type (.flex n) = .var (.rigid k) ∧
      .rigid k ∉ originalTypeIds ambient source target := by
  obtain ⟨k, he, hlo, _⟩ := prepare_target_type_param ambient source target hn
  exact ⟨k, he, fun hk => (Nat.not_lt.mpr hlo) (original_type_lt_start hk)⟩

theorem prepare_target_mode_fresh (ambient : Bounds) (source target : Scheme)
    {n : Nat} (hn : n ∈ target.modParams) :
    ∃ k, (prepare ambient source target).targetRenaming.mode (.flex n) = .var (.rigid k) ∧
      .rigid k ∉ originalModeIds ambient source target := by
  obtain ⟨k, he, hlo, _⟩ := prepare_target_mode_param ambient source target hn
  exact ⟨k, he, fun hk => (Nat.not_lt.mpr hlo) (original_mode_lt_start hk)⟩

end ModalityInference.SchemePreparation
