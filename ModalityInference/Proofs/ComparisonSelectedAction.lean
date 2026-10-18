import ModalityInference.ComparisonSelectedAction
import ModalityInference.Proofs.ComparisonSelectedReification

/-! The executable image-family reconstruction preserves exact key lists and
uses one common modality action across every selected type. -/
namespace ModalityInference.ComparisonSelectedBases

open ComparisonAlgebra ComparisonStructuralLattice ComparisonPreparation ComparisonWitnessRestriction

theorem reifyEntries_spec {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool} {modes : ModVar → ModExpr}
    {entries : List (Nat × CNF)} {types : List (Nat × CompareTy)}
    (h : reifyEntries first p solved world modes entries=some types) :
    types.map Prod.fst=entries.map Prod.fst ∧
      ∀entry∈types, ∃clauses, (entry.1,clauses)∈entries ∧
        reifyClosedImage first p solved world modes (.flex entry.1) clauses=some entry.2 := by
  induction entries generalizing types with
  | nil => simp [reifyEntries] at h; subst types; simp
  | cons entry rest ih =>
    rcases entry with ⟨n,clauses⟩
    cases ht : reifyClosedImage first p solved world modes (.flex n) clauses with
    | none => simp [reifyEntries,ht] at h
    | some type =>
      cases hr : reifyEntries first p solved world modes rest with
      | none => simp [reifyEntries,ht,hr] at h
      | some tail =>
        have he : (n,type)::tail=types := by simpa [reifyEntries,ht,hr] using h
        subst types
        refine ⟨by simp [(ih hr).1], ?_⟩
        intro entry he
        rcases List.mem_cons.mp he with rfl | he
        · exact ⟨clauses,List.mem_cons_self,ht⟩
        · obtain ⟨clauses,hc,hct⟩ := (ih hr).2 entry he
          exact ⟨clauses,List.mem_cons_of_mem _ hc,hct⟩

theorem reifyEntries_complete {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool} {modes : ModVar → ModExpr}
    {entries : List (Nat × CNF)}
    (h : ∀entry∈entries, ∃t,
      reifyClosedImage first p solved world modes (.flex entry.1) entry.2=some t) :
    ∃types, reifyEntries first p solved world modes entries=some types := by
  induction entries with
  | nil => exact ⟨[],rfl⟩
  | cons entry rest ih =>
    rcases entry with ⟨n,clauses⟩
    obtain ⟨type,ht⟩ := h (n,clauses) List.mem_cons_self
    obtain ⟨tail,hr⟩ := ih (fun entry he => h entry (List.mem_cons_of_mem _ he))
    exact ⟨(n,type)::tail,by simp [reifyEntries,ht,hr]⟩

theorem reifyAction_spec {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {modes : List (Nat × ModExpr)} {entries : List (Nat × CNF)} {action : CompareSubstitution}
    (h : reifyAction first p solved world modes entries=some action) :
    action.modes=modes ∧ action.types.map Prod.fst=entries.map Prod.fst ∧
      ∀entry∈action.types, ∃clauses, (entry.1,clauses)∈entries ∧
        reifyClosedImage first p solved world action.mode (.flex entry.1) clauses=some entry.2 := by
  cases hr : reifyEntries first p solved world ({modes:=modes} : CompareSubstitution).mode entries with
  | none => simp [reifyAction,hr] at h
  | some types =>
    have he : ({types:=types,modes:=modes} : CompareSubstitution)=action := by
      simpa [reifyAction,hr] using h
    subst action
    exact ⟨rfl,reifyEntries_spec hr⟩

theorem lookup_none_of_keys {α β : Type} {xs : List (Nat × α)} {ys : List (Nat × β)}
    (hk : xs.map Prod.fst=ys.map Prod.fst) {n : Nat} (h : xs.lookup n=none) :
    ys.lookup n=none := by
  have hn : n∉xs.map Prod.fst := by
    intro hn
    obtain ⟨entry,he,hkey⟩ := List.mem_map.mp hn
    have hh := List.lookup_eq_none_iff.mp h entry he
    simp [hkey] at hh
  apply List.lookup_eq_none_iff.mpr
  intro entry he
  apply bne_iff_ne.mpr
  intro hkey
  exact hn (hk ▸ List.mem_map.mpr ⟨entry,he,hkey.symm⟩)

theorem reifyAction_replacement {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {σ τ : CompareSubstitution} {entries : List (Nat × CNF)}
    (h : reifyAction first p solved world σ.modes entries=some τ)
    (hk : entries.map Prod.fst=σ.types.map Prod.fst)
    (hw : PreparedWitnessUnder p σ.closeTypeModes)
    (he : ∀entry∈entries, ∀t,
      reifyClosedImage first p solved world σ.mode (.flex entry.1) entry.2=some t →
      t.DefinedUnder p.assumptions ∧ Equiv p.assumptions t (σ.closeTypeModes.type (.flex entry.1))) :
    PreparedWitnessUnder p τ := by
  obtain ⟨hm,hkeys,hentries⟩ := reifyAction_spec h
  have hmfun : τ.mode=σ.mode := by funext v; cases v <;> simp [CompareSubstitution.mode,hm]
  have hkeys' : τ.types.map Prod.fst=σ.closeTypeModes.types.map Prod.fst :=
    hkeys.trans (hk.trans σ.closeTypeModes_keys.symm)
  have hout : ∀entry∈τ.types, entry.2.DefinedUnder p.assumptions ∧
      Equiv p.assumptions entry.2 (σ.closeTypeModes.type (.flex entry.1)) := by
    intro entry hx
    obtain ⟨clauses,hc,ht⟩ := hentries entry hx
    rw [hmfun] at ht
    exact he (entry.1,clauses) hc entry.2 ht
  have hrep : ComparisonStructuralBasis.Replacement p.assumptions σ.closeTypeModes τ := by
    refine ⟨?_,?_,fun v => congrFun hmfun v⟩
    · intro v
      cases v with
      | rigid n => exact .refl trivial
      | flex n =>
        cases hl : τ.types.lookup n with
        | none =>
          have ho := lookup_none_of_keys hkeys' hl
          simp only [CompareSubstitution.type,hl,ho,Option.getD_none]
          exact .refl trivial
        | some a =>
          obtain ⟨left,right,hlist,_⟩ := List.lookup_eq_some_iff.mp hl
          have he := (hout (n,a) (by simp [hlist])).2.symm
          simpa only [CompareSubstitution.type,hl,Option.getD_some] using he
    · intro v
      cases v with
      | rigid n => simp [CompareSubstitution.type, CompareTy.DefinedUnder,
          CompareTy.wellFormedBounds, ModeModels]
      | flex n =>
        cases hl : τ.types.lookup n with
        | none => simp [CompareSubstitution.type,hl,CompareTy.DefinedUnder,
            CompareTy.wellFormedBounds,ModeModels]
        | some a =>
          obtain ⟨left,right,hlist,_⟩ := List.lookup_eq_some_iff.mp hl
          simpa only [CompareSubstitution.type,hl,Option.getD_some] using
            (hout (n,a) (by simp [hlist])).1
  apply hrep.prepared rfl hw
  · refine ⟨?_,?_⟩
    · intro entry hx
      have hn : entry.1∈σ.closeTypeModes.types.map Prod.fst :=
        hkeys' ▸ List.mem_map.mpr ⟨entry,hx,rfl⟩
      obtain ⟨old,hold,hkey⟩ := List.mem_map.mp hn
      exact hkey ▸ hw.1.1.1 old hold
    · intro entry hx
      exact hw.1.1.2 entry (by simpa only [CompareSubstitution.closeTypeModes,hm] using hx)
  · intro entry hx
    exact (hout entry hx).2.1.wellShaped_left

theorem BranchPolynomials.reifyAction {ambient : Bounds} {source target : Scheme}
    {first : Nat} {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {σ : CompareSubstitution}
    (h : BranchPolynomials first (SchemePreparation.prepare ambient source target) solved world σ)
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hi : σ.ModesIdempotent)
    (hkeys : ∀n∈σ.types.map Prod.fst,
      TypeVar.flex n∈inputNames (SchemePreparation.prepare ambient source target)) :
    let p := SchemePreparation.prepare ambient source target
    ∃entries τ, ComparisonSelectedBases.reifyAction first p solved world σ.modes entries=some τ ∧
      entries.map Prod.fst=σ.types.map Prod.fst ∧
      τ.types.map Prod.fst=σ.types.map Prod.fst ∧ τ.modes=σ.modes ∧ PreparedWitnessUnder p τ := by
  classical
  let p := SchemePreparation.prepare ambient source target
  have hc : ∀n, ∃clauses, n∈σ.types.map Prod.fst → ∃t,
      ComparisonSelectedBases.reifyClosedImage first p solved world σ.mode (.flex n) clauses=some t ∧
      t.DefinedUnder p.assumptions ∧ Equiv p.assumptions t (σ.closeTypeModes.type (.flex n)) := by
    intro n
    by_cases hn : n∈σ.types.map Prod.fst
    · obtain ⟨clauses,t,ht,hd,he⟩ := h.reifyClosedImage hw (hkeys n hn)
      exact ⟨clauses,fun _ => ⟨t,ht,hd,he⟩⟩
    · exact ⟨[],fun hh => (hn hh).elim⟩
  choose clauses hc using hc
  let entries := σ.types.map fun entry => (entry.1,clauses entry.1)
  have hentry : ∀entry∈entries, ∃t,
      ComparisonSelectedBases.reifyClosedImage first p solved world σ.mode (.flex entry.1) entry.2=some t ∧
      t.DefinedUnder p.assumptions ∧ Equiv p.assumptions t (σ.closeTypeModes.type (.flex entry.1)) := by
    intro entry he
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp he
    exact hc old.1 (List.mem_map.mpr ⟨old,ho,rfl⟩)
  obtain ⟨types,ht⟩ := reifyEntries_complete (first:=first) (p:=p) (solved:=solved)
    (world:=world) (modes:=σ.mode) (fun entry he => (hentry entry he).imp fun t ht => ht.1)
  let τ : CompareSubstitution := ⟨types,σ.modes⟩
  have hrun : ComparisonSelectedBases.reifyAction first p solved world σ.modes entries=some τ := by
    change (reifyEntries first p solved world σ.mode entries).bind _=some τ
    rw [ht]
    rfl
  have hk : entries.map Prod.fst=σ.types.map Prod.fst := by
    simp [entries,List.map_map,Function.comp_def]
  refine ⟨entries,τ,hrun,hk,(reifyAction_spec hrun).2.1.trans hk,rfl,?_⟩
  apply reifyAction_replacement hrun hk (hw.closeTypeModes hi)
  intro entry he t hrt
  obtain ⟨u,hu,hd,heq⟩ := hentry entry he
  cases Option.some.inj (hrt.symm.trans hu)
  exact ⟨hd,heq⟩

end ModalityInference.ComparisonSelectedBases
