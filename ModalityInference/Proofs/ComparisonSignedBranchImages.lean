import ModalityInference.ComparisonSignedBranchImages
import ModalityInference.Proofs.ComparisonSignedFamily
import ModalityInference.Proofs.ComparisonSelectedReification
import ModalityInference.Proofs.ComparisonInputAction

namespace ModalityInference.ComparisonSignedBranchImages
open ComparisonSelectedBases ComparisonPropagation ComparisonSignedPolynomials

theorem locate_spec {name : Nat} {shape : ComparisonShape} {table : List Entry} {key : Nat}
    (h : locate name shape table=some key) :
    ∃entry,table[key]?=some entry ∧ entry.1=name ∧ entry.2.shape=shape := by
  induction table generalizing key with
  | nil => simp [locate] at h
  | cons entry table ih =>
      simp only [locate] at h
      split at h
      · next he =>
        obtain rfl := Option.some.inj h
        have he' : entry.1=name ∧ entry.2.shape=shape := by simpa using he
        exact ⟨entry,rfl,he'.1,he'.2⟩
      · cases ht : locate name shape table <;> simp only [ht,Option.map_none,Option.map_some] at h
        · cases h
        · rename_i k
          obtain rfl := Option.some.inj h
          obtain ⟨e,he,hn,hs⟩ := ih ht
          exact ⟨e,by simpa using he,hn,hs⟩

theorem locate_complete {name : Nat} {shape : ComparisonShape} {table : List Entry}
    (h : ∃entry∈table,entry.1=name ∧ entry.2.shape=shape) :
    ∃key,locate name shape table=some key := by
  induction table with
  | nil => simp at h
  | cons entry table ih =>
      by_cases he : entry.1==name && entry.2.shape==shape
      · exact ⟨0,by simp [locate,he]⟩
      · obtain ⟨e,hm,hn,hs⟩ := h
        have ht : e∈table := (List.mem_cons.mp hm).resolve_left (by
          intro heq
          subst e
          simp [hn,hs] at he)
        obtain ⟨k,hk⟩ := ih ⟨e,ht,hn,hs⟩
        exact ⟨k+1,by simp [locate,he,hk]⟩

theorem locate_key {name : Nat} {shape : ComparisonShape} {table : List Entry} {key : Nat}
    (h : locate name shape table=some key) : key∈(input table).keys := by
  obtain ⟨entry,he,_,_⟩ := locate_spec h
  simpa only [input,List.mem_range] using List.getElem?_eq_some_iff.mp he |>.1

theorem mem_entries {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {entry : Entry} :
    entry∈entries first p solved ↔ entry.1∈inputTypeKeys p ∧
      entry.2∈prepared first p solved (.flex entry.1) := by
  obtain ⟨name,branch⟩ := entry
  simp [entries]

theorem entry_basis {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {entry : Entry}
    (h : entry∈entries first p solved) :
    ComparisonStructuralBasis.basis (inputNames p) (inputModes p) solved.fixedShapes
      entry.2.shape=some entry.2.basis := by
  obtain ⟨_,_,_,_,hb⟩ := bases_origin (mem_entries.mp h).2
  exact hb

theorem locate_basis {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {name key : Nat} {branch : Branch}
    (hb : branch∈prepared first p solved (.flex name))
    (hk : locate name branch.shape (entries first p solved)=some key) :
    (input (entries first p solved)).bases key=branch.basis.types := by
  obtain ⟨entry,he,hn,hs⟩ := locate_spec hk
  have he' : entry∈entries first p solved := List.mem_of_getElem? he
  have hentry := entry_basis he'
  obtain ⟨_,_,_,_,hbranch⟩ := bases_origin hb
  rw [hs,hbranch] at hentry
  have heq := Option.some.inj hentry
  simp [input,he,←heq]

theorem locate_prepared {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {name : Nat}
    (hn : name∈inputTypeKeys p) {branch : Branch}
    (hb : branch∈prepared first p solved (.flex name)) :
    ∃key,locate name branch.shape (entries first p solved)=some key :=
  locate_complete ⟨(name,branch),mem_entries.mpr ⟨hn,hb⟩,rfl,rfl⟩

theorem pick_spec {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {images : List (Nat × CompareTy)} {name : Nat} {t : CompareTy}
    (h : pick first p solved world images name=some t) :
    ∃branch key,enabled world (prepared first p solved (.flex name))=some branch ∧
      locate name branch.shape (entries first p solved)=some key ∧ images.lookup key=some t := by
  cases hb : enabled world (prepared first p solved (.flex name)) <;>
    simp [pick,hb] at h
  rename_i branch
  cases hk : locate name branch.shape (entries first p solved) <;> simp [hk] at h
  exact ⟨branch,_,rfl,hk,h⟩

private theorem lookup_mem {α : Type} {xs : List (Nat × α)} {key : Nat} {a : α}
    (h : xs.lookup key=some a) : (key,a)∈xs := by
  obtain ⟨left,right,rfl,_⟩ := List.lookup_eq_some_iff.mp h
  simp

private theorem lookup_complete {α : Type} {xs : List (Nat × α)} {key : Nat}
    (h : key∈xs.map Prod.fst) : ∃a,xs.lookup key=some a := by
  cases hl : xs.lookup key with
  | some a => exact ⟨a,rfl⟩
  | none =>
      obtain ⟨entry,he,hh⟩ := List.mem_map.mp h
      have hn := List.lookup_eq_none_iff.mp hl entry he
      simp [hh] at hn

theorem pick_complete {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {images : List (Nat × CompareTy)}
    (hi : images.map Prod.fst=(input (entries first p solved)).keys)
    {name : Nat} (hn : name∈inputTypeKeys p)
    (hb : ∃branch∈prepared first p solved (.flex name),branch.guard.eval world=true) :
    ∃t,pick first p solved world images name=some t := by
  obtain ⟨branch,hbranch⟩ := enabled_complete hb
  obtain ⟨key,hkey⟩ := locate_prepared hn (enabled_spec hbranch).1
  have hk : key∈images.map Prod.fst := hi ▸ locate_key hkey
  obtain ⟨t,ht⟩ := lookup_complete hk
  exact ⟨t,by simp [pick,hbranch,hkey,ht]⟩

/-- Selecting a branch retrieves the exact polynomial from the common graph;
reification uses the enabled branch's actual structural basis. -/
theorem pick_reifyImage {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat → Bool}
    {r : CNF} {images : List (Nat × CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {name : Nat} {t : CompareTy} (hp : pick first p solved world images name=some t) :
    ∃key,key∈(input (entries first p solved)).keys ∧
      reifyImage first p solved world (.flex name)
        (polynomial parameters ((input (entries first p solved)).key key)
          ((input (entries first p solved)).bases key).length
          ((input (entries first p solved)).assignment r))=some t := by
  obtain ⟨branch,key,hb,hk,hi⟩ := pick_spec hp
  have htypes := ((input (entries first p solved)).reconstruct_spec hr).2 _ (lookup_mem hi)
  have hbas := locate_basis (enabled_spec hb).1 hk
  refine ⟨key,locate_key hk,?_⟩
  simp only [ComparisonSignedPolynomials.reconstruct] at htypes
  rw [hbas] at htypes
  simpa only [reifyImage,hb,Option.bind_some,hbas] using htypes

private theorem mapM_pairs {α β : Type} (xs : List α) (f : α → Option β)
    {ys : List (α × β)} (h : xs.mapM (fun x=>do return (x,←f x))=some ys) :
    ys.map Prod.fst=xs ∧ ∀y∈ys,f y.1=some y.2 := by
  induction xs generalizing ys with
  | nil =>
      have he : ys=[] := by simpa using h.symm
      simp [he]
  | cons x xs ih =>
      simp only [List.mapM_cons,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
      obtain ⟨pair,⟨y,hy,rfl⟩,rest,hr,rfl⟩ := h
      obtain ⟨hkeys,hvalues⟩ := ih hr
      constructor
      · simp [hkeys]
      · intro z hz
        rcases List.mem_cons.mp hz with rfl|hz
        · exact hy
        · exact hvalues z hz

private theorem mapM_exists {α β : Type} (xs : List α) (f : α → Option β)
    (h : ∀x∈xs,∃y,f x=some y) : ∃ys,xs.mapM f=some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
      obtain ⟨y,hy⟩ := h x List.mem_cons_self
      obtain ⟨ys,hys⟩ := ih (fun a ha=>h a (List.mem_cons_of_mem _ ha))
      exact ⟨y::ys,by simp [hy,hys]⟩

theorem select_spec {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {images : List (Nat × CompareTy)} {modes : List (Nat × ModExpr)} {result : CompareSubstitution}
    (h : select first p solved world images modes=some result) :
    result.modes=modes ∧ result.types.map Prod.fst=inputTypeKeys p ∧
      ∀entry∈result.types,∃raw,pick first p solved world images entry.1=some raw ∧
        entry.2=raw.subst CompareTy.var ({modes:=modes} : CompareSubstitution).mode := by
  simp only [select,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
  obtain ⟨types,ht,rfl⟩ := h
  have hmap : (inputTypeKeys p).mapM (fun name=>do
      return (name,←(pick first p solved world images name).map
        (fun raw=>raw.subst CompareTy.var ({modes:=modes} : CompareSubstitution).mode)))=some types := by
    convert ht using 1
    congr 1
    funext name
    cases pick first p solved world images name <;> rfl
  obtain ⟨hkeys,hvalues⟩ := mapM_pairs _ _ hmap
  refine ⟨rfl,hkeys,?_⟩
  intro entry he
  have hh := hvalues entry he
  obtain ⟨raw,hr,heq⟩ := Option.map_eq_some_iff.mp hh
  exact ⟨raw,hr,heq.symm⟩

theorem select_complete {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool}
    {images : List (Nat × CompareTy)} (modes : List (Nat × ModExpr))
    (hi : images.map Prod.fst=(input (entries first p solved)).keys)
    (hb : ∀name∈inputTypeKeys p,∃branch∈prepared first p solved (.flex name),
      branch.guard.eval world=true) :
    ∃result,select first p solved world images modes=some result := by
  obtain ⟨types,ht⟩ := mapM_exists (inputTypeKeys p) (fun name=>do
    let raw ← pick first p solved world images name
    return (name,raw.subst CompareTy.var ({modes:=modes} : CompareSubstitution).mode)) (by
      intro name hn
      obtain ⟨raw,hr⟩ := pick_complete hi hn (hb name hn)
      exact ⟨(name,raw.subst CompareTy.var ({modes:=modes} : CompareSubstitution).mode),by simp [hr]⟩)
  simp only [bind,pure] at ht
  exact ⟨⟨types,modes⟩,by simp only [select,bind,pure,ht,Option.bind_some]⟩

theorem select_defined {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat → Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : (layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat × CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat × ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes} : CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result) :
    ∀entry∈result.types,entry.2.DefinedUnder p.assumptions := by
  intro entry he
  obtain ⟨raw,hraw,heq⟩ := (select_spec h).2.2 entry he
  rw [heq]
  obtain ⟨key,_,ht⟩ := pick_reifyImage hr hraw
  have hn : entry.1∈inputTypeKeys p := (select_spec h).2.1 ▸ List.mem_map.mpr ⟨entry,he,rfl⟩
  have hv := (mem_inputTypeKeys p entry.1).mp hn |>.1
  exact hm.type_defined (reifyImage_representable hs hw hv ht).2.1

end ModalityInference.ComparisonSignedBranchImages
