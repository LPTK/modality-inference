import ModalityInference.Proofs.ComparisonRawHeadFiniteOrbits
import ModalityInference.Proofs.ComparisonRawCarrierSuffix

/-! A finite raw boundary records the calls made by the coordinate interpreter.
Inherited partial prefixes are recorded at products and sums; functions under
such a prefix are frozen. No inverse parsing of arbitrary modal labels is needed. -/
namespace ModalityInference.ComparisonRawHeadTrace

open ComparisonRawHeadFiniteOrbits ComparisonRawCarrierSuffix

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Site := Ty × Option ModExpr

def applyPrefix : Option ModExpr → Ty → Ty
  | none, a => a
  | some p, a => .modal a p

def calls (Δ : Bounds) : Ty → Option ModExpr → List Site
  | a, p => (a,p) :: match a,p with
    | .modal a m, none => calls Δ a (normalize Δ m).literal
    | .modal a m, some p => calls Δ a (some (.compose m p))
    | .prod a b, p | .sum a b, p => calls Δ a p ++ calls Δ b p
    | .fn a b, none => calls Δ a none ++ calls Δ b none
    | _, _ => []

theorem root_mem (Δ : Bounds) (a : Ty) (p : Option ModExpr) : (a,p) ∈ calls Δ a p :=
  by cases a <;> cases p <;> exact List.mem_cons_self

theorem modal_none_subset (Δ : Bounds) (a : Ty) (m : ModExpr) :
    calls Δ a (normalize Δ m).literal ⊆ calls Δ (.modal a m) none :=
  fun _ h => List.mem_cons_of_mem _ h

theorem modal_some_subset (Δ : Bounds) (a : Ty) (m p : ModExpr) :
    calls Δ a (some (.compose m p)) ⊆ calls Δ (.modal a m) (some p) :=
  fun _ h => List.mem_cons_of_mem _ h

theorem prod_subsets (Δ : Bounds) (a b : Ty) (p : Option ModExpr) :
    calls Δ a p ⊆ calls Δ (.prod a b) p ∧ calls Δ b p ⊆ calls Δ (.prod a b) p :=
  ⟨fun _ h => List.mem_cons_of_mem _ (List.mem_append_left _ h),
   fun _ h => List.mem_cons_of_mem _ (List.mem_append_right _ h)⟩

theorem sum_subsets (Δ : Bounds) (a b : Ty) (p : Option ModExpr) :
    calls Δ a p ⊆ calls Δ (.sum a b) p ∧ calls Δ b p ⊆ calls Δ (.sum a b) p :=
  ⟨fun _ h => List.mem_cons_of_mem _ (List.mem_append_left _ h),
   fun _ h => List.mem_cons_of_mem _ (List.mem_append_right _ h)⟩

theorem fn_subsets (Δ : Bounds) (a b : Ty) :
    calls Δ a none ⊆ calls Δ (.fn a b) none ∧ calls Δ b none ⊆ calls Δ (.fn a b) none :=
  ⟨fun _ h => List.mem_cons_of_mem _ (List.mem_append_left _ h),
   fun _ h => List.mem_cons_of_mem _ (List.mem_append_right _ h)⟩

theorem calls_closed {Δ : Bounds} {a : Ty} {p : Option ModExpr} {s : Site}
    (hs : s ∈ calls Δ a p) : calls Δ s.1 s.2 ⊆ calls Δ a p := by
  induction a generalizing p s <;> cases p <;> simp only [calls,List.mem_cons,List.mem_append] at hs
  all_goals rcases hs with rfl | hs
  all_goals try exact List.Subset.refl _
  all_goals try exact (List.not_mem_nil hs).elim
  case prod.none a b iha ihb =>
    rcases hs with ha | hb
    · exact (iha ha).trans (prod_subsets Δ a b none).1
    · exact (ihb hb).trans (prod_subsets Δ a b none).2
  case prod.some a b iha ihb p =>
    rcases hs with ha | hb
    · exact (iha ha).trans (prod_subsets Δ a b (some p)).1
    · exact (ihb hb).trans (prod_subsets Δ a b (some p)).2
  case sum.none a b iha ihb =>
    rcases hs with ha | hb
    · exact (iha ha).trans (sum_subsets Δ a b none).1
    · exact (ihb hb).trans (sum_subsets Δ a b none).2
  case sum.some a b iha ihb p =>
    rcases hs with ha | hb
    · exact (iha ha).trans (sum_subsets Δ a b (some p)).1
    · exact (ihb hb).trans (sum_subsets Δ a b (some p)).2
  case fn.none a b iha ihb =>
    rcases hs with ha | hb
    · exact (iha ha).trans (fn_subsets Δ a b).1
    · exact (ihb hb).trans (fn_subsets Δ a b).2
  case modal.none a m ih => exact (ih hs).trans (modal_none_subset Δ a m)
  case modal.some a m ih p => exact (ih hs).trans (modal_some_subset Δ a m p)

def rawHeads (sites : List Site) : List Ty := sites.map fun s => applyPrefix s.2 s.1

def boundary (Δ : Bounds) (sites : List Site) : Boundary Δ := .ofRaw Δ (rawHeads sites)

def ofInputs (Δ : Bounds) (inputs : List Ty) : List Site :=
  inputs.flatMap fun a => calls Δ a none

theorem input_subset {Δ : Bounds} {inputs : List Ty} {a : Ty} (ha : a ∈ inputs) :
    calls Δ a none ⊆ ofInputs Δ inputs :=
  fun _ h => List.mem_flatMap.mpr ⟨a,ha,h⟩

theorem ofInputs_closed {Δ : Bounds} {inputs : List Ty} {s : Site}
    (hs : s ∈ ofInputs Δ inputs) : calls Δ s.1 s.2 ⊆ ofInputs Δ inputs := by
  obtain ⟨a,ha,hs⟩ := List.mem_flatMap.mp hs
  exact (calls_closed hs).trans (input_subset ha)

def prefixes (sites : List Site) : List ModExpr := sites.filterMap Prod.snd

theorem prefix_mem {sites : List Site} {a : Ty} {p : ModExpr}
    (h : (a,some p) ∈ sites) : p ∈ prefixes sites :=
  List.mem_filterMap.mpr ⟨(a,some p),h,rfl⟩

def point (Δ : Bounds) (sites : List Site) (names : List ModVar) (i : Fin sites.length) :
    Point (boundary Δ sites) names :=
  ⟨⟨i.val,by simpa only [boundary,Boundary.ofRaw,rawHeads,List.length_map] using i.isLt⟩,1⟩

theorem point_equivalent (Δ : Bounds) (sites : List Site) (names : List ModVar)
    (i : Fin sites.length) :
    AlgebraSubtype Δ (point Δ sites names i).term (.ofTy (applyPrefix sites[i].2 sites[i].1)) ∧
      AlgebraSubtype Δ (.ofTy (applyPrefix sites[i].2 sites[i].1)) (point Δ sites names i).term := by
  simpa [boundary,Boundary.ofRaw,rawHeads,point,Point.base]
    using Point.base_equivalent (B := boundary Δ sites) (names := names)
      ⟨i.val,by simpa only [boundary,Boundary.ofRaw,rawHeads,List.length_map] using i.isLt⟩

def index {sites : List Site} {s : Site} (hs : s ∈ sites) : Fin sites.length :=
  (List.get_of_mem hs).choose

theorem index_value {sites : List Site} {s : Site} (hs : s ∈ sites) : sites[index hs] = s := by
  simpa only [List.get_eq_getElem] using (List.get_of_mem hs).choose_spec

def memberPoint (Δ : Bounds) {sites : List Site} (names : List ModVar) {s : Site}
    (hs : s ∈ sites) : Point (boundary Δ sites) names := point Δ sites names (index hs)

theorem memberPoint_equivalent (Δ : Bounds) {sites : List Site} (names : List ModVar) {s : Site}
    (hs : s ∈ sites) :
    AlgebraSubtype Δ (memberPoint Δ names hs).term (.ofTy (applyPrefix s.2 s.1)) ∧
      AlgebraSubtype Δ (.ofTy (applyPrefix s.2 s.1)) (memberPoint Δ names hs).term := by
  simpa only [memberPoint,index_value] using point_equivalent Δ sites names (index hs)

def tag {D : Type*} (fallback : D) (Δ : Bounds) (sites : List Site) (names : List ModVar)
    (s : Site) : D ⊕ Point (boundary Δ sites) names :=
  if hs : s ∈ sites then .inr (memberPoint Δ names hs) else .inl fallback

theorem tag_mem {D : Type*} (fallback : D) (Δ : Bounds) {sites : List Site}
    (names : List ModVar) {s : Site} (hs : s ∈ sites) :
    tag fallback Δ sites names s = .inr (memberPoint Δ names hs) := by simp only [tag,dif_pos hs]

theorem memberPoint_le_iff (Δ : Bounds) {sites : List Site} (names : List ModVar)
    {s t : Site} (hs : s ∈ sites) (ht : t ∈ sites) :
    memberPoint Δ names hs ≤ memberPoint Δ names ht ↔
      AlgebraSubtype Δ (.ofTy (applyPrefix s.2 s.1)) (.ofTy (applyPrefix t.2 t.1)) := by
  constructor
  · intro h
    exact (memberPoint_equivalent Δ names hs).2.trans
      (AlgebraSubtype.trans h (memberPoint_equivalent Δ names ht).1)
  · intro h
    exact (memberPoint_equivalent Δ names hs).1.trans
      (h.trans (memberPoint_equivalent Δ names ht).2)

def controlNames (Δ : Bounds) : Site → List ModVar
  | (.modal _ m,none) => (normalize Δ m).control.vars.toList
  | _ => []

def modeNames (Δ : Bounds) (sites : List Site) : List ModVar :=
  Δ.modVars.toList ++ (rawHeads sites).flatMap (fun a => a.modVars.toList) ++
    sites.flatMap (controlNames Δ)

theorem context_names (Δ : Bounds) (sites : List Site) : Δ.modVars ⊆ (modeNames Δ sites).toFinset := by
  intro v hv
  simp only [modeNames,List.mem_toFinset,List.mem_append,Finset.mem_toList]
  exact Or.inl (Or.inl hv)

theorem head_names {Δ : Bounds} {sites : List Site} {a : Ty} (ha : a ∈ rawHeads sites) :
    a.modVars ⊆ (modeNames Δ sites).toFinset := by
  intro v hv
  have hh : v ∈ (rawHeads sites).flatMap (fun a => a.modVars.toList) :=
    List.mem_flatMap.mpr ⟨a,ha,Finset.mem_toList.mpr hv⟩
  simp [modeNames,hh]

theorem control_names {Δ : Bounds} {sites : List Site} {a : Ty} {m : ModExpr}
    (ha : (.modal a m,none) ∈ sites) :
    (normalize Δ m).control.vars ⊆ (modeNames Δ sites).toFinset := by
  intro v hv
  have hh : v ∈ sites.flatMap (controlNames Δ) :=
    List.mem_flatMap.mpr ⟨(.modal a m,none),ha,Finset.mem_toList.mpr hv⟩
  simp [modeNames,hh]

@[simp] theorem ofTy_applyPrefix (p : Option ModExpr) (a : Ty) :
    CompareTy.ofTy (applyPrefix p a) = prefixApply p (.ofTy a) := by cases p <;> rfl

theorem modal_none_equivalent (Δ : Bounds) (a : Ty) (m : ModExpr) :
    AlgebraSubtype Δ (.ofTy (.modal a m))
      (.modal (.ofTy (applyPrefix (normalize Δ m).literal a)) (normalize Δ m).control) ∧
    AlgebraSubtype Δ (.modal (.ofTy (applyPrefix (normalize Δ m).literal a)) (normalize Δ m).control)
      (.ofTy (.modal a m)) := by
  simpa only [CompareTy.ofTy,ofTy_applyPrefix,Normalized.apply] using
    (normalize_algebra (Δ := Δ) (m := m) (CompareTy.wellShaped_ofTy a Δ))

theorem modal_some_equivalent (Δ : Bounds) (a : Ty) (m p : ModExpr) :
    AlgebraSubtype Δ (.ofTy (applyPrefix (some p) (.modal a m)))
      (.ofTy (applyPrefix (some (.compose m p)) a)) ∧
    AlgebraSubtype Δ (.ofTy (applyPrefix (some (.compose m p)) a))
      (.ofTy (applyPrefix (some p) (.modal a m))) :=
  ⟨.shaped (.compose (CompareTy.wellShaped_ofTy a Δ)),
   .shaped (.composeRev (CompareTy.wellShaped_ofTy a Δ))⟩

end
end ModalityInference.ComparisonRawHeadTrace
