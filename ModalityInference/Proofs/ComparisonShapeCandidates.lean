import ModalityInference.ComparisonShapeCandidates
import ModalityInference.Proofs.ComparisonShapeSolver

namespace ModalityInference.ComparisonShape

@[simp] theorem mem_subshapes_self (s : ComparisonShape) : s ∈ s.subshapes := by
  cases s <;> simp [subshapes]

theorem sub_left_mem_declaredTemplates {Δ : Bounds} {a b : Ty}
    (h : Constraint.sub a b ∈ Δ) : ofTy a ∈ declaredTemplates Δ := by
  exact List.mem_flatMap.mpr ⟨(ofTy a, ofTy b),
    List.mem_flatMap.mpr ⟨.sub a b, h, by simp⟩, by simp⟩

theorem sub_right_mem_declaredTemplates {Δ : Bounds} {a b : Ty}
    (h : Constraint.sub a b ∈ Δ) : ofTy b ∈ declaredTemplates Δ := by
  exact List.mem_flatMap.mpr ⟨(ofTy a, ofTy b),
    List.mem_flatMap.mpr ⟨.sub a b, h, by simp⟩, by simp⟩

/-- Matching a template against a fixed shape locates each substituted variable
at a subtree of that shape. -/
theorem subst_var_mem_subshapes (s : ComparisonShape) (ρ : TypeVar → ComparisonShape)
    {v : TypeVar} (hv : v ∈ s.vars) : ρ v ∈ (s.subst ρ).subshapes := by
  induction s with
  | var w =>
    have he : v = w := by simpa [vars] using hv
    simp [subst, he]
  | unit | credit => simp [vars] at hv
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [vars, List.mem_append] at hv
    exact List.mem_cons_of_mem _ (List.mem_append.mpr (hv.imp iha ihb))

theorem matching_var_mem_subshapes {s anchor : ComparisonShape}
    {ρ : TypeVar → ComparisonShape} {v : TypeVar}
    (hv : v ∈ s.vars) (h : s.subst ρ = anchor) : ρ v ∈ anchor.subshapes :=
  h ▸ subst_var_mem_subshapes s ρ hv

@[simp] theorem unit_mem_candidates (names : List TypeVar)
    (fixed : TypeVar → ComparisonShape) (templates : List ComparisonShape) :
    .unit ∈ candidates names fixed templates := List.mem_cons_self

theorem fixed_subshape_mem_candidates {names : List TypeVar}
    {fixed : TypeVar → ComparisonShape} {templates : List ComparisonShape}
    {v : TypeVar} (hv : v ∈ names) {s : ComparisonShape}
    (hs : s ∈ (fixed v).subshapes) : s ∈ candidates names fixed templates := by
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
    ⟨fixed v, List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩), hs⟩)

theorem template_subshape_mem_candidates {names : List TypeVar}
    {fixed : TypeVar → ComparisonShape} {templates : List ComparisonShape}
    {t : ComparisonShape} (ht : t ∈ templates) {s : ComparisonShape}
    (hs : s ∈ (t.subst fixed).subshapes) : s ∈ candidates names fixed templates := by
  exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
    ⟨t.subst fixed, List.mem_append_right _ (List.mem_map.mpr ⟨t, ht, rfl⟩), hs⟩)

theorem matching_fixed_candidate {names : List TypeVar}
    {fixed ρ : TypeVar → ComparisonShape} {templates : List ComparisonShape}
    {s : ComparisonShape} {v w : TypeVar} (hv : v ∈ s.vars) (hw : w ∈ names)
    (h : s.subst ρ = fixed w) : ρ v ∈ candidates names fixed templates :=
  fixed_subshape_mem_candidates hw (matching_var_mem_subshapes hv h)

theorem matching_template_candidate {names : List TypeVar}
    {fixed ρ : TypeVar → ComparisonShape} {templates : List ComparisonShape}
    {s t : ComparisonShape} {v : TypeVar} (hv : v ∈ s.vars) (ht : t ∈ templates)
    (h : s.subst ρ = t.subst fixed) : ρ v ∈ candidates names fixed templates :=
  template_subshape_mem_candidates ht (matching_var_mem_subshapes hv h)

/-- A template containing an unselected choice cannot match a fixed name. -/
theorem unselected_ne_fixed {names : List TypeVar}
    {fixed ρ : TypeVar → ComparisonShape} {templates : List ComparisonShape}
    {s : ComparisonShape} {v w : TypeVar}
    (hv : v ∈ s.vars) (hw : w ∈ names)
    (hn : ρ v ∉ candidates names fixed templates) : s.subst ρ ≠ fixed w :=
  fun h => hn (matching_fixed_candidate hv hw h)

/-- A template containing an unselected choice cannot match a declared endpoint. -/
theorem unselected_ne_template {names : List TypeVar}
    {fixed ρ : TypeVar → ComparisonShape} {templates : List ComparisonShape}
    {s t : ComparisonShape} {v : TypeVar}
    (hv : v ∈ s.vars) (ht : t ∈ templates)
    (hn : ρ v ∉ candidates names fixed templates) : s.subst ρ ≠ t.subst fixed :=
  fun h => hn (matching_template_candidate hv ht h)

theorem select_mem_candidates (names : List TypeVar) (fixed : TypeVar → ComparisonShape)
    (templates : List ComparisonShape) (ρ : TypeVar → ComparisonShape) (v : TypeVar) :
    select names fixed templates ρ v ∈ candidates names fixed templates := by
  simp only [select]
  split <;> simp_all

theorem select_of_mem {names : List TypeVar} {fixed ρ : TypeVar → ComparisonShape}
    {templates : List ComparisonShape} {v : TypeVar}
    (hv : ρ v ∈ candidates names fixed templates) :
    select names fixed templates ρ v = ρ v := by
  simp [select, hv]

/-- Selection leaves every template matching a fixed name unchanged. -/
theorem select_preserves_fixed {names : List TypeVar}
    {fixed ρ : TypeVar → ComparisonShape} {templates : List ComparisonShape}
    {s : ComparisonShape} {w : TypeVar} (hw : w ∈ names)
    (h : s.subst ρ = fixed w) :
    s.subst (select names fixed templates ρ) = fixed w := by
  exact (ComparisonShapeSolver.subst_congr s
    (fun _ hv => select_of_mem (matching_fixed_candidate hv hw h))).trans h

/-- The same simultaneous selection preserves every declared template match. -/
theorem select_preserves_template {names : List TypeVar}
    {fixed ρ : TypeVar → ComparisonShape} {templates : List ComparisonShape}
    {s t : ComparisonShape} (ht : t ∈ templates) (h : s.subst ρ = t.subst fixed) :
    s.subst (select names fixed templates ρ) = t.subst fixed := by
  exact (ComparisonShapeSolver.subst_congr s
    (fun _ hv => select_of_mem (matching_template_candidate hv ht h))).trans h

/-- Fixed assignments have finite support. Outside their keys the action is a
variable, so only finitely many names can anchor a constructor root. -/
theorem unselected_ne_action {assignment : ComparisonShapeSolver.Assignment}
    {names : List TypeVar} {ρ : TypeVar → ComparisonShape}
    {templates : List ComparisonShape} {s : ComparisonShape} {v : TypeVar}
    (hkeys : ∀ entry ∈ assignment, entry.1 ∈ names)
    (hv : v ∈ s.vars)
    (hn : ρ v ∉ candidates names (ComparisonShapeSolver.action assignment) templates)
    (hroot : ∀ w, s.subst ρ ≠ .var w) :
    ∀ w, ComparisonShapeSolver.action assignment w ≠ s.subst ρ := by
  intro w he
  cases hl : assignment.lookup w with
  | none => exact hroot w (by simpa [ComparisonShapeSolver.action, hl] using he.symm)
  | some a =>
    obtain ⟨left, right, hx, _⟩ := List.lookup_eq_some_iff.mp hl
    have hw : w ∈ names := hkeys (w, a) (by simp [hx])
    exact (unselected_ne_fixed hv hw hn) he.symm

end ModalityInference.ComparisonShape
