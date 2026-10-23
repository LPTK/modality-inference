import ModalityInference.Proofs.ComparisonRelativeSyntax

/-! Reflection at finitely many raw syntax calls follows from local orbit
edges and recorded table rows. The checks retain literal partial prefixes. -/
namespace ModalityInference.ComparisonRelativeSyntax

open ComparisonRelativeCoordinates ComparisonRawCarrierSuffix

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Model

variable {Δ : Bounds} {M A O : Type*} [PartialOrder M] [CommMonoid M]
  {embed : A → O → Bool} (S : Model Δ M A O embed)

theorem frozenValue_recorded {a : CompareTy} {v : Coordinates M (O → Bool)}
    (hm : (a,v) ∈ S.frozen)
    (hu : ∀ row ∈ S.frozen, row.1 = a → row.2 = v) : S.frozenValue a = v := by
  cases hf : S.frozen.find? (fun row => decide (row.1 = a)) with
  | none =>
    have hh := List.find?_eq_none.mp hf (a,v) hm
    exact (hh (by simp)).elim
  | some row =>
    have hr := List.mem_of_find?_eq_some hf
    have he : row.1 = a := of_decide_eq_true
      (List.find?_some (p := fun row : CompareTy × Coordinates M (O → Bool) =>
        decide (row.1 = a)) hf)
    simpa only [frozenValue,hf,Option.map_some,Option.getD_some] using hu row hr he

end Model

abbrev RawSite := Ty × Option ModExpr

private theorem ofTy_eq_iff (a b : Ty) : CompareTy.ofTy a = CompareTy.ofTy b ↔ a = b := by
  induction a generalizing b <;> cases b <;> simp_all [CompareTy.ofTy]

def rawFrozen {V : Type*} (sites : List RawSite) (value : RawSite → V) : List (CompareTy × V) :=
  sites.filterMap fun site => site.2.map fun p => (.modal (.ofTy site.1) p,value site)

theorem rawFrozen_recorded {V : Type*} (sites : List RawSite) (value : RawSite → V)
    {a : Ty} {p : ModExpr} (hs : (a,some p) ∈ sites) :
    (.modal (.ofTy a) p,value (a,some p)) ∈ rawFrozen sites value ∧
      ∀ row ∈ rawFrozen sites value, row.1 = .modal (.ofTy a) p → row.2 = value (a,some p) := by
  constructor
  · exact List.mem_filterMap.mpr ⟨(a,some p),hs,rfl⟩
  · intro row hr he
    obtain ⟨⟨b,q⟩,_,hq⟩ := List.mem_filterMap.mp hr
    cases q with
    | none => cases hq
    | some q =>
      have hrow : (.modal (.ofTy b) q,value (b,some q)) = row := Option.some.inj hq
      rw [← hrow] at he ⊢
      have hab : b = a := (ofTy_eq_iff _ _).mp (CompareTy.modal.inj he).1
      have hpq : q = p := (CompareTy.modal.inj he).2
      cases hab; cases hpq
      rfl

variable {Δ : Bounds} {M A O : Type*} [PartialOrder M] [CommMonoid M]
  {embed : A → O → Bool}

/-- All obligations are local to one of the listed calls. Constructor rows
quantify over the finite control type when instantiated in a finite model. -/
structure RawCoverage (S : Model Δ M A O embed)
    (act : M → A → A) (hindex : ∀ a, Monotone (fun m => embed (act m a)))
    (sites : List RawSite) (tag : RawSite → A) : Prop where
  unit : ∀ a, embed (act 1 a) = embed a
  atom : ∀ v, (.var v,none) ∈ sites → S.atom v = orbit embed act hindex (tag (.var v,none))
  unitValue : (.unit,none) ∈ sites → S.unit = orbit embed act hindex (tag (.unit,none))
  credit : (.credit,none) ∈ sites → S.credit = orbit embed act hindex (tag (.credit,none))
  frozen : ∀ a p, (a,some p) ∈ sites →
    (∃ v, a = .var v) ∨ a = .unit ∨ a = .credit ∨ (∃ b c, a = .fn b c) →
    (.modal (.ofTy a) p,orbit embed act hindex (tag (a,some p))) ∈ S.frozen ∧
      ∀ row ∈ S.frozen, row.1 = .modal (.ofTy a) p →
        row.2 = orbit embed act hindex (tag (a,some p))
  modal : ∀ a m, (.modal a m,none) ∈ sites →
    (a,(normalize Δ m).literal) ∈ sites ∧
      shift S.mul_mono (S.controls.toFun (normalize Δ m).control (control_total Δ m))
        (orbit embed act hindex (tag (a,(normalize Δ m).literal))) =
          orbit embed act hindex (tag (.modal a m,none))
  prefixed_modal : ∀ a m p, (.modal a m,some p) ∈ sites →
    (a,some (.compose m p)) ∈ sites ∧
      orbit embed act hindex (tag (a,some (.compose m p))) =
        orbit embed act hindex (tag (.modal a m,some p))
  prod : ∀ a b p, (.prod a b,p) ∈ sites →
    (a,p) ∈ sites ∧ (b,p) ∈ sites ∧ ∀ m,
      ((S.prodTable p).table m).entry (act m (tag (a,p))) (act m (tag (b,p)))
        (act m (tag (.prod a b,p)))
  sum : ∀ a b p, (.sum a b,p) ∈ sites →
    (a,p) ∈ sites ∧ (b,p) ∈ sites ∧ ∀ m,
      ((S.sumTable p).table m).entry (act m (tag (a,p))) (act m (tag (b,p)))
        (act m (tag (.sum a b,p)))
  fn : ∀ a b, (.fn a b,none) ∈ sites →
    (a,none) ∈ sites ∧ (b,none) ∈ sites ∧ ∀ m,
      (S.fnTable.table m).entry (tag (a,none)) (tag (b,none))
        (act m (tag (.fn a b,none)))

namespace RawCoverage

variable {S : Model Δ M A O embed} {act : M → A → A}
  {hindex : ∀ a, Monotone (fun m => embed (act m a))}
  {sites : List RawSite} {tag : RawSite → A}
  (h : RawCoverage S act hindex sites tag)

include h

theorem denote {a : Ty} {p : Option ModExpr} (hs : (a,p) ∈ sites) :
    S.denote (.ofTy a) p = orbit embed act hindex (tag (a,p)) := by
  induction a generalizing p with
  | prod a b iha ihb =>
    obtain ⟨ha,hb,hrow⟩ := h.prod a b p hs
    change pair (S.prodTable p) (S.prod_order p) (S.denote (.ofTy a) p)
      (S.denote (.ofTy b) p) = _
    rw [iha ha,ihb hb]
    exact pair_recorded (S.prodTable p) (S.prod_order p)
      (fun m => act m (tag (a,p))) (fun m => act m (tag (b,p)))
      (fun m => act m (tag (.prod a b,p))) (hindex _) (hindex _) (hindex _) hrow
  | sum a b iha ihb =>
    obtain ⟨ha,hb,hrow⟩ := h.sum a b p hs
    change pair (S.sumTable p) (S.sum_order p) (S.denote (.ofTy a) p)
      (S.denote (.ofTy b) p) = _
    rw [iha ha,ihb hb]
    exact pair_recorded (S.sumTable p) (S.sum_order p)
      (fun m => act m (tag (a,p))) (fun m => act m (tag (b,p)))
      (fun m => act m (tag (.sum a b,p))) (hindex _) (hindex _) (hindex _) hrow
  | fn a b iha ihb =>
    cases p with
    | none =>
      obtain ⟨ha,hb,hrow⟩ := h.fn a b hs
      change ComparisonRelativeCoordinates.fn S.fnTable S.fn_order (S.denote (.ofTy a) none)
        (S.denote (.ofTy b) none) = _
      rw [iha ha,ihb hb]
      exact fn_recorded S.fnTable S.fn_order
        (fun m => act m (tag (.fn a b,none))) (hindex _) (h.unit _) (h.unit _) hrow
    | some p =>
      obtain ⟨hm,hu⟩ := h.frozen (.fn a b) p hs (Or.inr (Or.inr (Or.inr ⟨a,b,rfl⟩)))
      exact S.frozenValue_recorded hm hu
  | modal a m ih =>
    cases p with
    | none =>
      obtain ⟨ha,he⟩ := h.modal a m hs
      change shift S.mul_mono (S.controls.toFun (normalize Δ m).control (control_total Δ m))
        (S.denote (.ofTy a) (normalize Δ m).literal) = _
      rw [ih ha]
      exact he
    | some p =>
      obtain ⟨ha,he⟩ := h.prefixed_modal a m p hs
      exact (ih ha).trans he
  | var v =>
    cases p with
    | none => exact h.atom v hs
    | some p =>
      obtain ⟨hm,hu⟩ := h.frozen (.var v) p hs (Or.inl ⟨v,rfl⟩)
      exact S.frozenValue_recorded hm hu
  | unit =>
    cases p with
    | none => exact h.unitValue hs
    | some p =>
      obtain ⟨hm,hu⟩ := h.frozen .unit p hs (Or.inr (Or.inl rfl))
      exact S.frozenValue_recorded hm hu
  | credit =>
    cases p with
    | none => exact h.credit hs
    | some p =>
      obtain ⟨hm,hu⟩ := h.frozen .credit p hs (Or.inr (Or.inr (Or.inl rfl)))
      exact S.frozenValue_recorded hm hu

theorem reflect {a b : Ty} (ha : (a,none) ∈ sites) (hb : (b,none) ∈ sites)
    (hab : S.Related (.ofTy a) (.ofTy b)) : embed (tag (a,none)) ≤ embed (tag (b,none)) := by
  change S.denote (.ofTy a) none ≤ S.denote (.ofTy b) none at hab
  rw [h.denote ha,h.denote hb] at hab
  have hh := hab 1
  change embed (act 1 (tag (a,none))) ≤ embed (act 1 (tag (b,none))) at hh
  simpa only [h.unit] using hh

theorem related_iff
    (htransport : ∀ m a b, embed a ≤ embed b → embed (act m a) ≤ embed (act m b))
    {a b : Ty} (ha : (a,none) ∈ sites) (hb : (b,none) ∈ sites) :
    S.Related (.ofTy a) (.ofTy b) ↔ embed (tag (a,none)) ≤ embed (tag (b,none)) := by
  change S.denote (.ofTy a) none ≤ S.denote (.ofTy b) none ↔ _
  rw [h.denote ha,h.denote hb]
  exact orbit_le_iff embed act hindex h.unit htransport _ _

end RawCoverage

end
end ModalityInference.ComparisonRelativeSyntax
