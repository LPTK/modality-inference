import ModalityInference.Proofs.ComparisonRawCarrierHeterogeneous

/-! A restriction that records whole partial constructor heads. Unlike capsule
support, it does not close the carrier under arbitrary constructor applications.
Joins, meets, and total outer actions remain available. -/
namespace ModalityInference.ComparisonRawHeadRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Total outer actions are transparent; an undefined action freezes its exact
payload. A partial constructor without an outer action is retained as a whole. -/
def heads (Δ : Bounds) : CompareTy → Set CompareTy
  | .modal a (.compose m n) => heads Δ (.modal (.modal a m) n)
  | .modal a m => if Entails Δ (.defined m) then heads Δ a else {.modal a m}
  | .join a b | .meet a b => heads Δ a ∪ heads Δ b
  | a => if a.DefinedUnder Δ then ∅ else {a}
termination_by a => ComparisonPartialCapsule.size a
decreasing_by
  all_goals simp_wf
  all_goals simp only [ComparisonPartialCapsule.size, ComparisonPartialModes.expressionSize]
  all_goals first | omega | have := ComparisonPartialCapsule.mode_size_pos m; omega

def Carrier (Δ : Bounds) (H : Set CompareTy) (a : CompareTy) : Prop := heads Δ a ⊆ H

theorem heads_modal_total {Δ : Bounds} {m : ModExpr} (hm : Entails Δ (.defined m))
    (a : CompareTy) : heads Δ (.modal a m) = heads Δ a := by
  induction m generalizing a with
  | compose m n ihm ihn =>
    rw [heads, ihn (Entails.defined_compose_iff.mp hm).2,
      ihm (Entails.defined_compose_iff.mp hm).1]
  | _ => simp only [heads, if_pos hm]

theorem heads_compose (Δ : Bounds) (a : CompareTy) (m n : ModExpr) :
    heads Δ (.modal a (.compose m n)) = heads Δ (.modal (.modal a m) n) := by
  rw [heads]

@[simp] theorem carrier_join {Δ H a b} :
    Carrier Δ H (.join a b) ↔ Carrier Δ H a ∧ Carrier Δ H b := by
  simp only [Carrier, heads, Set.union_subset_iff]

@[simp] theorem carrier_meet {Δ H a b} :
    Carrier Δ H (.meet a b) ↔ Carrier Δ H a ∧ Carrier Δ H b := by
  simp only [Carrier, heads, Set.union_subset_iff]

theorem carrier_modal_total {Δ H a m} (hm : Entails Δ (.defined m)) :
    Carrier Δ H (.modal a m) ↔ Carrier Δ H a := by
  simp only [Carrier, heads_modal_total hm]

theorem carrier_compose {Δ H a m n} :
    Carrier Δ H (.modal a (.compose m n)) ↔ Carrier Δ H (.modal (.modal a m) n) := by
  simp only [Carrier, heads_compose]

theorem heads_defined {Δ : Bounds} {a : CompareTy} (h : a.DefinedUnder Δ) :
    heads Δ a = ∅ := by
  induction a with
  | modal a m ih =>
    rw [heads_modal_total (CompareTy.definedUnder_modal_iff.mp h).2,
      ih (CompareTy.definedUnder_modal_iff.mp h).1]
  | join a b ia ib | meet a b ia ib =>
    simp only [heads, ia (CompareTy.definedUnder_fn_iff.mp h).1,
      ib (CompareTy.definedUnder_fn_iff.mp h).2, Set.empty_union]
  | _ => simp only [heads, if_pos h]

theorem carrier_defined {Δ H a} (h : CompareTy.DefinedUnder a Δ) : Carrier Δ H a := by
  simp only [Carrier, heads_defined h, Set.empty_subset]

theorem carrier_prod_partial {Δ H a b} (h : ¬CompareTy.DefinedUnder (.prod a b) Δ) :
    Carrier Δ H (.prod a b) ↔ (.prod a b : CompareTy) ∈ H := by
  simp only [Carrier, heads, if_neg h, Set.singleton_subset_iff]

theorem carrier_sum_partial {Δ H a b} (h : ¬CompareTy.DefinedUnder (.sum a b) Δ) :
    Carrier Δ H (.sum a b) ↔ (.sum a b : CompareTy) ∈ H := by
  simp only [Carrier, heads, if_neg h, Set.singleton_subset_iff]

theorem carrier_fn_partial {Δ H a b} (h : ¬CompareTy.DefinedUnder (.fn a b) Δ) :
    Carrier Δ H (.fn a b) ↔ (.fn a b : CompareTy) ∈ H := by
  simp only [Carrier, heads, if_neg h, Set.singleton_subset_iff]

theorem heads_finite (Δ : Bounds) (a : CompareTy) : (heads Δ a).Finite := by
  fun_induction heads Δ a with
  | case1 _ _ _ ih | case2 _ _ _ _ ih => exact ih
  | case3 | case7 => exact Set.finite_singleton _
  | case4 _ _ ha hb | case5 _ _ ha hb => exact ha.union hb
  | case6 => exact Set.finite_empty

abbrev Atomic := ComparisonRawModalRestriction.Atomic

/-- Every recursive endpoint belongs to the selected whole-head carrier.
Constructor rules explicitly check their outputs; arbitrary constructor
applications are not silently added to the carrier. -/
inductive Derivation (Δ : Bounds) (H : Set CompareTy) : CompareTy → CompareTy → Prop where
  | atom {a b} : Carrier Δ H a → Carrier Δ H b → Atomic Δ a b → Derivation Δ H a b
  | trans {a b c} : Derivation Δ H a b → Derivation Δ H b c → Derivation Δ H a c
  | congr {a b m n} : Derivation Δ H a b → Submode Δ m n →
      Derivation Δ H (.modal a m) (.modal b n)
  | prod {a b c d m} : Carrier Δ H (.modal (.prod a b) m) →
      Carrier Δ H (.modal (.prod c d) m) →
      Derivation Δ H (.modal a m) (.modal c m) →
      Derivation Δ H (.modal b m) (.modal d m) →
      Derivation Δ H (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : Carrier Δ H (.modal (.sum a b) m) →
      Carrier Δ H (.modal (.sum c d) m) →
      Derivation Δ H (.modal a m) (.modal c m) →
      Derivation Δ H (.modal b m) (.modal d m) →
      Derivation Δ H (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : Carrier Δ H (.modal (.fn a b) m) →
      Carrier Δ H (.modal (.fn c d) n) →
      Derivation Δ H c a → Derivation Δ H b d → Submode Δ m (.compose n .top) →
      Derivation Δ H (.modal (.fn a b) m) (.modal (.fn c d) n)
  | joinLeast {a b c} : Derivation Δ H a c → Derivation Δ H b c →
      Derivation Δ H (.join a b) c
  | meetGreatest {a b c} : Derivation Δ H a b → Derivation Δ H a c →
      Derivation Δ H a (.meet b c)
  | clamp {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → ComparisonAlgebra.DefinedMode Δ m →
      Derivation Δ H b a → Derivation Δ H a t →
      Derivation Δ H (.modal a m) (.meet (.join a (.modal b m)) (.modal t m))
  | clampRev {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → ComparisonAlgebra.DefinedMode Δ m →
      Derivation Δ H b a → Derivation Δ H a t →
      Derivation Δ H (.meet (.join a (.modal b m)) (.modal t m)) (.modal a m)

theorem Derivation.algebra {Δ H a b} (h : Derivation Δ H a b) : AlgebraSubtype Δ a b := by
  induction h with
  | atom _ _ h => exact h.subtype
  | trans _ _ iha ihb => exact .trans iha ihb
  | congr _ hm ih => exact .congr ih hm
  | prod _ _ _ _ iha ihb => exact .prod iha ihb
  | sum _ _ _ _ iha ihb => exact .sum iha ihb
  | fn _ _ _ _ hm iha ihb => exact .fn iha ihb hm
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb
  | clamp hab hat hm _ _ ihb iht => exact .clamp hab hat hm ihb iht
  | clampRev hab hat hm _ _ ihb iht => exact .clampRev hab hat hm ihb iht

theorem Derivation.carriers {Δ H a b} (h : Derivation Δ H a b) :
    Carrier Δ H a ∧ Carrier Δ H b := by
  induction h with
  | atom ha hb _ => exact ⟨ha, hb⟩
  | trans _ _ ha hb => exact ⟨ha.1, hb.2⟩
  | congr _ hm ih => exact ⟨(carrier_modal_total hm.defined.1).mpr ih.1,
      (carrier_modal_total hm.defined.2).mpr ih.2⟩
  | prod ha hb _ _ _ _ | sum ha hb _ _ _ _ | fn ha hb _ _ _ _ _ => exact ⟨ha, hb⟩
  | joinLeast _ _ ha hb => exact ⟨carrier_join.mpr ⟨ha.1, hb.1⟩, ha.2⟩
  | meetGreatest _ _ ha hb => exact ⟨ha.1, carrier_meet.mpr ⟨ha.2, hb.2⟩⟩
  | clamp hab hat hm _ _ hb ht =>
      exact ⟨(carrier_modal_total hm).mpr hb.2,
        carrier_meet.mpr ⟨carrier_join.mpr ⟨hb.2, (carrier_modal_total hm).mpr hb.1⟩,
          (carrier_modal_total hm).mpr ht.2⟩⟩
  | clampRev hab hat hm _ _ hb ht =>
      exact ⟨carrier_meet.mpr ⟨carrier_join.mpr ⟨hb.2, (carrier_modal_total hm).mpr hb.1⟩,
          (carrier_modal_total hm).mpr ht.2⟩, (carrier_modal_total hm).mpr hb.2⟩

theorem Derivation.shaped {Δ H a b} (h : Derivation Δ H a b) :
    a.WellShaped Δ ∧ b.WellShaped Δ := ⟨h.algebra.wellShaped_left, h.algebra.wellShaped_right⟩

def core (Δ : Bounds) (H : Set CompareTy) : ComparisonRawCarrierIdeals.Core Δ where
  carrier := Carrier Δ H
  le := Derivation Δ H
  sound := Derivation.algebra
  left h := h.carriers.1
  right h := h.carriers.2
  refl ha hs := .atom ha ha (.refl hs)
  trans := .trans
  join_closed ha hb := carrier_join.mpr ⟨ha, hb⟩
  meet_closed ha hb := carrier_meet.mpr ⟨ha, hb⟩
  joinLeft ha hb hs := .atom ha (carrier_join.mpr ⟨ha, hb⟩) (.joinLeft hs)
  joinRight ha hb hs := .atom hb (carrier_join.mpr ⟨ha, hb⟩) (.joinRight hs)
  joinLeast := .joinLeast
  meetLeft ha hb hs := .atom (carrier_meet.mpr ⟨ha, hb⟩) ha (.meetLeft hs)
  meetRight ha hb hs := .atom (carrier_meet.mpr ⟨ha, hb⟩) hb (.meetRight hs)
  meetGreatest := .meetGreatest

end
end ModalityInference.ComparisonRawHeadRestriction
