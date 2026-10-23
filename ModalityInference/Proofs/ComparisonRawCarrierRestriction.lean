import ModalityInference.Proofs.ComparisonPartialStructuredCapsule
import ModalityInference.Proofs.ComparisonRawModalRestriction
import ModalityInference.Proofs.ComparisonRawCarrierIdeals

/-! A capsule-supported subcalculus for arbitrary raw bounds. The carrier is
closed under lattice operations, including joins and meets of partial terms.
Partial actions retain their literal frozen payload; the relation below is an
inductive restriction of the original rules, not an oracle for their closure. -/
namespace ModalityInference.ComparisonRawCarrierRestriction

open ComparisonPartialStructuredCapsule

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Token := CompareTy × ModExpr

/-- The finite literal capsules needed by a term. Products and sums pass their
whole suffix to both children. Total suffixes inspect function and lattice
children, whereas partial suffixes freeze those constructors literally. -/
def support (Δ : Bounds) : CompareTy → Suffix → Set Token
  | .modal a m, suffix => support Δ a (suffix.prepend m)
  | .prod a b, suffix | .sum a b, suffix => support Δ a suffix ∪ support Δ b suffix
  | .fn a b, suffix =>
      if suffix.total Δ then support Δ a none ∪ support Δ b none
      else ComparisonPartialCapsule.observe Δ (suffix.apply (.fn a b))
  | .join a b, suffix =>
      if suffix.total Δ then support Δ a none ∪ support Δ b none
      else ComparisonPartialCapsule.observe Δ (suffix.apply (.join a b))
  | .meet a b, suffix =>
      if suffix.total Δ then support Δ a none ∪ support Δ b none
      else ComparisonPartialCapsule.observe Δ (suffix.apply (.meet a b))
  | a, suffix => ComparisonPartialCapsule.observe Δ (suffix.apply a)

theorem support_suffix_congr {Δ : Bounds} {left right : Suffix}
    (h : Suffix.Equivalent Δ left right) (a : CompareTy) :
    support Δ a left = support Δ a right := by
  induction a generalizing left right with
  | modal a m ih => exact ih (h.prepend m)
  | prod a b ia ib | sum a b ia ib => simp only [support, ia h, ib h]
  | fn a b ia ib | join a b ia ib | meet a b ia ib =>
      simp only [support, h.1, h.2]
  | var | unit | credit => simp only [support, h.2]

theorem support_total {Δ : Bounds} {suffix : Suffix} (h : suffix.total Δ) (a : CompareTy) :
    support Δ a suffix = support Δ a none := support_suffix_congr (Suffix.total_equivalent_none h) a

theorem support_modal_total {Δ : Bounds} {m : ModExpr} (h : Entails Δ (.defined m))
    (a : CompareTy) : support Δ (.modal a m) none = support Δ a none :=
  support_total (suffix := some m) h a

theorem support_compose (Δ : Bounds) (a : CompareTy) (m n : ModExpr) :
    support Δ (.modal a (.compose m n)) none = support Δ (.modal (.modal a m) n) none := rfl

def Carrier (Δ : Bounds) (K : Set Token) (a : CompareTy) : Prop := support Δ a none ⊆ K

@[simp] theorem carrier_prod {Δ K a b} :
    Carrier Δ K (.prod a b) ↔ Carrier Δ K a ∧ Carrier Δ K b := Set.union_subset_iff

@[simp] theorem carrier_sum {Δ K a b} :
    Carrier Δ K (.sum a b) ↔ Carrier Δ K a ∧ Carrier Δ K b := Set.union_subset_iff

@[simp] theorem carrier_fn {Δ K a b} :
    Carrier Δ K (.fn a b) ↔ Carrier Δ K a ∧ Carrier Δ K b := by
  simp only [Carrier, support, Suffix.total, ↓reduceIte, Set.union_subset_iff]

@[simp] theorem carrier_join {Δ K a b} :
    Carrier Δ K (.join a b) ↔ Carrier Δ K a ∧ Carrier Δ K b := by
  simp only [Carrier, support, Suffix.total, ↓reduceIte, Set.union_subset_iff]

@[simp] theorem carrier_meet {Δ K a b} :
    Carrier Δ K (.meet a b) ↔ Carrier Δ K a ∧ Carrier Δ K b := by
  simp only [Carrier, support, Suffix.total, ↓reduceIte, Set.union_subset_iff]

theorem carrier_modal_total {Δ K a m} (hm : Entails Δ (.defined m)) :
    Carrier Δ K (.modal a m) ↔ Carrier Δ K a := by
  simp only [Carrier, support_modal_total hm]

theorem carrier_compose {Δ K a m n} :
    Carrier Δ K (.modal a (.compose m n)) ↔ Carrier Δ K (.modal (.modal a m) n) := Iff.rfl

@[simp] theorem carrier_modal_prod {Δ K a b m} :
    Carrier Δ K (.modal (.prod a b) m) ↔
      Carrier Δ K (.modal a m) ∧ Carrier Δ K (.modal b m) := Set.union_subset_iff

@[simp] theorem carrier_modal_sum {Δ K a b m} :
    Carrier Δ K (.modal (.sum a b) m) ↔
      Carrier Δ K (.modal a m) ∧ Carrier Δ K (.modal b m) := Set.union_subset_iff

theorem support_defined {Δ : Bounds} {a : CompareTy} (h : a.DefinedUnder Δ) :
    support Δ a none = ∅ := by
  induction a with
  | var | unit | credit =>
      simp only [support, Suffix.apply, ComparisonPartialCapsule.observe]
  | prod a b ia ib | sum a b ia ib =>
      exact congrArg₂ (· ∪ ·) (ia (CompareTy.definedUnder_prod_iff.mp h).1)
        (ib (CompareTy.definedUnder_prod_iff.mp h).2) |>.trans (Set.empty_union _)
  | fn a b ia ib | join a b ia ib | meet a b ia ib =>
      simp only [support, Suffix.total, ↓reduceIte,
        ia (CompareTy.definedUnder_fn_iff.mp h).1,
        ib (CompareTy.definedUnder_fn_iff.mp h).2, Set.empty_union]
  | modal a m ih =>
      rw [support_modal_total (CompareTy.definedUnder_modal_iff.mp h).2,
        ih (CompareTy.definedUnder_modal_iff.mp h).1]

theorem carrier_defined {Δ K a} (h : CompareTy.DefinedUnder a Δ) : Carrier Δ K a := by
  simp only [Carrier, support_defined h, Set.empty_subset]

abbrev Atomic := ComparisonRawModalRestriction.Atomic

/-- The original rules with every recursive endpoint supported by the fixed
capsule set. No constructor assumes the unrestricted comparison relation. -/
inductive Derivation (Δ : Bounds) (K : Set Token) : CompareTy → CompareTy → Prop where
  | atom {a b} : Carrier Δ K a → Carrier Δ K b → Atomic Δ a b → Derivation Δ K a b
  | trans {a b c} : Derivation Δ K a b → Derivation Δ K b c → Derivation Δ K a c
  | congr {a b m n} : Derivation Δ K a b → Submode Δ m n →
      Derivation Δ K (.modal a m) (.modal b n)
  | prod {a b c d m} : Derivation Δ K (.modal a m) (.modal c m) →
      Derivation Δ K (.modal b m) (.modal d m) →
      Derivation Δ K (.modal (.prod a b) m) (.modal (.prod c d) m)
  | sum {a b c d m} : Derivation Δ K (.modal a m) (.modal c m) →
      Derivation Δ K (.modal b m) (.modal d m) →
      Derivation Δ K (.modal (.sum a b) m) (.modal (.sum c d) m)
  | fn {a b c d m n} : Derivation Δ K c a → Derivation Δ K b d →
      Submode Δ m (.compose n .top) →
      Derivation Δ K (.modal (.fn a b) m) (.modal (.fn c d) n)
  | joinLeast {a b c} : Derivation Δ K a c → Derivation Δ K b c →
      Derivation Δ K (.join a b) c
  | meetGreatest {a b c} : Derivation Δ K a b → Derivation Δ K a c →
      Derivation Δ K a (.meet b c)
  | clamp {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → ComparisonAlgebra.DefinedMode Δ m →
      Derivation Δ K b a → Derivation Δ K a t →
      Derivation Δ K (.modal a m) (.meet (.join a (.modal b m)) (.modal t m))
  | clampRev {b a t m} : ComparisonAlgebra.Compatible Δ b a →
      ComparisonAlgebra.Compatible Δ a t → ComparisonAlgebra.DefinedMode Δ m →
      Derivation Δ K b a → Derivation Δ K a t →
      Derivation Δ K (.meet (.join a (.modal b m)) (.modal t m)) (.modal a m)

theorem Derivation.algebra {Δ K a b} (h : Derivation Δ K a b) : AlgebraSubtype Δ a b := by
  induction h with
  | atom _ _ h => exact h.subtype
  | trans _ _ iha ihb => exact .trans iha ihb
  | congr _ hm ih => exact .congr ih hm
  | prod _ _ iha ihb => exact .prod iha ihb
  | sum _ _ iha ihb => exact .sum iha ihb
  | fn _ _ hm iha ihb => exact .fn iha ihb hm
  | joinLeast _ _ iha ihb => exact .joinLeast iha ihb
  | meetGreatest _ _ iha ihb => exact .meetGreatest iha ihb
  | clamp hab hat hm _ _ ihb iht => exact .clamp hab hat hm ihb iht
  | clampRev hab hat hm _ _ ihb iht => exact .clampRev hab hat hm ihb iht

theorem Derivation.carriers {Δ K a b} (h : Derivation Δ K a b) :
    Carrier Δ K a ∧ Carrier Δ K b := by
  induction h with
  | atom ha hb _ => exact ⟨ha, hb⟩
  | trans _ _ ha hb => exact ⟨ha.1, hb.2⟩
  | congr _ hm ih => exact ⟨(carrier_modal_total hm.defined.1).mpr ih.1,
      (carrier_modal_total hm.defined.2).mpr ih.2⟩
  | prod _ _ ha hb => exact ⟨carrier_modal_prod.mpr ⟨ha.1, hb.1⟩,
      carrier_modal_prod.mpr ⟨ha.2, hb.2⟩⟩
  | sum _ _ ha hb => exact ⟨carrier_modal_sum.mpr ⟨ha.1, hb.1⟩,
      carrier_modal_sum.mpr ⟨ha.2, hb.2⟩⟩
  | fn _ _ hm ha hb => exact ⟨(carrier_modal_total hm.defined.1).mpr
      (carrier_fn.mpr ⟨ha.2, hb.1⟩),
      (carrier_modal_total (Entails.defined_compose_iff.mp hm.defined.2).1).mpr
      (carrier_fn.mpr ⟨ha.1, hb.2⟩)⟩
  | joinLeast _ _ ha hb => exact ⟨carrier_join.mpr ⟨ha.1, hb.1⟩, ha.2⟩
  | meetGreatest _ _ ha hb => exact ⟨ha.1, carrier_meet.mpr ⟨ha.2, hb.2⟩⟩
  | clamp hab hat hm _ _ hb ht =>
      exact ⟨(carrier_modal_total hm).mpr hb.2,
        carrier_meet.mpr ⟨carrier_join.mpr ⟨hb.2, (carrier_modal_total hm).mpr hb.1⟩,
          (carrier_modal_total hm).mpr ht.2⟩⟩
  | clampRev hab hat hm _ _ hb ht =>
      exact ⟨carrier_meet.mpr ⟨carrier_join.mpr ⟨hb.2, (carrier_modal_total hm).mpr hb.1⟩,
          (carrier_modal_total hm).mpr ht.2⟩, (carrier_modal_total hm).mpr hb.2⟩

theorem Derivation.shaped {Δ K a b} (h : Derivation Δ K a b) :
    a.WellShaped Δ ∧ b.WellShaped Δ := ⟨h.algebra.wellShaped_left, h.algebra.wellShaped_right⟩

def core (Δ : Bounds) (K : Set Token) : ComparisonRawCarrierIdeals.Core Δ where
  carrier := Carrier Δ K
  le := Derivation Δ K
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

theorem capsule_observe_finite (Δ : Bounds) (a : CompareTy) :
    (ComparisonPartialCapsule.observe Δ a).Finite := by
  fun_induction ComparisonPartialCapsule.observe Δ a with
  | case1 _ _ _ ih | case2 _ _ _ _ ih => exact ih
  | case3 => exact Set.finite_singleton _
  | case4 _ _ ha hb => exact ha.union hb
  | case5 _ _ ha hb => exact ha.inter_of_left _
  | case6 => exact Set.finite_empty

theorem support_finite (Δ : Bounds) (a : CompareTy) (suffix : Suffix) :
    (support Δ a suffix).Finite := by
  induction a generalizing suffix with
  | modal a m ih => exact ih _
  | prod a b ha hb | sum a b ha hb => exact (ha _).union (hb _)
  | fn a b ha hb | join a b ha hb | meet a b ha hb =>
      exact if h : suffix.total Δ then
        (show (support Δ a none ∪ support Δ b none).Finite from (ha _).union (hb _))
          |> (by simpa only [support, if_pos h] using ·)
        else capsule_observe_finite _ _ |> (by simpa only [support, if_neg h] using ·)
  | var | unit | credit => exact capsule_observe_finite _ _

theorem Derivation.refl {Δ K a} (hc : Carrier Δ K a) (hs : CompareTy.WellShaped Δ a) :
    Derivation Δ K a a := .atom hc hc (.refl hs)

theorem Derivation.identity {Δ K a} (hc : Carrier Δ K a) (hs : CompareTy.WellShaped Δ a) :
    Derivation Δ K (.modal a .epsilon) a :=
  .atom ((carrier_modal_total (m := .epsilon) (fun _ _ => rfl)).mpr hc) hc (.identity hs)

theorem Derivation.identityRev {Δ K a} (hc : Carrier Δ K a) (hs : CompareTy.WellShaped Δ a) :
    Derivation Δ K a (.modal a .epsilon) :=
  .atom hc ((carrier_modal_total (m := .epsilon) (fun _ _ => rfl)).mpr hc) (.identityRev hs)

theorem Derivation.prod_congr {Δ K a b c d}
    (ha : Derivation Δ K a c) (hb : Derivation Δ K b d) :
    Derivation Δ K (.prod a b) (.prod c d) :=
  (Derivation.identityRev (carrier_prod.mpr ⟨ha.carriers.1, hb.carriers.1⟩)
    ⟨ha.shaped.1, hb.shaped.1⟩).trans
    ((Derivation.prod (ha.congr (Submode.refl (m := .epsilon) (fun _ _ => rfl)))
      (hb.congr (Submode.refl (m := .epsilon) (fun _ _ => rfl)))).trans
      (.identity (carrier_prod.mpr ⟨ha.carriers.2, hb.carriers.2⟩) ⟨ha.shaped.2, hb.shaped.2⟩))

theorem Derivation.sum_congr {Δ K a b c d}
    (ha : Derivation Δ K a c) (hb : Derivation Δ K b d) :
    Derivation Δ K (.sum a b) (.sum c d) :=
  (Derivation.identityRev (carrier_sum.mpr ⟨ha.carriers.1, hb.carriers.1⟩)
    ⟨ha.shaped.1, hb.shaped.1⟩).trans
    ((Derivation.sum (ha.congr (Submode.refl (m := .epsilon) (fun _ _ => rfl)))
      (hb.congr (Submode.refl (m := .epsilon) (fun _ _ => rfl)))).trans
      (.identity (carrier_sum.mpr ⟨ha.carriers.2, hb.carriers.2⟩) ⟨ha.shaped.2, hb.shaped.2⟩))

theorem Derivation.fn_congr {Δ K a b c d}
    (ha : Derivation Δ K c a) (hb : Derivation Δ K b d) :
    Derivation Δ K (.fn a b) (.fn c d) :=
  (Derivation.identityRev (carrier_fn.mpr ⟨ha.carriers.2, hb.carriers.1⟩)
    ⟨ha.shaped.2, hb.shaped.1⟩).trans
    ((Derivation.fn ha hb (.valid fun _ _ =>
      ⟨Mode.identity, Mode.identity.compose Mode.top, rfl, rfl, by decide⟩)).trans
      (.identity (carrier_fn.mpr ⟨ha.carriers.1, hb.carriers.2⟩) ⟨ha.shaped.1, hb.shaped.2⟩))

end
end ModalityInference.ComparisonRawCarrierRestriction
