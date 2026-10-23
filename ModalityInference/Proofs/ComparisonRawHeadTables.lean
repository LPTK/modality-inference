import ModalityInference.Proofs.ComparisonRawHeadRestriction
import ModalityInference.Proofs.ComparisonRawCarrierTables

/-! Ordered modal constructor tables over the whole-head restriction. Each
constructor output must already belong to the selected carrier. -/
namespace ModalityInference.ComparisonRawHeadRestriction

open ComparisonRawCarrierIdeals ComparisonRawCarrierRestriction

theorem Derivation.refl {Δ H a} (hc : Carrier Δ H a) (hs : CompareTy.WellShaped Δ a) :
    Derivation Δ H a a := .atom hc hc (.refl hs)

theorem Derivation.flatten_modal {Δ H a b m n r s}
    (h : Derivation Δ H (.modal (.modal a m) n) (.modal (.modal b r) s)) :
    Derivation Δ H (.modal a (.compose m n)) (.modal b (.compose r s)) :=
  (Derivation.atom (carrier_compose.mpr h.carriers.1) h.carriers.1
    (.composeRev h.shaped.1)).trans (h.trans
      (.atom h.carriers.2 (carrier_compose.mpr h.carriers.2) (.compose h.shaped.2)))

theorem Derivation.expand_modal {Δ H a b m n r s}
    (h : Derivation Δ H (.modal a (.compose m n)) (.modal b (.compose r s))) :
    Derivation Δ H (.modal (.modal a m) n) (.modal (.modal b r) s) :=
  (Derivation.atom (carrier_compose.mp h.carriers.1) h.carriers.1
    (.compose h.shaped.1)).trans (h.trans
      (.atom h.carriers.2 (carrier_compose.mp h.carriers.2) (.composeRev h.shaped.2)))

theorem Derivation.synchronize {Δ H a b m n}
    (h : Derivation Δ H (.modal a m) (.modal b n)) (hmn : Submode Δ m n) :
    Derivation Δ H (.modal a (.compose m n)) (.modal b (.compose m n)) := by
  have h' := (h.congr (Submode.refl hmn.compose_between.1.defined.2)).flatten_modal
  exact ((Derivation.refl ((carrier_modal_total hmn.defined.1).mp h.carriers.1)
    h.shaped.1).congr (submode_compose_absorb hmn).1).trans (h'.trans
      ((Derivation.refl ((carrier_modal_total hmn.defined.2).mp h.carriers.2)
        h.shaped.2).congr (submode_compose_absorb hmn).2))

theorem Derivation.inherited_prefix_ordered {Δ H a b c d p m n}
    (op : CompareTy → CompareTy → CompareTy)
    (rule : ∀ {a b c d r}, Carrier Δ H (.modal (op a b) r) →
      Carrier Δ H (.modal (op c d) r) →
      Derivation Δ H (.modal a r) (.modal c r) →
      Derivation Δ H (.modal b r) (.modal d r) →
      Derivation Δ H (.modal (op a b) r) (.modal (op c d) r))
    (hmn : Submode Δ m n)
    (hl : Carrier Δ H (.modal (.modal (op a b) p) m))
    (hr : Carrier Δ H (.modal (.modal (op c d) p) n))
    (hac : Derivation Δ H (.modal (.modal a p) m) (.modal (.modal c p) n))
    (hbd : Derivation Δ H (.modal (.modal b p) m) (.modal (.modal d p) n)) :
    Derivation Δ H (.modal (.modal (op a b) p) m) (.modal (.modal (op c d) p) n) := by
  have h := rule
    (carrier_compose.mpr ((carrier_modal_total hmn.compose_between.1.defined.2).mpr
      ((carrier_modal_total hmn.defined.1).mp hl)))
    (carrier_compose.mpr ((carrier_modal_total hmn.compose_between.1.defined.2).mpr
      ((carrier_modal_total hmn.defined.2).mp hr)))
    (hac.synchronize hmn).flatten_modal (hbd.synchronize hmn).flatten_modal
  exact ((Derivation.refl ((carrier_modal_total hmn.defined.1).mp hl)
    h.shaped.1).congr hmn.compose_between.1).trans
      (h.expand_modal.trans ((Derivation.refl ((carrier_modal_total hmn.defined.2).mp hr)
        h.shaped.2).congr hmn.compose_between.2))

theorem Derivation.inherited_ordered {Δ H a b c d m n}
    (op : CompareTy → CompareTy → CompareTy)
    (rule : ∀ {a b c d r}, Carrier Δ H (.modal (op a b) r) →
      Carrier Δ H (.modal (op c d) r) →
      Derivation Δ H (.modal a r) (.modal c r) →
      Derivation Δ H (.modal b r) (.modal d r) →
      Derivation Δ H (.modal (op a b) r) (.modal (op c d) r))
    (hmn : Submode Δ m n)
    (hl : Carrier Δ H (.modal (op a b) m)) (hr : Carrier Δ H (.modal (op c d) n))
    (hac : Derivation Δ H (.modal a m) (.modal c n))
    (hbd : Derivation Δ H (.modal b m) (.modal d n)) :
    Derivation Δ H (.modal (op a b) m) (.modal (op c d) n) := by
  have h := rule
    ((carrier_modal_total hmn.compose_between.1.defined.2).mpr
      ((carrier_modal_total hmn.defined.1).mp hl))
    ((carrier_modal_total hmn.compose_between.1.defined.2).mpr
      ((carrier_modal_total hmn.defined.2).mp hr))
    (hac.synchronize hmn) (hbd.synchronize hmn)
  exact ((Derivation.refl ((carrier_modal_total hmn.defined.1).mp hl)
    h.shaped.1).congr hmn.compose_between.1).trans
      (h.trans ((Derivation.refl ((carrier_modal_total hmn.defined.2).mp hr)
        h.shaped.2).congr hmn.compose_between.2))

open ComparisonPartialStructuredCapsule

def inheritedRow (Δ : Bounds) (H : Set CompareTy) (pref : Suffix)
    (op : CompareTy → CompareTy → CompareTy) (m : ModExpr)
    (x y z : CompareTy) : Prop :=
  ∃ a b, x = .modal (pref.apply a) m ∧ y = .modal (pref.apply b) m ∧
    z = .modal (pref.apply (op a b)) m ∧
    Carrier Δ H x ∧ Carrier Δ H y ∧ Carrier Δ H z ∧
    x.WellShaped Δ ∧ y.WellShaped Δ ∧ z.WellShaped Δ

theorem inheritedRow_mono {Δ H pref op m n x y z u v w}
    (rule : ∀ {a b c d r}, Carrier Δ H (.modal (op a b) r) →
      Carrier Δ H (.modal (op c d) r) →
      Derivation Δ H (.modal a r) (.modal c r) →
      Derivation Δ H (.modal b r) (.modal d r) →
      Derivation Δ H (.modal (op a b) r) (.modal (op c d) r))
    (hmn : Submode Δ m n) (hx : inheritedRow Δ H pref op m x y z)
    (hu : inheritedRow Δ H pref op n u v w)
    (hxu : Derivation Δ H x u) (hyv : Derivation Δ H y v) : Derivation Δ H z w := by
  obtain ⟨a,b,rfl,rfl,rfl,_,_,hz,_⟩ := hx
  obtain ⟨c,d,rfl,rfl,rfl,_,_,hw,_⟩ := hu
  cases pref with
  | none => exact Derivation.inherited_ordered op rule hmn hz hw hxu hyv
  | some p => exact Derivation.inherited_prefix_ordered op rule hmn hz hw hxu hyv

def inheritedTable (Δ : Bounds) (H : Set CompareTy) (pref : Suffix)
    (op : CompareTy → CompareTy → CompareTy)
    (rule : ∀ {a b c d r}, Carrier Δ H (.modal (op a b) r) →
      Carrier Δ H (.modal (op c d) r) →
      Derivation Δ H (.modal a r) (.modal c r) →
      Derivation Δ H (.modal b r) (.modal d r) →
      Derivation Δ H (.modal (op a b) r) (.modal (op c d) r))
    (m : TotalIndex Δ) : BinaryTable (core Δ H) false false where
  entry := inheritedRow Δ H pref op m.val
  left := by
    rintro _ _ _ ⟨a,b,_,_,_,ha,_⟩
    exact ha
  right := by
    rintro _ _ _ ⟨a,b,_,_,_,_,hb,_⟩
    exact hb
  output := by
    rintro _ _ _ ⟨a,b,_,_,_,_,_,hc,_⟩
    exact hc
  left_shaped := by
    rintro _ _ _ ⟨a,b,_,_,_,_,_,_,ha,_⟩
    exact ha
  right_shaped := by
    rintro _ _ _ ⟨a,b,_,_,_,_,_,_,_,hb,_⟩
    exact hb
  output_shaped := by
    rintro _ _ _ ⟨a,b,_,_,_,_,_,_,_,_,hc⟩
    exact hc
  mono := inheritedRow_mono rule (Submode.refl m.property)

def indexedInheritedTable (Δ : Bounds) (H : Set CompareTy) (pref : Suffix)
    (op : CompareTy → CompareTy → CompareTy)
    (rule : ∀ {a b c d r}, Carrier Δ H (.modal (op a b) r) →
      Carrier Δ H (.modal (op c d) r) →
      Derivation Δ H (.modal a r) (.modal c r) →
      Derivation Δ H (.modal b r) (.modal d r) →
      Derivation Δ H (.modal (op a b) r) (.modal (op c d) r)) :
    IndexedBinaryTable (core Δ H) (TotalIndex Δ) false false where
  table := inheritedTable Δ H pref op rule
  le m n := Submode Δ m.val n.val
  refl m := Submode.refl m.property
  trans := Submode.trans
  cross_mono := inheritedRow_mono rule

def indexedProdTable (Δ : Bounds) (H : Set CompareTy) (pref : Suffix) :
    IndexedBinaryTable (core Δ H) (TotalIndex Δ) false false :=
  indexedInheritedTable Δ H pref .prod Derivation.prod

def indexedSumTable (Δ : Bounds) (H : Set CompareTy) (pref : Suffix) :
    IndexedBinaryTable (core Δ H) (TotalIndex Δ) false false :=
  indexedInheritedTable Δ H pref .sum Derivation.sum

end ModalityInference.ComparisonRawHeadRestriction
