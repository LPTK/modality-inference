import ModalityInference.Proofs.ComparisonRawCarrierRestriction

/-! Products and sums transport comparisons between distinct ordered total
annotations. Payloads may be partial. The proof synchronizes both annotations
at their composition and uses only the original inherited-action rules. -/
namespace ModalityInference.ComparisonRawCarrierRestriction

theorem submode_compose_between {Δ m n} (h : Submode Δ m n) :
    Submode Δ m (.compose m n) ∧ Submode Δ (.compose m n) n := h.compose_between

theorem submode_compose_absorb {Δ m n} (h : Submode Δ m n) :
    Submode Δ (.compose m n) (.compose m (.compose m n)) ∧
      Submode Δ (.compose n (.compose m n)) (.compose m n) := by
  constructor
  · apply Submode.valid
    intro η hη
    obtain ⟨x,y,hx,hy,_⟩ := h.denote hη
    exact ⟨x.compose y, x.compose y, by simp [ModExpr.eval, hx, hy],
      by simp [ModExpr.eval, hx, hy], Mode.le_refl _⟩
  · apply Submode.valid
    intro η hη
    obtain ⟨x,y,hx,hy,_⟩ := h.denote hη
    exact ⟨x.compose y, x.compose y,
      by simp [ModExpr.eval, hx, hy],
      by simp [ModExpr.eval, hx, hy], Mode.le_refl _⟩

theorem Derivation.postcompose {Δ K a b m n k}
    (h : Derivation Δ K (.modal a m) (.modal b n)) (hk : Entails Δ (.defined k)) :
    Derivation Δ K (.modal a (.compose m k)) (.modal b (.compose n k)) := by
  have h' := h.congr (Submode.refl hk)
  exact (Derivation.atom (carrier_compose.mpr h'.carriers.1) h'.carriers.1
    (.composeRev h'.shaped.1)).trans (h'.trans
      (.atom h'.carriers.2 (carrier_compose.mpr h'.carriers.2) (.compose h'.shaped.2)))

/-- Ordered total labels have a common composite at which both child
comparisons can be read. No definedness condition is placed on the payloads. -/
theorem Derivation.synchronize {Δ K a b m n}
    (h : Derivation Δ K (.modal a m) (.modal b n)) (hmn : Submode Δ m n) :
    Derivation Δ K (.modal a (.compose m n)) (.modal b (.compose m n)) := by
  have hk := (submode_compose_between hmn).1.defined.2
  have ha := Derivation.refl ((carrier_modal_total hmn.defined.1).mp h.carriers.1) h.shaped.1
  have hb := Derivation.refl ((carrier_modal_total hmn.defined.2).mp h.carriers.2) h.shaped.2
  exact (ha.congr (submode_compose_absorb hmn).1).trans
    ((h.postcompose hk).trans (hb.congr (submode_compose_absorb hmn).2))

theorem Derivation.inherited_ordered {Δ K a b c d m n}
    (op : CompareTy → CompareTy → CompareTy)
    (rule : ∀ {a b c d r}, Derivation Δ K (.modal a r) (.modal c r) →
      Derivation Δ K (.modal b r) (.modal d r) →
      Derivation Δ K (.modal (op a b) r) (.modal (op c d) r))
    (hmn : Submode Δ m n)
    (hac : Derivation Δ K (.modal a m) (.modal c n))
    (hbd : Derivation Δ K (.modal b m) (.modal d n)) :
    Derivation Δ K (.modal (op a b) m) (.modal (op c d) n) := by
  obtain ⟨hmk,hkn⟩ := submode_compose_between hmn
  have h := rule (hac.synchronize hmn) (hbd.synchronize hmn)
  have ha := Derivation.refl ((carrier_modal_total hmk.defined.2).mp h.carriers.1) h.shaped.1
  have hb := Derivation.refl ((carrier_modal_total hmk.defined.2).mp h.carriers.2) h.shaped.2
  exact (ha.congr hmk).trans (h.trans (hb.congr hkn))

theorem Derivation.prod_ordered {Δ K a b c d m n} (hmn : Submode Δ m n)
    (hac : Derivation Δ K (.modal a m) (.modal c n))
    (hbd : Derivation Δ K (.modal b m) (.modal d n)) :
    Derivation Δ K (.modal (.prod a b) m) (.modal (.prod c d) n) :=
  Derivation.inherited_ordered .prod Derivation.prod hmn hac hbd

theorem Derivation.sum_ordered {Δ K a b c d m n} (hmn : Submode Δ m n)
    (hac : Derivation Δ K (.modal a m) (.modal c n))
    (hbd : Derivation Δ K (.modal b m) (.modal d n)) :
    Derivation Δ K (.modal (.sum a b) m) (.modal (.sum c d) n) :=
  Derivation.inherited_ordered .sum Derivation.sum hmn hac hbd

theorem Derivation.flatten_modal {Δ K a b m n r s}
    (h : Derivation Δ K (.modal (.modal a m) n) (.modal (.modal b r) s)) :
    Derivation Δ K (.modal a (.compose m n)) (.modal b (.compose r s)) :=
  (Derivation.atom (carrier_compose.mpr h.carriers.1) h.carriers.1
    (.composeRev h.shaped.1)).trans (h.trans
      (.atom h.carriers.2 (carrier_compose.mpr h.carriers.2) (.compose h.shaped.2)))

theorem Derivation.expand_modal {Δ K a b m n r s}
    (h : Derivation Δ K (.modal a (.compose m n)) (.modal b (.compose r s))) :
    Derivation Δ K (.modal (.modal a m) n) (.modal (.modal b r) s) :=
  (Derivation.atom (carrier_compose.mp h.carriers.1) h.carriers.1
    (.compose h.shaped.1)).trans (h.trans
      (.atom h.carriers.2 (carrier_compose.mp h.carriers.2) (.composeRev h.shaped.2)))

/-- A shared literal prefix may be undefined. Only the two outer labels are
compared; no rewriting or equivalence of partial annotations is assumed. -/
theorem Derivation.inherited_prefix_ordered {Δ K a b c d p m n}
    (op : CompareTy → CompareTy → CompareTy)
    (rule : ∀ {a b c d r}, Derivation Δ K (.modal a r) (.modal c r) →
      Derivation Δ K (.modal b r) (.modal d r) →
      Derivation Δ K (.modal (op a b) r) (.modal (op c d) r))
    (hmn : Submode Δ m n)
    (hac : Derivation Δ K (.modal (.modal a p) m) (.modal (.modal c p) n))
    (hbd : Derivation Δ K (.modal (.modal b p) m) (.modal (.modal d p) n)) :
    Derivation Δ K (.modal (.modal (op a b) p) m) (.modal (.modal (op c d) p) n) := by
  obtain ⟨hmk,hkn⟩ := submode_compose_between hmn
  have h := (rule (hac.synchronize hmn).flatten_modal
    (hbd.synchronize hmn).flatten_modal).expand_modal
  have ha := Derivation.refl ((carrier_modal_total hmk.defined.2).mp h.carriers.1) h.shaped.1
  have hb := Derivation.refl ((carrier_modal_total hmk.defined.2).mp h.carriers.2) h.shaped.2
  exact (ha.congr hmk).trans (h.trans (hb.congr hkn))

theorem Derivation.prod_prefix_ordered {Δ K a b c d p m n} (hmn : Submode Δ m n)
    (hac : Derivation Δ K (.modal (.modal a p) m) (.modal (.modal c p) n))
    (hbd : Derivation Δ K (.modal (.modal b p) m) (.modal (.modal d p) n)) :
    Derivation Δ K (.modal (.modal (.prod a b) p) m) (.modal (.modal (.prod c d) p) n) :=
  Derivation.inherited_prefix_ordered .prod Derivation.prod hmn hac hbd

theorem Derivation.sum_prefix_ordered {Δ K a b c d p m n} (hmn : Submode Δ m n)
    (hac : Derivation Δ K (.modal (.modal a p) m) (.modal (.modal c p) n))
    (hbd : Derivation Δ K (.modal (.modal b p) m) (.modal (.modal d p) n)) :
    Derivation Δ K (.modal (.modal (.sum a b) p) m) (.modal (.modal (.sum c d) p) n) :=
  Derivation.inherited_prefix_ordered .sum Derivation.sum hmn hac hbd

end ModalityInference.ComparisonRawCarrierRestriction

namespace ModalityInference

open ComparisonRawCarrierRestriction

theorem AlgebraSubtype.postcompose {Δ a b m n k}
    (h : AlgebraSubtype Δ (.modal a m) (.modal b n)) (hk : Entails Δ (.defined k)) :
    AlgebraSubtype Δ (.modal a (.compose m k)) (.modal b (.compose n k)) :=
  (AlgebraSubtype.shaped (.composeRev (a := a) h.wellShaped_left)).trans
    ((h.congr (.refl hk)).trans (.shaped (.compose (a := b) h.wellShaped_right)))

theorem AlgebraSubtype.synchronize {Δ a b m n}
    (h : AlgebraSubtype Δ (.modal a m) (.modal b n)) (hmn : Submode Δ m n) :
    AlgebraSubtype Δ (.modal a (.compose m n)) (.modal b (.compose m n)) :=
  ((AlgebraSubtype.refl (a := a) h.wellShaped_left).congr (submode_compose_absorb hmn).1).trans
    ((h.postcompose (submode_compose_between hmn).1.defined.2).trans
      ((AlgebraSubtype.refl (a := b) h.wellShaped_right).congr (submode_compose_absorb hmn).2))

theorem AlgebraSubtype.inherited_ordered {Δ a b c d m n}
    (op : CompareTy → CompareTy → CompareTy)
    (rule : ∀ {a b c d r}, AlgebraSubtype Δ (.modal a r) (.modal c r) →
      AlgebraSubtype Δ (.modal b r) (.modal d r) →
      AlgebraSubtype Δ (.modal (op a b) r) (.modal (op c d) r))
    (hmn : Submode Δ m n)
    (hac : AlgebraSubtype Δ (.modal a m) (.modal c n))
    (hbd : AlgebraSubtype Δ (.modal b m) (.modal d n)) :
    AlgebraSubtype Δ (.modal (op a b) m) (.modal (op c d) n) := by
  obtain ⟨hmk,hkn⟩ := submode_compose_between hmn
  have h := rule (hac.synchronize hmn) (hbd.synchronize hmn)
  exact ((AlgebraSubtype.refl (a := op a b) h.wellShaped_left).congr hmk).trans
    (h.trans ((AlgebraSubtype.refl (a := op c d) h.wellShaped_right).congr hkn))

theorem AlgebraSubtype.prod_ordered {Δ a b c d m n} (hmn : Submode Δ m n)
    (hac : AlgebraSubtype Δ (.modal a m) (.modal c n))
    (hbd : AlgebraSubtype Δ (.modal b m) (.modal d n)) :
    AlgebraSubtype Δ (.modal (.prod a b) m) (.modal (.prod c d) n) :=
  AlgebraSubtype.inherited_ordered .prod AlgebraSubtype.prod hmn hac hbd

theorem AlgebraSubtype.sum_ordered {Δ a b c d m n} (hmn : Submode Δ m n)
    (hac : AlgebraSubtype Δ (.modal a m) (.modal c n))
    (hbd : AlgebraSubtype Δ (.modal b m) (.modal d n)) :
    AlgebraSubtype Δ (.modal (.sum a b) m) (.modal (.sum c d) n) :=
  AlgebraSubtype.inherited_ordered .sum AlgebraSubtype.sum hmn hac hbd

theorem AlgebraSubtype.flatten_modal {Δ a b m n r s}
    (h : AlgebraSubtype Δ (.modal (.modal a m) n) (.modal (.modal b r) s)) :
    AlgebraSubtype Δ (.modal a (.compose m n)) (.modal b (.compose r s)) :=
  (AlgebraSubtype.shaped (.composeRev (a := a) h.wellShaped_left)).trans
    (h.trans (.shaped (.compose (a := b) h.wellShaped_right)))

theorem AlgebraSubtype.expand_modal {Δ a b m n r s}
    (h : AlgebraSubtype Δ (.modal a (.compose m n)) (.modal b (.compose r s))) :
    AlgebraSubtype Δ (.modal (.modal a m) n) (.modal (.modal b r) s) :=
  (AlgebraSubtype.shaped (.compose (a := a) h.wellShaped_left)).trans
    (h.trans (.shaped (.composeRev (a := b) h.wellShaped_right)))

theorem AlgebraSubtype.inherited_prefix_ordered {Δ a b c d p m n}
    (op : CompareTy → CompareTy → CompareTy)
    (rule : ∀ {a b c d r}, AlgebraSubtype Δ (.modal a r) (.modal c r) →
      AlgebraSubtype Δ (.modal b r) (.modal d r) →
      AlgebraSubtype Δ (.modal (op a b) r) (.modal (op c d) r))
    (hmn : Submode Δ m n)
    (hac : AlgebraSubtype Δ (.modal (.modal a p) m) (.modal (.modal c p) n))
    (hbd : AlgebraSubtype Δ (.modal (.modal b p) m) (.modal (.modal d p) n)) :
    AlgebraSubtype Δ (.modal (.modal (op a b) p) m) (.modal (.modal (op c d) p) n) := by
  obtain ⟨hmk,hkn⟩ := submode_compose_between hmn
  have h := (rule (hac.synchronize hmn).flatten_modal
    (hbd.synchronize hmn).flatten_modal).expand_modal
  exact ((AlgebraSubtype.refl (a := .modal (op a b) p) h.wellShaped_left).congr hmk).trans
    (h.trans ((AlgebraSubtype.refl (a := .modal (op c d) p) h.wellShaped_right).congr hkn))

theorem AlgebraSubtype.prod_prefix_ordered {Δ a b c d p m n} (hmn : Submode Δ m n)
    (hac : AlgebraSubtype Δ (.modal (.modal a p) m) (.modal (.modal c p) n))
    (hbd : AlgebraSubtype Δ (.modal (.modal b p) m) (.modal (.modal d p) n)) :
    AlgebraSubtype Δ (.modal (.modal (.prod a b) p) m) (.modal (.modal (.prod c d) p) n) :=
  AlgebraSubtype.inherited_prefix_ordered .prod AlgebraSubtype.prod hmn hac hbd

theorem AlgebraSubtype.sum_prefix_ordered {Δ a b c d p m n} (hmn : Submode Δ m n)
    (hac : AlgebraSubtype Δ (.modal (.modal a p) m) (.modal (.modal c p) n))
    (hbd : AlgebraSubtype Δ (.modal (.modal b p) m) (.modal (.modal d p) n)) :
    AlgebraSubtype Δ (.modal (.modal (.sum a b) p) m) (.modal (.modal (.sum c d) p) n) :=
  AlgebraSubtype.inherited_prefix_ordered .sum AlgebraSubtype.sum hmn hac hbd

end ModalityInference
