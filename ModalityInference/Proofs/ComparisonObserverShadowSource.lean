import ModalityInference.Proofs.ComparisonObserverShadowRealization

/-! Actual optional defined cuts supply the finite shadow presentation. Fresh
names designate their attained observer-range values without requiring a
single finite term that represents a whole cut. -/
namespace ModalityInference.ComparisonObserverShadowPresentation

open ComparisonObserverHeadCuts ComparisonObserverShadowRows ComparisonRelativeIntervals

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} {P : Type*} [Preorder P]

def headIntervals (term : P → CompareTy)
    (horder : ∀ p q, p ≤ q ↔ AlgebraSubtype Δ (term p) (term q)) :
    IntervalData (ComparisonObserverRangeProduct.Value Δ) P where
  lower p := if h : LowerInhabited (Δ := Δ) (shape := .unit) (term p) then some (lower h) else none
  upper p := if h : UpperInhabited (Δ := Δ) (shape := .unit) (term p) then some (upper h) else none
  consistent := by
    intro p a b ha hb
    split at ha
    next hp =>
      split at hb
      next hu =>
        cases ha; cases hb
        exact ComparisonObserverShadowRows.consistent hp hu
      next => cases hb
    next => cases ha
  lower_mono := by
    intro p q hpq a ha
    split at ha
    next hp =>
      cases ha
      have hq := hp.mono ((horder p q).mp hpq)
      exact ⟨lower hq,dif_pos hq,ComparisonObserverShadowRows.lower_mono hp hq ((horder p q).mp hpq)⟩
    next h => cases ha
  upper_mono := by
    intro p q hpq b hb
    split at hb
    next hq =>
      cases hb
      have hp := hq.antitone ((horder p q).mp hpq)
      exact ⟨upper hp,dif_pos hp,ComparisonObserverShadowRows.upper_mono hp hq ((horder p q).mp hpq)⟩
    next h => cases hb
  saturated := by
    intro p q a b ha hb hab
    split at ha
    next hp =>
      split at hb
      next hq =>
        cases ha; cases hb
        exact (horder p q).mpr (ComparisonObserverShadowRows.saturation hp hq hab)
      next => cases hb
    next => cases ha

section Names

variable [Fintype P]

def shadowName (base : Nat) (slot : P × Bool) : TypeVar :=
  .rigid (base + (Fintype.equivFin (P × Bool) slot).val)

omit [Preorder P] in
theorem shadowName_injective (base : Nat) : Function.Injective (shadowName (P := P) base) := by
  intro a b h
  apply (Fintype.equivFin (P × Bool)).injective
  apply Fin.ext
  exact Nat.add_left_cancel (TypeVar.rigid.inj h)

omit [Preorder P] in
theorem shadowName_index (base : Nat) (slot : P × Bool) :
    base ≤ (shadowName base slot).index := by
  exact Nat.le_add_right _ _

variable (I : IntervalData (ComparisonObserverRangeProduct.Value Δ) P)

def slotValue (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (base : Nat) (slot : P × Bool) : ComparisonObserverRangeProduct.Value Δ :=
  (if slot.2 then I.upper slot.1 else I.lower slot.1).getD (fallback (shadowName base slot))

def shadowAssign (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (base : Nat) (v : TypeVar) : ComparisonObserverRangeProduct.Value Δ :=
  if h : ∃ slot, shadowName base slot = v then slotValue I fallback base h.choose else fallback v

theorem shadowAssign_name (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (base : Nat) (slot : P × Bool) :
    shadowAssign I fallback base (shadowName base slot) = slotValue I fallback base slot := by
  unfold shadowAssign
  split
  next h => exact congrArg (slotValue I fallback base) (shadowName_injective base h.choose_spec)
  next h => exact False.elim (h ⟨slot,rfl⟩)

theorem shadowAssign_fresh (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (base : Nat) (v : TypeVar) (hv : v.index < base) :
    shadowAssign I fallback base v = fallback v := by
  apply dif_neg
  rintro ⟨slot,rfl⟩
  exact Nat.not_lt_of_ge (shadowName_index base slot) hv

theorem shadowAssign_lower (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (base : Nat) {p : P} {a : ComparisonObserverRangeProduct.Value Δ} (h : I.lower p = some a) :
    shadowAssign I fallback base (shadowName base (p,false)) = a := by
  rw [shadowAssign_name I]
  simp [slotValue,h]

theorem shadowAssign_upper (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (base : Nat) {p : P} {a : ComparisonObserverRangeProduct.Value Δ} (h : I.upper p = some a) :
    shadowAssign I fallback base (shadowName base (p,true)) = a := by
  rw [shadowAssign_name I]
  simp [slotValue,h]

def named (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ) (base : Nat) :
    NamedIntervals (shadowAssign I fallback base) P where
  lower p := (I.lower p).map fun _ => shadowName base (p,false)
  upper p := (I.upper p).map fun _ => shadowName base (p,true)
  consistent := by
    intro p v w hv hw
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hv
    obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp hw
    rw [shadowAssign_lower I fallback base ha,shadowAssign_upper I fallback base hb]
    exact I.consistent p a b ha hb
  lower_mono := by
    intro p q hpq v hv
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hv
    obtain ⟨b,hb,hab⟩ := I.lower_mono hpq ha
    refine ⟨shadowName base (q,false),by simp [hb],?_⟩
    rw [shadowAssign_lower I fallback base ha,shadowAssign_lower I fallback base hb]
    exact hab
  upper_mono := by
    intro p q hpq w hw
    obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp hw
    obtain ⟨a,ha,hab⟩ := I.upper_mono hpq hb
    refine ⟨shadowName base (p,true),by simp [ha],?_⟩
    rw [shadowAssign_upper I fallback base ha,shadowAssign_upper I fallback base hb]
    exact hab
  saturated := by
    intro p q v w hv hw hvw
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hv
    obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp hw
    rw [shadowAssign_upper I fallback base ha,shadowAssign_lower I fallback base hb] at hvw
    exact I.saturated p q a b ha hb hvw

theorem named_head_lower (term : P → CompareTy)
    (horder : ∀ p q, p ≤ q ↔ AlgebraSubtype Δ (term p) (term q))
    (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ) (base : Nat) (p : P)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (term p)) :
    shadowAssign (headIntervals term horder) fallback base (shadowName base (p,false)) = lower hp :=
  shadowAssign_lower _ fallback base (dif_pos hp)

theorem named_head_upper (term : P → CompareTy)
    (horder : ∀ p q, p ≤ q ↔ AlgebraSubtype Δ (term p) (term q))
    (fallback : TypeVar → ComparisonObserverRangeProduct.Value Δ) (base : Nat) (p : P)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (term p)) :
    shadowAssign (headIntervals term horder) fallback base (shadowName base (p,true)) = upper hp :=
  shadowAssign_upper _ fallback base (dif_pos hp)

end Names
end
end ModalityInference.ComparisonObserverShadowPresentation
