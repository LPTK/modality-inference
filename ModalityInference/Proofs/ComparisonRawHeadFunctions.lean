import ModalityInference.Proofs.ComparisonRawHeadTables

/-! Function rows compare total outer controls through their future coordinates.
Arguments remain unacted and the domain reverses order. Every output must
already belong to the whole-head carrier. -/
namespace ModalityInference.ComparisonRawHeadRestriction

open ComparisonRawCarrierIdeals ComparisonRawCarrierRestriction

def FnIndexLe (Δ : Bounds) (m n : ModExpr) : Prop := Submode Δ m (.compose n .top)

theorem FnIndexLe.refl {Δ m} (hm : Entails Δ (.defined m)) : FnIndexLe Δ m m := by
  apply Submode.valid
  intro η hη
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  exact ⟨x,x.compose Mode.top,hx,by simp [ModExpr.eval,ModExpr.top,hx],
    by simp [Mode.le_iff,Mode.compose,Mode.top]⟩

theorem FnIndexLe.trans {Δ m n r} (hmn : FnIndexLe Δ m n) (hnr : FnIndexLe Δ n r) :
    FnIndexLe Δ m r := by
  apply Submode.valid
  intro η hη
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp (hmn.defined.1 η hη)
  obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp (hnr.defined.1 η hη)
  obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp
    ((Entails.defined_compose_iff.mp hnr.defined.2).1 η hη)
  have hxy := hmn.denote hη
  have hyz := hnr.denote hη
  simp [ModExpr.Below,ModExpr.eval,ModExpr.top,hx,hy,hz] at hxy hyz ⊢
  exact Mode.le_trans hxy (by simpa [Mode.compose_assoc] using Mode.compose_le_right Mode.top hyz)

theorem FnIndexLe.of_submode {Δ m n} (h : Submode Δ m n) : FnIndexLe Δ m n :=
  h.trans (FnIndexLe.refl h.defined.2)

theorem FnIndexLe.postcompose {Δ m n s} (h : FnIndexLe Δ m n)
    (hs : Entails Δ (.defined s)) : FnIndexLe Δ (.compose m s) (.compose n s) := by
  apply Submode.valid
  intro η hη
  obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp (h.defined.1 η hη)
  obtain ⟨y,hy⟩ := Option.isSome_iff_exists.mp
    ((Entails.defined_compose_iff.mp h.defined.2).1 η hη)
  obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp (hs η hη)
  have hxy := h.denote hη
  simp [ModExpr.Below,ModExpr.eval,ModExpr.top,hx,hy,hz] at hxy ⊢
  simpa only [Mode.compose_assoc,Mode.compose_comm Mode.top z] using Mode.compose_le_right z hxy

def fnRow (Δ : Bounds) (H : Set CompareTy) (m : ModExpr) (x y z : CompareTy) : Prop :=
  z = .modal (.fn x y) m ∧ Carrier Δ H x ∧ Carrier Δ H y ∧ Carrier Δ H z ∧
    x.WellShaped Δ ∧ y.WellShaped Δ ∧ z.WellShaped Δ

theorem fnRow_mono {Δ H m n a b c x y z} (hmn : FnIndexLe Δ m n)
    (ha : fnRow Δ H m a b c) (hx : fnRow Δ H n x y z)
    (hxa : Derivation Δ H x a) (hby : Derivation Δ H b y) : Derivation Δ H c z := by
  obtain ⟨rfl,_,_,hc,_⟩ := ha
  obtain ⟨rfl,_,_,hz,_⟩ := hx
  exact .fn hc hz hxa hby hmn

def fnTable (Δ : Bounds) (H : Set CompareTy) (m : TotalIndex Δ) :
    BinaryTable (core Δ H) true false where
  entry := fnRow Δ H m.val
  left h := h.2.1
  right h := h.2.2.1
  output h := h.2.2.2.1
  left_shaped h := h.2.2.2.2.1
  right_shaped h := h.2.2.2.2.2.1
  output_shaped h := h.2.2.2.2.2.2
  mono := fnRow_mono (FnIndexLe.refl m.property)

def indexedFnTable (Δ : Bounds) (H : Set CompareTy) :
    IndexedBinaryTable (core Δ H) (TotalIndex Δ) true false where
  table := fnTable Δ H
  le m n := FnIndexLe Δ m.val n.val
  refl m := FnIndexLe.refl m.property
  trans := FnIndexLe.trans
  cross_mono := fnRow_mono

end ModalityInference.ComparisonRawHeadRestriction
