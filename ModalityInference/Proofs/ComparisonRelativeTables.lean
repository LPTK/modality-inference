import ModalityInference.Proofs.ComparisonRelativeIntervals

/-! Order-compatible partial tables extend to Boolean powers without changing
any recorded row. Variance is retained in both arguments. -/
namespace ModalityInference.ComparisonRelativeTables

variable {A O : Type*}

def Direction (reverse : Bool) (x y : O → Bool) : Prop :=
  if reverse then y ≤ x else x ≤ y

theorem Direction.refl (p : Bool) (x : O → Bool) : Direction p x x := by
  cases p <;> exact le_refl _

theorem Direction.trans {p : Bool} {x y z : O → Bool}
    (hxy : Direction p x y) (hyz : Direction p y z) : Direction p x z := by
  cases p
  · exact le_trans hxy hyz
  · exact le_trans hyz hxy

structure Table (embed : A → O → Bool) (leftReverse rightReverse : Bool) where
  entry : A → A → A → Prop
  mono : ∀ {a b c x y z}, entry a b c → entry x y z →
    Direction leftReverse (embed a) (embed x) →
    Direction rightReverse (embed b) (embed y) → embed c ≤ embed z

namespace Table

variable {embed : A → O → Bool} {p q : Bool} (T : Table embed p q)

noncomputable def extend (x y : O → Bool) : O → Bool := fun o =>
  @decide (∃ a b c, T.entry a b c ∧ Direction p (embed a) x ∧
    Direction q (embed b) y ∧ embed c o = true) (Classical.propDecidable _)

theorem extend_mono {x x' y y' : O → Bool}
    (hx : Direction p x x') (hy : Direction q y y') :
    T.extend x y ≤ T.extend x' y' := by
  intro o
  apply Bool.le_iff_imp.mpr
  simp only [extend,decide_eq_true_eq]
  rintro ⟨a,b,c,ht,ha,hb,hc⟩
  exact ⟨a,b,c,ht,ha.trans hx,hb.trans hy,hc⟩

theorem extend_recorded {a b c : A} (ht : T.entry a b c) :
    T.extend (embed a) (embed b) = embed c := by
  funext o
  apply Bool.eq_iff_iff.mpr
  simp only [extend,decide_eq_true_eq]
  constructor
  · rintro ⟨x,y,z,hrow,hx,hy,hz⟩
    exact Bool.le_iff_imp.mp (T.mono hrow ht hx hy o) hz
  · intro hc
    exact ⟨a,b,c,ht,Direction.refl _ _,Direction.refl _ _,hc⟩

/-- The extension preserves every recorded row, including an infinite family
of defined rows; its codomain is finite whenever the observation set is finite. -/
theorem extension_exists :
    ∃ f : (O → Bool) → (O → Bool) → (O → Bool),
      (∀ x x' y y', Direction p x x' → Direction q y y' → f x y ≤ f x' y') ∧
      (∀ a b c, T.entry a b c → f (embed a) (embed b) = embed c) :=
  ⟨T.extend,fun _ _ _ _ => T.extend_mono,fun _ _ _ => T.extend_recorded⟩

end Table
/-- Ordered controls retain compatibility between different recorded tables. -/
structure IndexedTable (embed : A → O → Bool) (Index : Type*) (p q : Bool) where
  table : Index → Table embed p q
  le : Index → Index → Prop
  refl : ∀ m, le m m
  trans : ∀ {m n r}, le m n → le n r → le m r
  cross_mono : ∀ {m n a b c x y z}, le m n →
    (table m).entry a b c → (table n).entry x y z →
    Direction p (embed a) (embed x) → Direction q (embed b) (embed y) → embed c ≤ embed z

namespace IndexedTable

variable {embed : A → O → Bool} {Index : Type*} {p q : Bool}
  (T : IndexedTable embed Index p q)

noncomputable def extend (m : Index) (x y : O → Bool) : O → Bool := fun o =>
  @decide (∃ r a b c, T.le r m ∧ (T.table r).entry a b c ∧
    Direction p (embed a) x ∧ Direction q (embed b) y ∧ embed c o = true)
    (Classical.propDecidable _)

theorem extend_mono {m n : Index} {x x' y y' : O → Bool}
    (hmn : T.le m n) (hx : Direction p x x') (hy : Direction q y y') :
    T.extend m x y ≤ T.extend n x' y' := by
  intro o
  apply Bool.le_iff_imp.mpr
  simp only [extend,decide_eq_true_eq]
  rintro ⟨r,a,b,c,hr,ht,ha,hb,hc⟩
  exact ⟨r,a,b,c,T.trans hr hmn,ht,ha.trans hx,hb.trans hy,hc⟩

theorem extend_recorded {m : Index} {a b c : A} (ht : (T.table m).entry a b c) :
    T.extend m (embed a) (embed b) = embed c := by
  funext o
  apply Bool.eq_iff_iff.mpr
  simp only [extend,decide_eq_true_eq]
  constructor
  · rintro ⟨r,x,y,z,hr,hrow,hx,hy,hz⟩
    exact Bool.le_iff_imp.mp (T.cross_mono hr hrow ht hx hy o) hz
  · intro hc
    exact ⟨m,a,b,c,T.refl m,ht,Direction.refl _ _,Direction.refl _ _,hc⟩

end IndexedTable
end ModalityInference.ComparisonRelativeTables
