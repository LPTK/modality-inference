import ModalityInference.Proofs.ComparisonRawCarrierHeterogeneous

/-! Ideal interpretations of partial constructor tables. A table records only
supported input/output triples. Its carrier need not contain a constructor
application for every pair of supported arguments. Reflection holds at recorded
triples, including for a contravariant argument. -/
namespace ModalityInference.ComparisonRawCarrierIdeals

variable {Δ : Bounds} (C : Core Δ)

/-- An order-compatible partial graph; no totality or lattice-homomorphism
property is required of the constructor represented by this table. -/
structure BinaryTable (leftReverse rightReverse : Bool) where
  entry : CompareTy → CompareTy → CompareTy → Prop
  left : ∀ {a b c}, entry a b c → C.carrier a
  right : ∀ {a b c}, entry a b c → C.carrier b
  output : ∀ {a b c}, entry a b c → C.carrier c
  left_shaped : ∀ {a b c}, entry a b c → a.WellShaped Δ
  right_shaped : ∀ {a b c}, entry a b c → b.WellShaped Δ
  output_shaped : ∀ {a b c}, entry a b c → c.WellShaped Δ
  mono : ∀ {a b c x y z}, entry a b c → entry x y z →
    Direction C leftReverse a x → Direction C rightReverse b y → C.le c z

namespace BinaryTable

variable {C} {p q : Bool} (T : BinaryTable C p q)

def image (S U : CompareTy → Prop) : CompareTy → Prop :=
  fun c => ∃ a b, S a ∧ U b ∧ T.entry a b c

def lower (S U : CompareTy → Prop) : LowerIdeal C :=
  .closure C (T.image S U)

def upper (S U : CompareTy → Prop) : UpperIdeal C :=
  .closure C (T.image S U)

theorem lower_mem {S U a b c} (h : T.entry a b c) (ha : S a) (hb : U b) :
    (T.lower S U).mem c :=
  .base (T.output h) (T.output_shaped h) ⟨a,b,ha,hb,h⟩

theorem upper_mem {S U a b c} (h : T.entry a b c) (ha : S a) (hb : U b) :
    (T.upper S U).mem c :=
  .base (T.output h) (T.output_shaped h) ⟨a,b,ha,hb,h⟩

theorem lower_mono {S S' U U' : CompareTy → Prop}
    (hS : ∀ a, S a → S' a) (hU : ∀ b, U b → U' b) {c}
    (hc : (T.lower S U).mem c) : (T.lower S' U').mem c := by
  apply LowerClosure.lift C hc (T.lower S' U')
  rintro _ ⟨a,b,ha,hb,ht⟩ _ _
  exact T.lower_mem ht (hS a ha) (hU b hb)

theorem upper_mono {S S' U U' : CompareTy → Prop}
    (hS : ∀ a, S a → S' a) (hU : ∀ b, U b → U' b) {c}
    (hc : (T.upper S U).mem c) : (T.upper S' U').mem c := by
  apply UpperClosure.lift C hc (T.upper S' U')
  rintro _ ⟨a,b,ha,hb,ht⟩ _ _
  exact T.upper_mem ht (hS a ha) (hU b hb)

theorem lower_sound {S U : CompareTy → Prop} {a b c}
    (ht : T.entry a b c)
    (hS : ∀ x, S x → Direction C p x a)
    (hU : ∀ y, U y → Direction C q y b) {z}
    (hz : (T.lower S U).mem z) : C.le z c := by
  apply LowerClosure.lift C hz (LowerIdeal.principal C c)
  rintro _ ⟨x,y,hx,hy,hxy⟩ _ _
  exact T.mono hxy ht (hS x hx) (hU y hy)

theorem upper_sound {S U : CompareTy → Prop} {a b c}
    (ht : T.entry a b c)
    (hS : ∀ x, S x → Direction C p a x)
    (hU : ∀ y, U y → Direction C q b y) {z}
    (hz : (T.upper S U).mem z) : C.le c z := by
  apply UpperClosure.lift C hz (UpperIdeal.principal C c)
  rintro _ ⟨x,y,hx,hy,hxy⟩ _ _
  exact T.mono ht hxy (hS x hx) (hU y hy)

theorem lower_principal {a b c} (ht : T.entry a b c) (z : CompareTy) :
    (T.lower (fun x => Direction C p x a) (fun y => Direction C q y b)).mem z ↔
      C.le z c := by
  constructor
  · exact T.lower_sound ht (fun _ h => h) (fun _ h => h)
  · intro hz
    apply (T.lower _ _).lower hz
    apply T.lower_mem ht
    · cases p <;> exact C.refl (T.left ht) (T.left_shaped ht)
    · cases q <;> exact C.refl (T.right ht) (T.right_shaped ht)

theorem upper_principal {a b c} (ht : T.entry a b c) (z : CompareTy) :
    (T.upper (fun x => Direction C p a x) (fun y => Direction C q b y)).mem z ↔
      C.le c z := by
  constructor
  · exact T.upper_sound ht (fun _ h => h) (fun _ h => h)
  · intro hz
    apply (T.upper _ _).upper hz
    apply T.upper_mem ht
    · cases p <;> exact C.refl (T.left ht) (T.left_shaped ht)
    · cases q <;> exact C.refl (T.right ht) (T.right_shaped ht)

end BinaryTable

/-- A sparse family with compatibility between rows at ordered indices.
No constructor totality or modal distribution over lattice operations is
required. The index preorder is supplied explicitly. -/
structure IndexedBinaryTable (Index : Type) (leftReverse rightReverse : Bool) where
  table : Index → BinaryTable C leftReverse rightReverse
  le : Index → Index → Prop
  refl : ∀ m, le m m
  trans : ∀ {m n r}, le m n → le n r → le m r
  cross_mono : ∀ {m n a b c x y z}, le m n →
    (table m).entry a b c → (table n).entry x y z →
    Direction C leftReverse a x → Direction C rightReverse b y → C.le c z

namespace IndexedBinaryTable

variable {C} {Index : Type} {p q : Bool} (T : IndexedBinaryTable C Index p q)

def lowerImage (m : Index) (S U : CompareTy → Prop) : CompareTy → Prop :=
  fun c => ∃ r, T.le r m ∧ (T.table r).image S U c

def upperImage (m : Index) (S U : CompareTy → Prop) : CompareTy → Prop :=
  fun c => ∃ r, T.le m r ∧ (T.table r).image S U c

def lower (m : Index) (S U : CompareTy → Prop) : LowerIdeal C :=
  .closure C (T.lowerImage m S U)

def upper (m : Index) (S U : CompareTy → Prop) : UpperIdeal C :=
  .closure C (T.upperImage m S U)

theorem lower_mem {m r S U a b c} (hr : T.le r m)
    (h : (T.table r).entry a b c) (ha : S a) (hb : U b) :
    (T.lower m S U).mem c :=
  .base ((T.table r).output h) ((T.table r).output_shaped h) ⟨r,hr,a,b,ha,hb,h⟩

theorem upper_mem {m r S U a b c} (hr : T.le m r)
    (h : (T.table r).entry a b c) (ha : S a) (hb : U b) :
    (T.upper m S U).mem c :=
  .base ((T.table r).output h) ((T.table r).output_shaped h) ⟨r,hr,a,b,ha,hb,h⟩

/-- Increasing the index preserves every lower witness, without changing its
annotation or lifting its operands inside a lower ideal. -/
theorem lower_mono {m n S S' U U'} (hmn : T.le m n)
    (hS : ∀ a, S a → S' a) (hU : ∀ b, U b → U' b) {c}
    (hc : (T.lower m S U).mem c) : (T.lower n S' U').mem c := by
  apply LowerClosure.lift C hc (T.lower n S' U')
  rintro _ ⟨r,hr,a,b,ha,hb,ht⟩ _ _
  exact T.lower_mem (T.trans hr hmn) ht (hS a ha) (hU b hb)

theorem upper_mono {m n S S' U U'} (hmn : T.le m n)
    (hS : ∀ a, S a → S' a) (hU : ∀ b, U b → U' b) {c}
    (hc : (T.upper n S U).mem c) : (T.upper m S' U').mem c := by
  apply UpperClosure.lift C hc (T.upper m S' U')
  rintro _ ⟨r,hr,a,b,ha,hb,ht⟩ _ _
  exact T.upper_mem (T.trans hmn hr) ht (hS a ha) (hU b hb)

theorem lower_sound {m S U a b c} (ht : (T.table m).entry a b c)
    (hS : ∀ x, S x → Direction C p x a)
    (hU : ∀ y, U y → Direction C q y b) {z}
    (hz : (T.lower m S U).mem z) : C.le z c := by
  apply LowerClosure.lift C hz (LowerIdeal.principal C c)
  rintro _ ⟨r,hr,x,y,hx,hy,hxy⟩ _ _
  exact T.cross_mono hr hxy ht (hS x hx) (hU y hy)

theorem upper_sound {m S U a b c} (ht : (T.table m).entry a b c)
    (hS : ∀ x, S x → Direction C p a x)
    (hU : ∀ y, U y → Direction C q b y) {z}
    (hz : (T.upper m S U).mem z) : C.le c z := by
  apply UpperClosure.lift C hz (UpperIdeal.principal C c)
  rintro _ ⟨r,hr,x,y,hx,hy,hxy⟩ _ _
  exact T.cross_mono hr ht hxy (hS x hx) (hU y hy)

theorem lower_principal {m a b c} (ht : (T.table m).entry a b c) (z : CompareTy) :
    (T.lower m (fun x => Direction C p x a) (fun y => Direction C q y b)).mem z ↔
      C.le z c := by
  constructor
  · exact T.lower_sound ht (fun _ h => h) (fun _ h => h)
  · intro hz
    apply (T.lower _ _ _).lower hz
    apply T.lower_mem (T.refl m) ht
    · cases p <;> exact C.refl ((T.table m).left ht) ((T.table m).left_shaped ht)
    · cases q <;> exact C.refl ((T.table m).right ht) ((T.table m).right_shaped ht)

theorem upper_principal {m a b c} (ht : (T.table m).entry a b c) (z : CompareTy) :
    (T.upper m (fun x => Direction C p a x) (fun y => Direction C q b y)).mem z ↔
      C.le c z := by
  constructor
  · exact T.upper_sound ht (fun _ h => h) (fun _ h => h)
  · intro hz
    apply (T.upper _ _ _).upper hz
    apply T.upper_mem (T.refl m) ht
    · cases p <;> exact C.refl ((T.table m).left ht) ((T.table m).left_shaped ht)
    · cases q <;> exact C.refl ((T.table m).right ht) ((T.table m).right_shaped ht)

end IndexedBinaryTable

end ModalityInference.ComparisonRawCarrierIdeals

namespace ModalityInference.ComparisonRawCarrierRestriction

open ComparisonRawCarrierIdeals

/-- Rows retain the common literal annotation and both of its operands. The
chosen output predicate may be sparse: no constructor-closure condition is
placed on it, and the annotation need not be defined. -/
def actedTable (Δ : Bounds) (K : Set Token) (op : CompareTy → CompareTy → CompareTy)
    (m : ModExpr) (keep : CompareTy → Prop)
    (rule : ∀ {a b c d}, Derivation Δ K (.modal a m) (.modal c m) →
      Derivation Δ K (.modal b m) (.modal d m) →
      Derivation Δ K (.modal (op a b) m) (.modal (op c d) m)) :
    BinaryTable (core Δ K) false false where
  entry x y z := ∃ a b, x = .modal a m ∧ y = .modal b m ∧ z = .modal (op a b) m ∧
    Carrier Δ K x ∧ Carrier Δ K y ∧ Carrier Δ K z ∧
    x.WellShaped Δ ∧ y.WellShaped Δ ∧ z.WellShaped Δ ∧ keep z
  left := by
    rintro _ _ _ ⟨a,b,rfl,rfl,rfl,ha,hb,hc,sa,sb,sc,hk⟩
    exact ha
  right := by
    rintro _ _ _ ⟨a,b,rfl,rfl,rfl,ha,hb,hc,sa,sb,sc,hk⟩
    exact hb
  output := by
    rintro _ _ _ ⟨a,b,rfl,rfl,rfl,ha,hb,hc,sa,sb,sc,hk⟩
    exact hc
  left_shaped := by
    rintro _ _ _ ⟨a,b,rfl,rfl,rfl,ha,hb,hc,sa,sb,sc,hk⟩
    exact sa
  right_shaped := by
    rintro _ _ _ ⟨a,b,rfl,rfl,rfl,ha,hb,hc,sa,sb,sc,hk⟩
    exact sb
  output_shaped := by
    rintro _ _ _ ⟨a,b,rfl,rfl,rfl,ha,hb,hc,sa,sb,sc,hk⟩
    exact sc
  mono := by
    rintro _ _ _ _ _ _ ⟨a,b,rfl,rfl,rfl,_⟩ ⟨c,d,rfl,rfl,rfl,_⟩ hac hbd
    exact rule hac hbd

def prodTable (Δ : Bounds) (K : Set Token) (m : ModExpr) (keep : CompareTy → Prop) :
    BinaryTable (core Δ K) false false :=
  actedTable Δ K .prod m keep Derivation.prod

def sumTable (Δ : Bounds) (K : Set Token) (m : ModExpr) (keep : CompareTy → Prop) :
    BinaryTable (core Δ K) false false :=
  actedTable Δ K .sum m keep Derivation.sum

abbrev TotalIndex (Δ : Bounds) := {m : ModExpr // Entails Δ (.defined m)}

/-- The output predicate remains arbitrary and may retain only input heads.
Cross-index compatibility is derived from the original structural rule. -/
def indexedActedTable (Δ : Bounds) (K : Set Token) (op : CompareTy → CompareTy → CompareTy)
    (keep : CompareTy → Prop)
    (rule : ∀ {a b c d m}, Derivation Δ K (.modal a m) (.modal c m) →
      Derivation Δ K (.modal b m) (.modal d m) →
      Derivation Δ K (.modal (op a b) m) (.modal (op c d) m)) :
    IndexedBinaryTable (core Δ K) (TotalIndex Δ) false false where
  table m := actedTable Δ K op m.val keep rule
  le m n := Submode Δ m.val n.val
  refl m := Submode.refl m.property
  trans := Submode.trans
  cross_mono := by
    rintro m n _ _ _ _ _ _ hmn ⟨a,b,rfl,rfl,rfl,_⟩ ⟨c,d,rfl,rfl,rfl,_⟩ hac hbd
    exact Derivation.inherited_ordered op rule hmn hac hbd

def indexedProdTable (Δ : Bounds) (K : Set Token) (keep : CompareTy → Prop) :
    IndexedBinaryTable (core Δ K) (TotalIndex Δ) false false :=
  indexedActedTable Δ K .prod keep Derivation.prod

def indexedSumTable (Δ : Bounds) (K : Set Token) (keep : CompareTy → Prop) :
    IndexedBinaryTable (core Δ K) (TotalIndex Δ) false false :=
  indexedActedTable Δ K .sum keep Derivation.sum

/-- Indexing only the outer total action also accommodates a fixed literal
partial prefix. Rows use the exact composition syntax `p.compose m`. -/
def indexedPrefixTable (Δ : Bounds) (K : Set Token) (op : CompareTy → CompareTy → CompareTy)
    (p : ModExpr) (keep : CompareTy → Prop)
    (rule : ∀ {a b c d m}, Derivation Δ K (.modal a m) (.modal c m) →
      Derivation Δ K (.modal b m) (.modal d m) →
      Derivation Δ K (.modal (op a b) m) (.modal (op c d) m)) :
    IndexedBinaryTable (core Δ K) (TotalIndex Δ) false false where
  table m := actedTable Δ K op (.compose p m.val) keep rule
  le m n := Submode Δ m.val n.val
  refl m := Submode.refl m.property
  trans := Submode.trans
  cross_mono := by
    rintro m n _ _ _ _ _ _ hmn ⟨a,b,rfl,rfl,rfl,_⟩ ⟨c,d,rfl,rfl,rfl,_⟩ hac hbd
    exact (Derivation.inherited_prefix_ordered op rule hmn
      hac.expand_modal hbd.expand_modal).flatten_modal

def indexedPrefixProdTable (Δ : Bounds) (K : Set Token) (p : ModExpr)
    (keep : CompareTy → Prop) : IndexedBinaryTable (core Δ K) (TotalIndex Δ) false false :=
  indexedPrefixTable Δ K .prod p keep Derivation.prod

def indexedPrefixSumTable (Δ : Bounds) (K : Set Token) (p : ModExpr)
    (keep : CompareTy → Prop) : IndexedBinaryTable (core Δ K) (TotalIndex Δ) false false :=
  indexedPrefixTable Δ K .sum p keep Derivation.sum

end ModalityInference.ComparisonRawCarrierRestriction
