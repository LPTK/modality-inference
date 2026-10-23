import ModalityInference.Proofs.ComparisonRawCarrierRestriction

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

end ModalityInference.ComparisonRawCarrierRestriction
