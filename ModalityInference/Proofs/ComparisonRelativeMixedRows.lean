import ModalityInference.Proofs.ComparisonRelativeTables

/-! Defined constructor rows and finite interface rows form one monotone table
when their optional principal cuts satisfy the two variance-aware shadow rules. -/
namespace ModalityInference.ComparisonRelativeMixedRows

open ComparisonRelativeIntervals

section Relational

variable {D P : Type*} [Lattice D] [Preorder P]

def Direction {A : Type*} (rel : A → A → Prop) (reverse : Bool) (a b : A) : Prop :=
  if reverse then rel b a else rel a b

namespace IntervalData

variable (I : ComparisonRelativeIntervals.IntervalData D P)

/-- A defined input below a partial row uses its lower cut covariantly and
its upper cut contravariantly. -/
def lowerInput (reverse : Bool) (p : P) : Option D :=
  if reverse then I.upper p else I.lower p

/-- A partial input below a defined row uses the dual choice of cut. -/
def upperInput (reverse : Bool) (p : P) : Option D :=
  if reverse then I.lower p else I.upper p

theorem lower_witness {reverse a p}
    (h : Direction I.Rel reverse (.inl a) (.inr p)) :
    ∃ b, lowerInput I reverse p = some b ∧ Direction (· ≤ ·) reverse a b := by
  cases reverse <;> exact h

theorem upper_witness {reverse p a}
    (h : Direction I.Rel reverse (.inr p) (.inl a)) :
    ∃ b, upperInput I reverse p = some b ∧ Direction (· ≤ ·) reverse b a := by
  cases reverse <;> exact h

end IntervalData

inductive MixedRow (f : D → D → D) (rows : P → P → P → Prop) :
    D ⊕ P → D ⊕ P → D ⊕ P → Prop where
  | defined (a b : D) : MixedRow f rows (.inl a) (.inl b) (.inl (f a b))
  | boundary {a b c : P} : rows a b c → MixedRow f rows (.inr a) (.inr b) (.inr c)

/-- Only an existing pair of input cuts triggers a shadow obligation.
An absent cut requires no invented defined lower or upper bound. -/
structure Compatibility (I : ComparisonRelativeIntervals.IntervalData D P)
    (leftReverse rightReverse : Bool) (f : D → D → D) (rows : P → P → P → Prop) : Prop where
  defined_mono : ∀ {a b x y}, Direction (· ≤ ·) leftReverse a x →
    Direction (· ≤ ·) rightReverse b y → f a b ≤ f x y
  partial_mono : ∀ {a b c x y z}, rows a b c → rows x y z →
    Direction (· ≤ ·) leftReverse a x → Direction (· ≤ ·) rightReverse b y → c ≤ z
  lower_shadow : ∀ {p q r a b}, rows p q r →
    IntervalData.lowerInput I leftReverse p = some a →
    IntervalData.lowerInput I rightReverse q = some b →
    ∃ c, I.lower r = some c ∧ f a b ≤ c
  upper_shadow : ∀ {p q r a b}, rows p q r →
    IntervalData.upperInput I leftReverse p = some a →
    IntervalData.upperInput I rightReverse q = some b →
    ∃ c, I.upper r = some c ∧ c ≤ f a b

namespace Compatibility

variable {I : ComparisonRelativeIntervals.IntervalData D P} {p q : Bool}
  {f : D → D → D} {rows : P → P → P → Prop} (h : Compatibility I p q f rows)

include h

theorem defined_partial {a b x y z} (hr : rows x y z)
    (ha : Direction I.Rel p (.inl a) (.inr x))
    (hb : Direction I.Rel q (.inl b) (.inr y)) :
    I.Rel (.inl (f a b)) (.inr z) := by
  obtain ⟨u,hu,hau⟩ := IntervalData.lower_witness I ha
  obtain ⟨v,hv,hbv⟩ := IntervalData.lower_witness I hb
  obtain ⟨w,hw,hfw⟩ := h.lower_shadow hr hu hv
  exact ⟨w,hw,(h.defined_mono hau hbv).trans hfw⟩

theorem partial_defined {x y z a b} (hr : rows x y z)
    (ha : Direction I.Rel p (.inr x) (.inl a))
    (hb : Direction I.Rel q (.inr y) (.inl b)) :
    I.Rel (.inr z) (.inl (f a b)) := by
  obtain ⟨u,hu,hua⟩ := IntervalData.upper_witness I ha
  obtain ⟨v,hv,hvb⟩ := IntervalData.upper_witness I hb
  obtain ⟨w,hw,hwf⟩ := h.upper_shadow hr hu hv
  exact ⟨w,hw,hwf.trans (h.defined_mono hua hvb)⟩

/-- The complete union of defined and interface rows is order-compatible. -/
theorem mono {a b c x y z} (habc : MixedRow f rows a b c) (hxyz : MixedRow f rows x y z)
    (hax : Direction I.Rel p a x) (hby : Direction I.Rel q b y) : I.Rel c z := by
  cases habc with
  | defined a b =>
    cases hxyz with
    | defined x y => exact h.defined_mono hax hby
    | boundary hr => exact h.defined_partial hr hax hby
  | boundary hr =>
    cases hxyz with
    | defined a b => exact h.partial_defined hr hax hby
    | boundary hs => exact h.partial_mono hr hs hax hby

end Compatibility
end Relational

section Embedding

variable {D P : Type*} [DistribLattice D] [Preorder P]
  {I : ComparisonRelativeIntervals.IntervalData D P} {p q : Bool}
  {f : D → D → D} {rows : P → P → P → Prop}

theorem embedded_direction_iff (reverse : Bool) (x y : D ⊕ P) :
    ComparisonRelativeTables.Direction reverse (I.embed x) (I.embed y) ↔
      Direction I.Rel reverse x y := by
  cases reverse <;> exact I.embed_le_iff _ _

namespace Compatibility

def table (h : Compatibility I p q f rows) : ComparisonRelativeTables.Table I.embed p q where
  entry := MixedRow f rows
  mono habc hxyz hax hby := (I.embed_le_iff _ _).mpr
    (h.mono habc hxyz ((embedded_direction_iff p _ _).mp hax)
      ((embedded_direction_iff q _ _).mp hby))

theorem extend_defined (h : Compatibility I p q f rows) (a b : D) :
    h.table.extend (I.embed (.inl a)) (I.embed (.inl b)) = I.embed (.inl (f a b)) :=
  h.table.extend_recorded (.defined a b)

theorem extend_partial (h : Compatibility I p q f rows) {a b c : P} (hr : rows a b c) :
    h.table.extend (I.embed (.inr a)) (I.embed (.inr b)) = I.embed (.inr c) :=
  h.table.extend_recorded (.boundary hr)

end Compatibility
end Embedding

end ModalityInference.ComparisonRelativeMixedRows
