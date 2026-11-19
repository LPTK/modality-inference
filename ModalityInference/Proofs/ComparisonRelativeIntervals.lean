import ModalityInference.Proofs.ComparisonAlgebraOrder
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-! Relative order extensions by an interface with optional principal cuts.
An absent lower or upper cut does not introduce a defined bottom or top. -/
namespace ModalityInference.ComparisonRelativeIntervals

section Order

variable {D P : Type*} [Lattice D] [Preorder P]

structure IntervalData (D P : Type*) [Lattice D] [Preorder P] where
  lower : P → Option D
  upper : P → Option D
  consistent : ∀ p a b, lower p = some a → upper p = some b → a ≤ b
  lower_mono : ∀ {p q}, p ≤ q → ∀ {a}, lower p = some a →
    ∃ b, lower q = some b ∧ a ≤ b
  upper_mono : ∀ {p q}, p ≤ q → ∀ {b}, upper q = some b →
    ∃ a, upper p = some a ∧ a ≤ b
  saturated : ∀ p q a b, upper p = some a → lower q = some b → a ≤ b → p ≤ q

namespace IntervalData

variable (I : IntervalData D P)

def Rel : D ⊕ P → D ⊕ P → Prop
  | .inl a, .inl b => a ≤ b
  | .inl a, .inr p => ∃ b, I.lower p = some b ∧ a ≤ b
  | .inr p, .inl b => ∃ a, I.upper p = some a ∧ a ≤ b
  | .inr p, .inr q => p ≤ q

theorem rel_refl (x : D ⊕ P) : I.Rel x x := by
  cases x <;> exact le_refl _

theorem rel_trans {x y z : D ⊕ P} (hxy : I.Rel x y) (hyz : I.Rel y z) :
    I.Rel x z := by
  cases x <;> cases y <;> cases z <;> dsimp only [Rel] at *
  case inl.inl.inl | inr.inr.inr => exact hxy.trans hyz
  case inl.inl.inr => exact let ⟨a,ha,haz⟩ := hyz; ⟨a,ha,hxy.trans haz⟩
  case inl.inr.inl =>
    exact let ⟨a,ha,hxa⟩ := hxy; let ⟨b,hb,hbz⟩ := hyz;
      hxa.trans ((I.consistent _ a b ha hb).trans hbz)
  case inl.inr.inr =>
    exact let ⟨a,ha,hxa⟩ := hxy;
      let ⟨b,hb,hab⟩ := I.lower_mono hyz ha; ⟨b,hb,hxa.trans hab⟩
  case inr.inl.inl => exact let ⟨a,ha,hay⟩ := hxy; ⟨a,ha,hay.trans hyz⟩
  case inr.inl.inr =>
    exact let ⟨a,ha,hay⟩ := hxy; let ⟨b,hb,hyb⟩ := hyz;
      I.saturated _ _ a b ha hb (hay.trans hyb)
  case inr.inr.inl =>
    exact let ⟨b,hb,hbz⟩ := hyz;
      let ⟨a,ha,hab⟩ := I.upper_mono hxy hb; ⟨a,ha,hab.trans hbz⟩

theorem rel_sup_iff (a b : D) (z : D ⊕ P) :
    I.Rel (.inl (a ⊔ b)) z ↔ I.Rel (.inl a) z ∧ I.Rel (.inl b) z := by
  cases z with
  | inl c => exact sup_le_iff
  | inr p => cases h : I.lower p <;> simp [Rel,h,sup_le_iff]

theorem rel_inf_iff (x : D ⊕ P) (a b : D) :
    I.Rel x (.inl (a ⊓ b)) ↔ I.Rel x (.inl a) ∧ I.Rel x (.inl b) := by
  cases x with
  | inl c => exact le_inf_iff
  | inr p => cases h : I.upper p <;> simp [Rel,h,le_inf_iff]

def lowerValue (f : LatticeHom D Bool) (p : P) : Bool :=
  match I.lower p with | none => false | some a => f a

def upperValue (f : LatticeHom D Bool) (p : P) : Bool :=
  match I.upper p with | none => true | some a => f a

theorem lowerValue_mono (f : LatticeHom D Bool) : Monotone (I.lowerValue f) := by
  intro p q hpq
  cases h : I.lower p with
  | none => simp [lowerValue,h]
  | some a =>
    obtain ⟨b,hb,hab⟩ := I.lower_mono hpq h
    simpa only [lowerValue,h,hb] using (OrderHomClass.mono f) hab

theorem upperValue_mono (f : LatticeHom D Bool) : Monotone (I.upperValue f) := by
  intro p q hpq
  cases h : I.upper q with
  | none => simp [upperValue,h]
  | some b =>
    obtain ⟨a,ha,hab⟩ := I.upper_mono hpq h
    simpa only [upperValue,h,ha] using (OrderHomClass.mono f) hab

theorem values_consistent (f : LatticeHom D Bool) (p : P) :
    I.lowerValue f p ≤ I.upperValue f p := by
  cases hl : I.lower p <;> cases hu : I.upper p <;> simp only [lowerValue,upperValue,hl,hu]
  all_goals first | exact bot_le | exact le_top | exact (OrderHomClass.mono f) (I.consistent _ _ _ hl hu)

structure Observation where
  defined : LatticeHom D Bool
  boundary : P → Bool
  partial_mono : Monotone boundary
  lower_le : ∀ p, I.lowerValue defined p ≤ boundary p
  le_upper : ∀ p, boundary p ≤ I.upperValue defined p

namespace Observation

variable {I}

def value (o : I.Observation) : D ⊕ P → Bool
  | .inl a => o.defined a
  | .inr p => o.boundary p

theorem value_mono (o : I.Observation) {x y : D ⊕ P} (h : I.Rel x y) :
    o.value x ≤ o.value y := by
  cases x <;> cases y
  case inl.inl => exact OrderHomClass.mono o.defined h
  case inr.inr => exact o.partial_mono h
  case inl.inr a p =>
    obtain ⟨b,hb,hab⟩ := h
    exact (OrderHomClass.mono o.defined hab).trans
      (by simpa only [lowerValue,hb] using o.lower_le p)
  case inr.inl p b =>
    obtain ⟨a,ha,hab⟩ := h
    exact (show o.boundary p ≤ o.defined a by simpa only [upperValue,ha] using o.le_upper p).trans
      (OrderHomClass.mono o.defined hab)

def lowerObservation (f : LatticeHom D Bool) : I.Observation where
  defined := f
  boundary := I.lowerValue f
  partial_mono := I.lowerValue_mono f
  lower_le _ := le_refl _
  le_upper := I.values_consistent f

def upperObservation (f : LatticeHom D Bool) : I.Observation where
  defined := f
  boundary := I.upperValue f
  partial_mono := I.upperValue_mono f
  lower_le := I.values_consistent f
  le_upper _ := le_refl _

noncomputable def pinned (f : LatticeHom D Bool) (p : P)
    (hp : I.upperValue f p = true) : I.Observation where
  defined := f
  boundary q := I.lowerValue f q ⊔ @decide (p ≤ q) (Classical.propDecidable _)
  partial_mono := by
    intro a b hab
    apply sup_le_sup (I.lowerValue_mono f hab)
    by_cases h : p ≤ a
    · simp [h,h.trans hab]
    · simp [h]
  lower_le _ := le_sup_left
  le_upper := by
    intro q
    apply sup_le (I.values_consistent f q)
    by_cases h : p ≤ q
    · simpa only [h,decide_true,hp] using I.upperValue_mono f h
    · simp [h]

theorem ext {a b : I.Observation} (hd : a.defined = b.defined) (hp : a.boundary = b.boundary) : a = b := by
  cases a; cases b; cases hd; cases hp; rfl

instance [Finite D] [Finite P] : Finite I.Observation := by
  classical
  letI := Fintype.ofFinite D
  letI := Fintype.ofFinite P
  exact Finite.of_injective (fun o : I.Observation => ((o.defined : D → Bool),o.boundary))
    (fun _ _ h => ext (DFunLike.coe_injective (congrArg Prod.fst h)) (congrArg Prod.snd h))

end Observation
def constant (b : Bool) : LatticeHom D Bool where
  toFun _ := b
  map_sup' _ _ := (sup_idem _).symm
  map_inf' _ _ := (inf_idem _).symm

end IntervalData
end Order

section Separation

variable {D P : Type*} [DistribLattice D] [Preorder P]

namespace IntervalData

variable (I : IntervalData D P)

theorem boundary_separator {p q : P} (hpq : ¬p ≤ q) :
    ∃ o : I.Observation, o.value (.inr p) = true ∧ o.value (.inr q) = false := by
  classical
  cases hu : I.upper p with
  | none =>
    refine ⟨Observation.pinned (I := I) (constant false) p (by simp [upperValue,hu]), ?_, ?_⟩
    · simp [Observation.value,Observation.pinned]
    · cases hl : I.lower q <;> simp [Observation.value,Observation.pinned,lowerValue,hl,constant,hpq]
  | some a =>
    cases hl : I.lower q with
    | none =>
      refine ⟨Observation.pinned (I := I) (constant true) p (by simp [upperValue,hu,constant]), ?_, ?_⟩
      · simp [Observation.value,Observation.pinned]
      · simp [Observation.value,Observation.pinned,lowerValue,hl,hpq]
    | some b =>
      obtain ⟨f,hfa,hfb⟩ := ComparisonAlgebra.lattice_separator
        (show ¬a ≤ b from fun h => hpq (I.saturated p q a b hu hl h))
      refine ⟨Observation.pinned (I := I) f p (by simp [upperValue,hu,hfa]), ?_, ?_⟩
      · simp [Observation.value,Observation.pinned]
      · simp [Observation.value,Observation.pinned,lowerValue,hl,hfb,hpq]

theorem separates {x y : D ⊕ P} (hxy : ¬I.Rel x y) :
    ∃ o : I.Observation, o.value x = true ∧ o.value y = false := by
  cases x <;> cases y
  case inr.inr p q => exact I.boundary_separator hxy
  case inl.inl a b =>
    obtain ⟨f,ha,hb⟩ := ComparisonAlgebra.lattice_separator hxy
    exact ⟨Observation.lowerObservation f,ha,hb⟩
  case inl.inr a p =>
    cases hl : I.lower p with
    | none =>
      exact ⟨Observation.lowerObservation (constant true),rfl,
        by simp [Observation.value,Observation.lowerObservation,lowerValue,hl]⟩
    | some b =>
      obtain ⟨f,ha,hb⟩ := ComparisonAlgebra.lattice_separator
        (show ¬a ≤ b from fun h => hxy ⟨b,hl,h⟩)
      exact ⟨Observation.lowerObservation f,ha,
        by simpa [Observation.value,Observation.lowerObservation,lowerValue,hl] using hb⟩
  case inr.inl p b =>
    cases hu : I.upper p with
    | none =>
      exact ⟨Observation.upperObservation (constant false),
        by simp [Observation.value,Observation.upperObservation,upperValue,hu],rfl⟩
    | some a =>
      obtain ⟨f,ha,hb⟩ := ComparisonAlgebra.lattice_separator
        (show ¬a ≤ b from fun h => hxy ⟨a,hu,h⟩)
      exact ⟨Observation.upperObservation f,
        by simpa [Observation.value,Observation.upperObservation,upperValue,hu] using ha,hb⟩

abbrev Completion := I.Observation → Bool

instance [Finite D] [Finite P] : Finite I.Completion := by
  classical
  letI := Fintype.ofFinite I.Observation
  infer_instance

def embed (x : D ⊕ P) : I.Completion := fun o => o.value x

theorem embed_le_iff (x y : D ⊕ P) : I.embed x ≤ I.embed y ↔ I.Rel x y := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨o,hx,hy⟩ := I.separates hn
    exact (by decide : ¬(true : Bool) ≤ false) (by simpa only [embed,hx,hy] using h o)
  · exact fun h o => o.value_mono h

def definedEmbedding : LatticeHom D I.Completion where
  toFun a := I.embed (.inl a)
  map_sup' a b := funext fun o => o.defined.map_sup' a b
  map_inf' a b := funext fun o => o.defined.map_inf' a b

theorem definedEmbedding_le_iff (a b : D) :
    I.definedEmbedding a ≤ I.definedEmbedding b ↔ a ≤ b :=
  I.embed_le_iff (.inl a) (.inl b)

theorem definedEmbedding_injective : Function.Injective I.definedEmbedding :=
  fun _ _ h => le_antisymm ((I.definedEmbedding_le_iff _ _).mp h.le)
    ((I.definedEmbedding_le_iff _ _).mp h.ge)

/-- A finite defined lattice and finite optional-cut interface have a finite
separating distributive extension preserving every defined meet and join.
This theorem does not construct the cut data from an unbounded algebra. -/
theorem finite_representation [Finite D] [Finite P] :
    Finite I.Completion ∧
    (∀ x y, I.embed x ≤ I.embed y ↔ I.Rel x y) ∧
    Function.Injective I.definedEmbedding :=
  ⟨inferInstance,I.embed_le_iff,I.definedEmbedding_injective⟩

end IntervalData
end Separation
end ModalityInference.ComparisonRelativeIntervals
