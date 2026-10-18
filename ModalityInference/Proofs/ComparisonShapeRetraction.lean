import ModalityInference.Proofs.ComparisonUnanchoredProjection
import ModalityInference.Proofs.ComparisonSkeletonRebase

/-! Defined shape retractions retain selected subtrees literally and replace
unanchored leaves by an absorbing unit. Recursive constructor nodes carry the
local absence-of-anchors certificate used by structural projection. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeletonCoordinates
open ComparisonUnanchoredProjection

inductive Cut where
  | keep (shape : ComparisonShape)
  | erase (shape : ComparisonShape)
  | prod (left right : Cut)
  | sum (left right : Cut)
  | fn (domain codomain : Cut)

def Cut.source : Cut → ComparisonShape
  | .keep s | .erase s => s
  | .prod a b => .prod a.source b.source
  | .sum a b => .sum a.source b.source
  | .fn a b => .fn a.source b.source

def Cut.target : Cut → ComparisonShape
  | .keep s => s
  | .erase _ => .unit
  | .prod a b => .prod a.target b.target
  | .sum a b => .sum a.target b.target
  | .fn a b => .fn a.target b.target

def Cut.Valid (Δ : Bounds) (ρ : TypeVar → ComparisonShape) : Cut → Prop
  | .keep _ | .erase _ => True
  | .prod a b => Zone Δ ρ ((ComparisonShape.prod a.source b.source).subst ρ) ∧ a.Valid Δ ρ ∧ b.Valid Δ ρ
  | .sum a b => Zone Δ ρ ((ComparisonShape.sum a.source b.source).subst ρ) ∧ a.Valid Δ ρ ∧ b.Valid Δ ρ
  | .fn a b => Zone Δ ρ ((ComparisonShape.fn a.source b.source).subst ρ) ∧ a.Valid Δ ρ ∧ b.Valid Δ ρ

def absorbing (Δ : Bounds) : Carrier Δ .unit where
  type := .modal .unit (.const Mode.absorbing)
  shaped := trivial
  defined := by
    apply CompareTy.definedUnder_modal_iff.mpr
    constructor
    · intro η hη c hc
      cases hc
    · simp [Entails, ModExpr.WellFormed, ModExpr.eval]
  shape_eq := .refl

def pair (isSum : Bool) {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) (m : GuardedMode Δ) :
    Carrier Δ ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t) where
  type := .modal ((if isSum then CompareTy.sum else CompareTy.prod) a.type b.type) m.expression
  shaped := by cases isSum <;> exact ⟨a.shaped, b.shaped⟩
  defined := by
    apply CompareTy.definedUnder_modal_iff.mpr
    cases isSum
    · exact ⟨CompareTy.definedUnder_prod_iff.mpr ⟨a.defined, b.defined⟩, m.defined⟩
    · exact ⟨CompareTy.definedUnder_sum_iff.mpr ⟨a.defined, b.defined⟩, m.defined⟩
  shape_eq := by
    intro φ hφ
    cases isSum <;> simp only [Bool.false_eq_true, if_false, if_true, CompareTy.shape,
      ComparisonShape.subst, a.shape_eq φ hφ, b.shape_eq φ hφ]

def function {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) (m : GuardedMode Δ) : Carrier Δ (.fn s t) where
  type := .modal (.fn a.type b.type) m.expression
  shaped := ⟨a.shaped, b.shaped⟩
  defined := CompareTy.definedUnder_modal_iff.mpr
    ⟨CompareTy.definedUnder_fn_iff.mpr ⟨a.defined, b.defined⟩, m.defined⟩
  shape_eq := by
    intro φ hφ
    simp only [CompareTy.shape, ComparisonShape.subst, a.shape_eq φ hφ, b.shape_eq φ hφ]

def pairLeft {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (isSum : Bool) (hz : Zone Δ ρ (((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t).subst ρ))
    (a : Carrier Δ ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t)) : Carrier Δ s := by
  have hr := pairRoot_of_resolved hz a.shaped isSum
    (by cases isSum <;> rfl) (a.shape_eq ρ hz.models)
  exact ⟨pairChild false a.type, pairChild_shaped hr a.shaped false,
    pairChild_defined hr a.defined false, (Normalization.pairShapes hr a.shape_eq).1⟩

def pairRight {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (isSum : Bool) (hz : Zone Δ ρ (((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t).subst ρ))
    (a : Carrier Δ ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t)) : Carrier Δ t := by
  have hr := pairRoot_of_resolved hz a.shaped isSum
    (by cases isSum <;> rfl) (a.shape_eq ρ hz.models)
  exact ⟨pairChild true a.type, pairChild_shaped hr a.shaped true,
    pairChild_defined hr a.defined true, (Normalization.pairShapes hr a.shape_eq).2⟩

def functionDomain {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (hz : Zone Δ ρ ((ComparisonShape.fn s t).subst ρ)) (a : Carrier Δ (.fn s t)) : Carrier Δ s := by
  have hr := functionRoot_of_resolved hz a.shaped rfl (a.shape_eq ρ hz.models)
  exact ⟨fnChild true a.type, fnChild_shaped hr a.shaped true,
    fnChild_defined hr a.defined true, (Normalization.fnShapes hr a.shape_eq).1⟩

def functionCodomain {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (hz : Zone Δ ρ ((ComparisonShape.fn s t).subst ρ)) (a : Carrier Δ (.fn s t)) : Carrier Δ t := by
  have hr := functionRoot_of_resolved hz a.shaped rfl (a.shape_eq ρ hz.models)
  exact ⟨fnChild false a.type, fnChild_shaped hr a.shaped false,
    fnChild_defined hr a.defined false, (Normalization.fnShapes hr a.shape_eq).2⟩

def Cut.retract {Δ : Bounds} {ρ : TypeVar → ComparisonShape} :
    (c : Cut) → c.Valid Δ ρ → Carrier Δ c.source → Carrier Δ c.target
  | .keep _, _, a => a
  | .erase _, _, _ => absorbing Δ
  | .prod c d, h, a => pair false
      (c.retract h.2.1 (pairLeft false h.1 a))
      (d.retract h.2.2 (pairRight false h.1 a)) (rootGuarded a.type a.defined)
  | .sum c d, h, a => pair true
      (c.retract h.2.1 (pairLeft true h.1 a))
      (d.retract h.2.2 (pairRight true h.1 a)) (rootGuarded a.type a.defined)
  | .fn c d, h, a => function
      (c.retract h.2.1 (functionDomain h.1 a))
      (d.retract h.2.2 (functionCodomain h.1 a)) (rootGuarded a.type a.defined)


theorem pair_mono (isSum : Bool) {Δ : Bounds} {s t : ComparisonShape}
    {a c : Carrier Δ s} {b d : Carrier Δ t} {m n : GuardedMode Δ}
    (ha : a ≤ c) (hb : b ≤ d) (hm : Scalar.le m n) : pair isSum a b m ≤ pair isSum c d n := by
  have hmode := Scalar.submode (Scalar.refl m)
  have hmn := Scalar.submode hm
  cases isSum
  · exact (AlgebraSubtype.prod (.congr ha hmode) (.congr hb hmode)).trans
      (.congr (.refl ⟨c.shaped, d.shaped⟩) hmn)
  · exact (AlgebraSubtype.sum (.congr ha hmode) (.congr hb hmode)).trans
      (.congr (.refl ⟨c.shaped, d.shaped⟩) hmn)

theorem function_mono {Δ : Bounds} {s t : ComparisonShape}
    {a c : Carrier Δ s} {b d : Carrier Δ t} {m n : GuardedMode Δ}
    (ha : c ≤ a) (hb : b ≤ d) (hm : Scalar.futureLe m n) : function a b m ≤ function c d n :=
  AlgebraSubtype.fn ha hb (Scalar.future_submode hm)

theorem pairLeft_mono {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (isSum : Bool) (hz : Zone Δ ρ (((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t).subst ρ))
    {a b : Carrier Δ ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t)}
    (h : a ≤ b) : pairLeft isSum hz a ≤ pairLeft isSum hz b :=
  ComparisonUnanchoredProjection.algebra_pairChild (isSum := isSum) hz (by cases isSum <;> rfl)
    h (a.shape_eq ρ hz.models) false

theorem pairRight_mono {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (isSum : Bool) (hz : Zone Δ ρ (((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t).subst ρ))
    {a b : Carrier Δ ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t)}
    (h : a ≤ b) : pairRight isSum hz a ≤ pairRight isSum hz b :=
  ComparisonUnanchoredProjection.algebra_pairChild (isSum := isSum) hz (by cases isSum <;> rfl)
    h (a.shape_eq ρ hz.models) true

theorem functionDomain_mono {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (hz : Zone Δ ρ ((ComparisonShape.fn s t).subst ρ)) {a b : Carrier Δ (.fn s t)}
    (h : a ≤ b) : functionDomain hz b ≤ functionDomain hz a :=
  ComparisonUnanchoredProjection.algebra_fnChild hz rfl h (a.shape_eq ρ hz.models) true

theorem functionCodomain_mono {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (hz : Zone Δ ρ ((ComparisonShape.fn s t).subst ρ)) {a b : Carrier Δ (.fn s t)}
    (h : a ≤ b) : functionCodomain hz a ≤ functionCodomain hz b :=
  ComparisonUnanchoredProjection.algebra_fnChild hz rfl h (a.shape_eq ρ hz.models) false


@[simp] theorem pairLeft_act {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (isSum : Bool) (hz : Zone Δ ρ (((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t).subst ρ))
    (a : Carrier Δ ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t))
    (m : GuardedMode Δ) : pairLeft isSum hz (m.act a) = m.act (pairLeft isSum hz a) := rfl

@[simp] theorem pairRight_act {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (isSum : Bool) (hz : Zone Δ ρ (((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t).subst ρ))
    (a : Carrier Δ ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t))
    (m : GuardedMode Δ) : pairRight isSum hz (m.act a) = m.act (pairRight isSum hz a) := rfl

@[simp] theorem functionDomain_act {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (hz : Zone Δ ρ ((ComparisonShape.fn s t).subst ρ)) (a : Carrier Δ (.fn s t))
    (m : GuardedMode Δ) : functionDomain hz (m.act a) = functionDomain hz a := rfl

@[simp] theorem functionCodomain_act {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (hz : Zone Δ ρ ((ComparisonShape.fn s t).subst ρ)) (a : Carrier Δ (.fn s t))
    (m : GuardedMode Δ) : functionCodomain hz (m.act a) = functionCodomain hz a := rfl

end ModalityInference.ComparisonShapeRetraction
