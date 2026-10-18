import ModalityInference.Proofs.ComparisonShapeRetractionLaws

/-! Shape cuts commute with public constructors up to algebraic identity.
Kept subtrees remain literal, and recursive cuts share their child images. -/
namespace ModalityInference.ComparisonShapeRetraction

open ComparisonAlgebra ComparisonStructuralProjection ComparisonSkeletonCoordinates
open ComparisonUnanchoredProjection

def barePair (isSum : Bool) {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) :
    Carrier Δ ((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t) where
  type := (if isSum then CompareTy.sum else CompareTy.prod) a.type b.type
  shaped := by cases isSum <;> exact ⟨a.shaped, b.shaped⟩
  defined := by
    cases isSum
    · exact CompareTy.definedUnder_prod_iff.mpr ⟨a.defined, b.defined⟩
    · exact CompareTy.definedUnder_sum_iff.mpr ⟨a.defined, b.defined⟩
  shape_eq := by
    intro φ hφ
    cases isSum <;> simp only [Bool.false_eq_true, if_false, if_true, CompareTy.shape,
      ComparisonShape.subst, a.shape_eq φ hφ, b.shape_eq φ hφ]

def bareFunction {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) : Carrier Δ (.fn s t) where
  type := .fn a.type b.type
  shaped := ⟨a.shaped, b.shaped⟩
  defined := CompareTy.definedUnder_fn_iff.mpr ⟨a.defined, b.defined⟩
  shape_eq := by
    intro φ hφ
    simp only [CompareTy.shape, ComparisonShape.subst, a.shape_eq φ hφ, b.shape_eq φ hφ]

@[simp] theorem pairLeft_barePair {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (isSum : Bool) (hz : Zone Δ ρ (((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t).subst ρ))
    (a : Carrier Δ s) (b : Carrier Δ t) : pairLeft isSum hz (barePair isSum a b) = a := by
  cases isSum <;> rfl

@[simp] theorem pairRight_barePair {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (isSum : Bool) (hz : Zone Δ ρ (((if isSum then ComparisonShape.sum else ComparisonShape.prod) s t).subst ρ))
    (a : Carrier Δ s) (b : Carrier Δ t) : pairRight isSum hz (barePair isSum a b) = b := by
  cases isSum <;> rfl

@[simp] theorem functionDomain_bareFunction {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (hz : Zone Δ ρ ((ComparisonShape.fn s t).subst ρ)) (a : Carrier Δ s) (b : Carrier Δ t) :
    functionDomain hz (bareFunction a b) = a := rfl

@[simp] theorem functionCodomain_bareFunction {Δ : Bounds} {ρ : TypeVar → ComparisonShape} {s t : ComparisonShape}
    (hz : Zone Δ ρ ((ComparisonShape.fn s t).subst ρ)) (a : Carrier Δ s) (b : Carrier Δ t) :
    functionCodomain hz (bareFunction a b) = b := rfl

@[simp] theorem rootGuarded_barePair {Δ : Bounds} {s t : ComparisonShape}
    (isSum : Bool) (a : Carrier Δ s) (b : Carrier Δ t) :
    rootGuarded (barePair isSum a b).type (barePair isSum a b).defined = Scalar.identity := by
  cases isSum <;> rfl

@[simp] theorem rootGuarded_bareFunction {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) :
    rootGuarded (bareFunction a b).type (bareFunction a b).defined = Scalar.identity := rfl

@[simp] theorem Cut.retract_keep {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {s : ComparisonShape} (hc : (Cut.keep s).Valid Δ ρ) (a : Carrier Δ s) :
    (Cut.keep s).retract hc a = a := rfl

theorem pair_identity {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    (a : Carrier Δ s) (b : Carrier Δ t) :
    pair isSum a b Scalar.identity ≤ barePair isSum a b ∧
      barePair isSum a b ≤ pair isSum a b Scalar.identity := by
  cases isSum
  · exact ⟨.shaped (.identity ⟨a.shaped, b.shaped⟩), .shaped (.identityRev ⟨a.shaped, b.shaped⟩)⟩
  · exact ⟨.shaped (.identity ⟨a.shaped, b.shaped⟩), .shaped (.identityRev ⟨a.shaped, b.shaped⟩)⟩

theorem function_identity {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) :
    function a b Scalar.identity ≤ bareFunction a b ∧
      bareFunction a b ≤ function a b Scalar.identity :=
  ⟨.shaped (.identity ⟨a.shaped, b.shaped⟩), .shaped (.identityRev ⟨a.shaped, b.shaped⟩)⟩

theorem Cut.retract_prod {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (c d : Cut) (hc : (Cut.prod c d).Valid Δ ρ)
    (a : Carrier Δ c.source) (b : Carrier Δ d.source) :
    (Cut.prod c d).retract hc (barePair false a b) ≤
      barePair false (c.retract hc.2.1 a) (d.retract hc.2.2 b) ∧
      barePair false (c.retract hc.2.1 a) (d.retract hc.2.2 b) ≤
        (Cut.prod c d).retract hc (barePair false a b) := by
  simpa only [Cut.retract, pairLeft_barePair, pairRight_barePair, rootGuarded_barePair] using
    pair_identity false (c.retract hc.2.1 a) (d.retract hc.2.2 b)

theorem Cut.retract_sum {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (c d : Cut) (hc : (Cut.sum c d).Valid Δ ρ)
    (a : Carrier Δ c.source) (b : Carrier Δ d.source) :
    (Cut.sum c d).retract hc (barePair true a b) ≤
      barePair true (c.retract hc.2.1 a) (d.retract hc.2.2 b) ∧
      barePair true (c.retract hc.2.1 a) (d.retract hc.2.2 b) ≤
        (Cut.sum c d).retract hc (barePair true a b) := by
  simpa only [Cut.retract, pairLeft_barePair, pairRight_barePair, rootGuarded_barePair] using
    pair_identity true (c.retract hc.2.1 a) (d.retract hc.2.2 b)

theorem Cut.retract_fn {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (c d : Cut) (hc : (Cut.fn c d).Valid Δ ρ)
    (a : Carrier Δ c.source) (b : Carrier Δ d.source) :
    (Cut.fn c d).retract hc (bareFunction a b) ≤
      bareFunction (c.retract hc.2.1 a) (d.retract hc.2.2 b) ∧
      bareFunction (c.retract hc.2.1 a) (d.retract hc.2.2 b) ≤
        (Cut.fn c d).retract hc (bareFunction a b) := by
  simpa only [Cut.retract, functionDomain_bareFunction, functionCodomain_bareFunction,
    rootGuarded_bareFunction] using
    function_identity (c.retract hc.2.1 a) (d.retract hc.2.2 b)

end ModalityInference.ComparisonShapeRetraction
