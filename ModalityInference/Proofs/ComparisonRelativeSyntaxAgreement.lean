import ModalityInference.Proofs.ComparisonRelativeSyntaxDefined

/-! Recorded defined rows in the relative completion imply the primitive
defined-operation agreement used by full algebra soundness. -/
namespace ModalityInference.ComparisonRelativeSyntax

open ComparisonRelativeIntervals ComparisonRelativeCoordinates ComparisonFiniteControls
  ComparisonFiniteControlProjection ComparisonFiniteControlRange ComparisonObserverMachine
  ComparisonObserverFiniteRange ComparisonStructuralLayout

noncomputable section

variable {Δ : Bounds} {names : List ModVar} {State : Type} {nodes : State → Node State}
  {P : Type*} [Preorder P]
  (I : IntervalData (ComparisonObserverFiniteRange.Value nodes) P)
  (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes)

def definedOrbit : LatticeHom (ComparisonObserverFiniteRange.Value nodes)
    (Coordinates (Control Δ names) I.Completion) :=
  latticeOrbit I.definedEmbedding (action hv hr)
    (fun x => (OrderHomClass.mono I.definedEmbedding).comp (action_index hv hr x))

@[simp] theorem definedOrbit_apply (x : ComparisonObserverFiniteRange.Value nodes)
    (m : Control Δ names) :
    definedOrbit I hv hr x m = I.embed (.inl (action hv hr m x)) := rfl

theorem definedOrbit_reflect {x y : ComparisonObserverFiniteRange.Value nodes}
    (h : definedOrbit (names := names) I hv hr x ≤ definedOrbit I hv hr y) : x ≤ y := by
  have hh := h 1
  change I.definedEmbedding (action hv hr (1 : Control Δ names) x) ≤
    I.definedEmbedding (action hv hr (1 : Control Δ names) y) at hh
  rw [action_one hv hr x,action_one hv hr y] at hh
  exact (I.definedEmbedding_le_iff _ _).mp hh

theorem definedOrbit_shift (hmul : ∀ m : Control Δ names, Monotone (m * ·))
    (n : Control Δ names) (x : ComparisonObserverFiniteRange.Value nodes) :
    shift hmul n (definedOrbit I hv hr x) = definedOrbit I hv hr (action hv hr n x) := by
  ext m o
  exact congrFun (congrArg I.definedEmbedding (action_mul hv hr n m x)) o

/-- Every agreement field follows from a concrete recorded row or a finite
control identity. In particular, constructor agreement is not an extra axiom. -/
theorem agreement_of_defined_rows
    (S : Model Δ (Control Δ names) (ComparisonObserverFiniteRange.Value nodes ⊕ P)
      I.Observation I.embed)
    (hc : Coherent Δ nodes) (hnames : Δ.modVars ⊆ names.toFinset)
    (hcontrols : ∀ m hm, S.controls.toFun m hm = project hnames m hm)
    (hatom : ∀ v, S.atom v = definedOrbit I hv hr (atom hr v))
    (hunit : S.unit = definedOrbit I hv hr (unit hr))
    (hcredit : S.credit = definedOrbit I hv hr (credit hr))
    (hprod : ∀ m x y, ((S.prodTable none).table m).entry (.inl x) (.inl y)
      (.inl (action hv hr m (op hr .prod x y))))
    (hsum : ∀ m x y, ((S.sumTable none).table m).entry (.inl x) (.inl y)
      (.inl (action hv hr m (op hr .sum x y))))
    (hfn : ∀ m x y, (S.fnTable.table m).entry (.inl x) (.inl y)
      (.inl (action hv hr m (op hr .fn x y)))) :
    DefinedAgreement S hv hr hnames (definedOrbit I hv hr) where
  controls := hcontrols
  reflect := definedOrbit_reflect I hv hr
  atom := hatom
  unit := hunit
  credit := hcredit
  action := definedOrbit_shift I hv hr S.mul_mono
  prod x y := by
    ext m o
    change (S.prodTable none).extend m (I.embed (.inl (action hv hr m x)))
      (I.embed (.inl (action hv hr m y))) o = I.embed (.inl (action hv hr m (op hr .prod x y))) o
    rw [(S.prodTable none).extend_recorded (hprod m (action hv hr m x) (action hv hr m y)),
      action_pair_absorb hv hr hc .prod (Or.inl rfl) m x y]
  sum x y := by
    ext m o
    change (S.sumTable none).extend m (I.embed (.inl (action hv hr m x)))
      (I.embed (.inl (action hv hr m y))) o = I.embed (.inl (action hv hr m (op hr .sum x y))) o
    rw [(S.sumTable none).extend_recorded (hsum m (action hv hr m x) (action hv hr m y)),
      action_pair_absorb hv hr hc .sum (Or.inr rfl) m x y]
  fn x y := by
    ext m o
    change S.fnTable.extend m (I.embed (.inl (action hv hr (1 : Control Δ names) x)))
      (I.embed (.inl (action hv hr (1 : Control Δ names) y))) o =
        I.embed (.inl (action hv hr m (op hr .fn x y))) o
    rw [action_one hv hr x,action_one hv hr y,S.fnTable.extend_recorded (hfn m x y)]

end
end ModalityInference.ComparisonRelativeSyntax
