import ModalityInference.Proofs.ComparisonExecutableModelTransport
import ModalityInference.Proofs.ComparisonFiniteControlEncoding
import ModalityInference.Proofs.ComparisonRelativeSyntaxDefined

/-! Primitive agreement checked on finite control codes transfers to the
semantic-control model used by the original algebra soundness theorem. -/
namespace ModalityInference.ComparisonExecutableDefinedAgreement

open ComparisonRelativeCoordinates ComparisonRelativeSyntax ComparisonFiniteControls
  ComparisonObserverMachine ComparisonObserverFiniteRange ComparisonExecutableTableTransport

noncomputable section

variable {Δ : Bounds} {names : List ModVar} {State : Type} {nodes : State → Node State}
  {A O : Type*} {embed : A → O → Bool}
  (S : Model Δ (ComparisonFiniteControlEncoding.Code Δ names) A O embed)
  (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes)
  (hnames : Δ.modVars ⊆ names.toFinset)
  (j : LatticeHom (ComparisonObserverFiniteRange.Value nodes)
    (Coordinates (ComparisonFiniteControlEncoding.Code Δ names) (O → Bool)))

structure CodeDefinedAgreement : Prop where
  controls : ∀ m hm, S.controls.toFun m hm = ComparisonFiniteControlEncoding.project Δ names m
  reflect : ∀ {x y}, j x ≤ j y → x ≤ y
  atom : ∀ v, S.atom v = j (atom hr v)
  unit : S.unit = j (unit hr)
  credit : S.credit = j (credit hr)
  action : ∀ m x, shift S.mul_mono m (j x) =
    j (ComparisonFiniteControlRange.action hv hr (ComparisonFiniteControlEncoding.decode m) x)
  prod : ∀ x y, pair (S.prodTable none) (S.prod_order none) (j x) (j y) = j (op hr .prod x y)
  sum : ∀ x y, pair (S.sumTable none) (S.sum_order none) (j x) (j y) = j (op hr .sum x y)
  fn : ∀ x y, fn S.fnTable S.fn_order (j x) (j y) = j (op hr .fn x y)

theorem inverse_one (Δ : Bounds) (names : List ModVar) :
    (ComparisonFiniteControlEncoding.orderIso Δ names).symm 1 = 1 :=
  map_one (ComparisonFiniteControlEncoding.mulEquiv Δ names).symm

theorem inverse_mul (Δ : Bounds) (names : List ModVar) (m n : Control Δ names) :
    (ComparisonFiniteControlEncoding.orderIso Δ names).symm (m * n) =
      (ComparisonFiniteControlEncoding.orderIso Δ names).symm m *
        (ComparisonFiniteControlEncoding.orderIso Δ names).symm n :=
  map_mul (ComparisonFiniteControlEncoding.mulEquiv Δ names).symm m n

def semanticModel : Model Δ (Control Δ names) A O embed :=
  ComparisonExecutableModelTransport.transport S (ComparisonFiniteControlEncoding.orderIso Δ names).symm
    (inverse_one Δ names) (inverse_mul Δ names)

def semanticEmbedding : LatticeHom (ComparisonObserverFiniteRange.Value nodes) (Coordinates (Control Δ names) (O → Bool)) :=
  (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O)).comp j

theorem decode_inverse (m : Control Δ names) :
    ComparisonFiniteControlEncoding.decode ((ComparisonFiniteControlEncoding.orderIso Δ names).symm m) = m :=
  (ComparisonFiniteControlEncoding.orderIso Δ names).apply_symm_apply m

theorem CodeDefinedAgreement.definedAgreement (h : CodeDefinedAgreement S hv hr j) :
    DefinedAgreement (semanticModel S) hv hr hnames (semanticEmbedding j) where
  controls m hm := by
    change ComparisonFiniteControlEncoding.decode (S.controls.toFun m hm) =
      ComparisonFiniteControlProjection.project hnames m hm
    simpa only [h.controls] using ComparisonFiniteControlEncoding.decode_project hnames m hm
  reflect hh := h.reflect ((coordinates_le_iff
    (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O) _ _).mp hh)
  atom v := congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O)) (h.atom v)
  unit := congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O)) h.unit
  credit := congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O)) h.credit
  action m x := by
    have ht := coordinates_shift S.mul_mono (semanticModel S).mul_mono
      (ComparisonFiniteControlEncoding.orderIso Δ names).symm (inverse_mul Δ names) (Equiv.refl O) m (j x)
    exact ht.symm.trans (congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O))
      (by simpa only [decode_inverse] using h.action ((ComparisonFiniteControlEncoding.orderIso Δ names).symm m) x))
  prod x y := (coordinates_pair (S.prodTable none) (S.prod_order none)
    (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl A) (Equiv.refl O) (j x) (j y)).trans
      (congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O)) (h.prod x y))
  sum x y := (coordinates_pair (S.sumTable none) (S.sum_order none)
    (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl A) (Equiv.refl O) (j x) (j y)).trans
      (congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O)) (h.sum x y))
  fn x y := (coordinates_fn S.fnTable S.fn_order
    (ComparisonFiniteControlEncoding.orderIso Δ names).symm (inverse_one Δ names)
    (Equiv.refl A) (Equiv.refl O) (j x) (j y)).trans
      (congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names).symm (Equiv.refl O)) (h.fn x y))

include hnames in
theorem CodeDefinedAgreement.algebra_sound (h : CodeDefinedAgreement S hv hr j)
    (hb : ∀ a b, Constraint.sub a b ∈ Δ → S.Related (.ofTy a) (.ofTy b))
    {a b : CompareTy} (hab : AlgebraSubtype Δ a b) : S.Related a b :=
  (ComparisonExecutableModelTransport.related_iff S (ComparisonFiniteControlEncoding.orderIso Δ names).symm
    (inverse_one Δ names) (inverse_mul Δ names) a b).mp
    ((CodeDefinedAgreement.definedAgreement S hv hr hnames j h).algebra_sound
      (fun x y hxy => (ComparisonExecutableModelTransport.related_iff S
        (ComparisonFiniteControlEncoding.orderIso Δ names).symm (inverse_one Δ names) (inverse_mul Δ names)
        (.ofTy x) (.ofTy y)).mpr (hb x y hxy)) hab)

end
end ModalityInference.ComparisonExecutableDefinedAgreement
