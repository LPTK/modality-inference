import ModalityInference.Proofs.ComparisonExecutableDefinedAgreement
import ModalityInference.Proofs.ComparisonExecutableObservationTransport

/-! Source defined-algebra agreement is retained when semantic controls and
finite observations are replaced by their certificate indices. -/
namespace ModalityInference.ComparisonExecutableAgreementEncoding

open ComparisonRelativeCoordinates ComparisonRelativeSyntax ComparisonFiniteControls
  ComparisonObserverMachine ComparisonObserverFiniteRange ComparisonExecutableTableTransport
  ComparisonExecutableDefinedAgreement

noncomputable section

section Controls

variable {Δ : Bounds} {names : List ModVar} {State : Type} {nodes : State → Node State}
  {A O : Type*} {embed : A → O → Bool}
  (S : Model Δ (Control Δ names) A O embed)
  (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes)
  (hnames : Δ.modVars ⊆ names.toFinset)
  (j : LatticeHom (ComparisonObserverFiniteRange.Value nodes) (Coordinates (Control Δ names) (O → Bool)))

def encodeModel : Model Δ (ComparisonFiniteControlEncoding.Code Δ names) A O embed :=
  ComparisonExecutableModelTransport.transport S (ComparisonFiniteControlEncoding.orderIso Δ names)
    ComparisonFiniteControlEncoding.decode_one ComparisonFiniteControlEncoding.decode_mul

def encodeEmbedding : LatticeHom (ComparisonObserverFiniteRange.Value nodes)
    (Coordinates (ComparisonFiniteControlEncoding.Code Δ names) (O → Bool)) :=
  (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O)).comp j

theorem encode_agreement (h : DefinedAgreement S hv hr hnames j) :
    CodeDefinedAgreement (encodeModel S) hv hr (encodeEmbedding j) where
  controls m hm := (congrArg (ComparisonFiniteControlEncoding.orderIso Δ names).symm (h.controls m hm)).trans
    (ComparisonFiniteControlEncoding.decode_injective
      ((decode_inverse _).trans (ComparisonFiniteControlEncoding.decode_project hnames m hm).symm))
  reflect hh := h.reflect ((coordinates_le_iff
    (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O) _ _).mp hh)
  atom v := congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O)) (h.atom v)
  unit := congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O)) h.unit
  credit := congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O)) h.credit
  action m x := (coordinates_shift S.mul_mono (encodeModel S).mul_mono
    (ComparisonFiniteControlEncoding.orderIso Δ names) ComparisonFiniteControlEncoding.decode_mul
      (Equiv.refl O) m (j x)).symm.trans
        (congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O))
          (h.action (ComparisonFiniteControlEncoding.decode m) x))
  prod x y := (coordinates_pair (S.prodTable none) (S.prod_order none)
    (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl A) (Equiv.refl O) (j x) (j y)).trans
      (congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O)) (h.prod x y))
  sum x y := (coordinates_pair (S.sumTable none) (S.sum_order none)
    (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl A) (Equiv.refl O) (j x) (j y)).trans
      (congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O)) (h.sum x y))
  fn x y := (coordinates_fn S.fnTable S.fn_order
    (ComparisonFiniteControlEncoding.orderIso Δ names) ComparisonFiniteControlEncoding.decode_one
      (Equiv.refl A) (Equiv.refl O) (j x) (j y)).trans
        (congrArg (coordinates (ComparisonFiniteControlEncoding.orderIso Δ names) (Equiv.refl O)) (h.fn x y))

end Controls

section Observations

variable {Δ : Bounds} {names : List ModVar} {State : Type} {nodes : State → Node State}
  {A B O Q : Type*} {embed : A → O → Bool}
  (S : Model Δ (ComparisonFiniteControlEncoding.Code Δ names) A O embed)
  (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes)
  (j : LatticeHom (ComparisonObserverFiniteRange.Value nodes)
    (Coordinates (ComparisonFiniteControlEncoding.Code Δ names) (O → Bool)))

def observationEmbedding (eo : Q ≃ O) : LatticeHom (ComparisonObserverFiniteRange.Value nodes)
    (Coordinates (ComparisonFiniteControlEncoding.Code Δ names) (Q → Bool)) :=
  (coordinates (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo).comp j

theorem observations_agreement (h : CodeDefinedAgreement S hv hr j) (ea : B ≃ A) (eo : Q ≃ O) :
    CodeDefinedAgreement (ComparisonExecutableObservationTransport.transport S ea eo) hv hr
      (observationEmbedding j eo) where
  controls := h.controls
  reflect hh := h.reflect ((coordinates_le_iff
    (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo _ _).mp hh)
  atom v := congrArg (coordinates (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo) (h.atom v)
  unit := congrArg (coordinates (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo) h.unit
  credit := congrArg (coordinates (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo) h.credit
  action m x := (coordinates_shift S.mul_mono S.mul_mono
    (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) (fun _ _ => rfl) eo m (j x)).symm.trans
      (congrArg (coordinates (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo) (h.action m x))
  prod x y := (coordinates_pair (S.prodTable none) (S.prod_order none)
    (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) ea eo (j x) (j y)).trans
      (congrArg (coordinates (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo) (h.prod x y))
  sum x y := (coordinates_pair (S.sumTable none) (S.sum_order none)
    (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) ea eo (j x) (j y)).trans
      (congrArg (coordinates (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo) (h.sum x y))
  fn x y := (coordinates_fn S.fnTable S.fn_order
    (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) rfl ea eo (j x) (j y)).trans
      (congrArg (coordinates (OrderIso.refl (ComparisonFiniteControlEncoding.Code Δ names)) eo) (h.fn x y))

theorem change_nodes {nodes' : State → Node State} (he : nodes = nodes')
    (hv' : ModalValid Δ nodes') (hr' : RangeClosed Δ nodes') (h : CodeDefinedAgreement S hv hr j) :
    ∃ j' : LatticeHom (ComparisonObserverFiniteRange.Value nodes')
      (Coordinates (ComparisonFiniteControlEncoding.Code Δ names) (O → Bool)),
      CodeDefinedAgreement S hv' hr' j' := by
  cases he
  exact ⟨j,h⟩

end Observations
end
end ModalityInference.ComparisonExecutableAgreementEncoding
