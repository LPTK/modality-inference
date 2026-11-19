import ModalityInference.Proofs.ComparisonObserverMachine

/-! Observer-machine modal laws depend only on scalar models. Transporting these
laws does not transport the machine's declared type-bound certificate. -/
namespace ModalityInference.ComparisonObserverMachineModeTransport

open ComparisonObserverMachine

variable {State : Type} {Γ Δ : Bounds} {nodes : State → Node State}

theorem modal_valid (hmodels : ∀ η, ModeModels Γ η → ModeModels Δ η)
    (h : ModalValid Γ nodes) : ModalValid Δ nodes where
  monotone i m hm := h.monotone i m (fun η hη => hm η (hmodels η hη))
  epsilon := h.epsilon
  compose i m n hm hn := h.compose i m n
    (fun η hη => hm η (hmodels η hη)) (fun η hη => hn η (hmodels η hη))
  join i m n hm hn := h.join i m n
    (fun η hη => hm η (hmodels η hη)) (fun η hη => hn η (hmodels η hη))
  meet i m n hm hn := h.meet i m n
    (fun η hη => hm η (hmodels η hη)) (fun η hη => hn η (hmodels η hη))
  submode i m n hmn := h.submode i m n
    (.valid fun η hη => hmn.denote (hmodels η hη))

theorem range_closed (hmodels : ∀ η, ModeModels Γ η → ModeModels Δ η)
    (h : RangeClosed Γ nodes) : RangeClosed Δ nodes where
  atom := h.atom
  unit := h.unit
  credit := h.credit
  branch := h.branch
  modal i m hm := h.modal i m (fun η hη => hm η (hmodels η hη))

theorem coherent (hmodels : ∀ η, ModeModels Γ η → ModeModels Δ η)
    (h : Coherent Γ nodes) : Coherent Δ nodes where
  pair i k hk m hm := h.pair i k hk m (fun η hη => hm η (hmodels η hη))
  fn i m n hmn := h.fn i m n (.valid fun η hη => hmn.denote (hmodels η hη))

theorem certified_modes (hmodels : ∀ η, ModeModels Γ η → ModeModels Δ η)
    (h : Certified Γ nodes) :
    ModalValid Δ nodes ∧ RangeClosed Δ nodes ∧ Coherent Δ nodes :=
  ⟨modal_valid hmodels h.modal, range_closed hmodels h.range,
    coherent hmodels h.coherent⟩

end ModalityInference.ComparisonObserverMachineModeTransport
