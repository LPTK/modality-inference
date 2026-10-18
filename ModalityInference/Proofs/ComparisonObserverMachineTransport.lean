import ModalityInference.Proofs.ComparisonObserverMachine

/-! Renaming finite observer states preserves their full semantic certificate. -/
namespace ModalityInference.ComparisonObserverMachine

def transport {S T : Type} (e : T ≃ S) (nodes : S → Node S) (i : T) : Node T where
  atom := (nodes (e i)).atom
  unitValue := (nodes (e i)).unitValue
  creditValue := (nodes (e i)).creditValue
  action := (nodes (e i)).action
  branch k := ⟨((nodes (e i)).branch k).left, e.symm ((nodes (e i)).branch k).next⟩
  range := (nodes (e i)).range

theorem transport_value {S T : Type} (e : T ≃ S) (nodes : S → Node S) (a : CompareTy) (i : T) :
    value (transport e nodes) a i = value nodes a (e i) := by
  induction a generalizing i <;> simp_all [value, ComparisonObserverMachine.transport]

theorem Certified.transport {S T : Type} (e : T ≃ S) {nodes : S → Node S} {Δ : Bounds}
    (h : Certified Δ nodes) : Certified Δ (transport e nodes) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨fun i => h.modal.monotone (e i), fun i => h.modal.epsilon (e i),
      fun i => h.modal.compose (e i), fun i => h.modal.join (e i),
      fun i => h.modal.meet (e i), fun i => h.modal.submode (e i)⟩
  · refine ⟨fun i => h.range.atom (e i), fun i => h.range.unit (e i),
      fun i => h.range.credit (e i), ?_, fun i => h.range.modal (e i)⟩
    intro i k x hx
    exact h.range.branch (e i) k x (by simpa only [ComparisonObserverMachine.transport, Equiv.apply_symm_apply] using hx)
  · constructor
    · intro i k hk m hm x hx
      simpa only [ComparisonObserverMachine.transport, Equiv.apply_symm_apply] using h.coherent.pair (e i) k hk m hm x
        (by simpa only [ComparisonObserverMachine.transport, Equiv.apply_symm_apply] using hx)
    · intro i m n hm x hx
      simpa only [ComparisonObserverMachine.transport, Equiv.apply_symm_apply] using h.coherent.fn (e i) m n hm x
        (by simpa only [ComparisonObserverMachine.transport, Equiv.apply_symm_apply] using hx)
  · intro i a b hab
    simpa only [transport_value] using h.bounds (e i) a b hab

end ModalityInference.ComparisonObserverMachine
