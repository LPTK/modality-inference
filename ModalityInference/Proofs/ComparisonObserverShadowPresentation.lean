import ModalityInference.Proofs.ComparisonObserverRangeTransfer
import ModalityInference.Proofs.ComparisonObserverShadowRows
import ModalityInference.Proofs.ComparisonRelativeIntervals

/-! A finite list of named observer values can retain its exact order in one
finite certified machine. Extra raw rows may impose the required modal,
constructor, and defined-anchor equations at the same time. -/
namespace ModalityInference.ComparisonObserverShadowPresentation

open ComparisonObserverGluing ComparisonObserverRangeTransfer
  ComparisonRelativeIntervals

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds}

def orderRows (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (vars : List TypeVar) : List (Ty × Ty) :=
  vars.flatMap fun v => (vars.filter fun w => decide (assign v ≤ assign w)).map
    fun w => (.var v,.var w)

theorem mem_orderRows {assign : TypeVar → ComparisonObserverRangeProduct.Value Δ}
    {vars : List TypeVar} {a b : Ty} :
    (a,b) ∈ orderRows assign vars ↔ ∃ v ∈ vars, ∃ w ∈ vars,
      assign v ≤ assign w ∧ a = .var v ∧ b = .var w := by
  simp only [orderRows,List.mem_flatMap,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨v,hv,w,⟨hw,hle⟩,h⟩
    cases h
    exact ⟨v,hv,w,hw,hle,rfl,rfl⟩
  · rintro ⟨v,hv,w,hw,hle,rfl,rfl⟩
    exact ⟨v,hv,w,⟨hw,hle⟩,rfl⟩

theorem var_defined (Δ : Bounds) (v : TypeVar) :
    (CompareTy.var v).DefinedUnder Δ := by
  intro η hη c hc
  exact False.elim (List.not_mem_nil hc)

theorem raw_var_defined (Δ : Bounds) (v : TypeVar) :
    (show Ty from .var v).DefinedUnder Δ := by
  intro η hη c hc
  exact False.elim (List.not_mem_nil hc)

theorem orderRows_defined (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (vars : List TypeVar) : ∀ p ∈ orderRows assign vars,
      p.1.DefinedUnder Δ ∧ p.2.DefinedUnder Δ := by
  rintro ⟨a,b⟩ h
  obtain ⟨v,_,w,_,_,rfl,rfl⟩ := mem_orderRows.mp h
  exact ⟨raw_var_defined Δ v,raw_var_defined Δ w⟩

theorem orderRows_sound (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (vars : List TypeVar) :
    ∀ p ∈ orderRows assign vars, ∀ g,
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.1) g ≤
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.2) g := by
  rintro ⟨a,b⟩ h
  obtain ⟨v,_,w,_,hle,rfl,rfl⟩ := mem_orderRows.mp h
  exact fun g => hle g

/-- All named comparisons are preserved and reflected, while every extra row
is certified throughout the resulting finite machine. -/
theorem finite_named_order (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (vars : List TypeVar)
    (extra : List (Ty × Ty))
    (hd : ∀ p ∈ extra, p.1.DefinedUnder Δ ∧ p.2.DefinedUnder Δ)
    (hr : ∀ p ∈ extra, ∀ g,
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.1) g ≤
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.2) g) :
    ∃ count ≤ ComparisonObserverBoundary.sizeBound
      (context Δ (orderRows assign vars ++ extra)) (vars.map CompareTy.var),
      ∃ machine : ComparisonObserverMachine.Machine count,
        ComparisonObserverMachine.Certified
          (context Δ (orderRows assign vars ++ extra)) machine ∧
        ∀ v ∈ vars, ∀ w ∈ vars,
          (∀ i, (machine i).atom v ≤ (machine i).atom w) ↔ assign v ≤ assign w := by
  obtain ⟨count,hcount,machine,hc,hcover⟩ := finite_rows hn assign
    (orderRows assign vars ++ extra)
    (fun p hp => (List.mem_append.mp hp).elim (orderRows_defined assign vars p) (hd p))
    (fun p hp => (List.mem_append.mp hp).elim (orderRows_sound hn assign vars p) (hr p))
    (vars.map CompareTy.var)
  refine ⟨count,hcount,machine,hc,?_⟩
  intro v hv w hw
  constructor
  · intro h g
    obtain ⟨i,hi⟩ := hcover g
    have hvi := hi (.var v) (List.mem_map.mpr ⟨v,hv,rfl⟩) (var_defined _ v)
    have hwi := hi (.var w) (List.mem_map.mpr ⟨w,hw,rfl⟩) (var_defined _ w)
    change (assign v g).val ≤ (assign w g).val
    change (machine i).atom v = (assign v g).val at hvi
    change (machine i).atom w = (assign w g).val at hwi
    rw [← hvi,← hwi]
    exact h i
  · intro h i
    apply hc.bounds i (.var v) (.var w)
    apply context_sub.mpr
    exact List.mem_append_left _ (mem_orderRows.mpr ⟨v,hv,w,hw,h,rfl,rfl⟩)

end
end ModalityInference.ComparisonObserverShadowPresentation
