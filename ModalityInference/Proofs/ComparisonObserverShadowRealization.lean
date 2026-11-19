import ModalityInference.Proofs.ComparisonObserverShadowPresentation
import ModalityInference.Proofs.ComparisonObserverFiniteRange

/-! Optional source cuts retain their flags and their exact named order in a
finite defined algebra. The resulting intervals are principal at the named
machine values, rather than at joins of approximated source cuts. -/
namespace ModalityInference.ComparisonObserverShadowPresentation

open ComparisonObserverRangeTransfer ComparisonRelativeIntervals

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} {P : Type*} [Preorder P]

structure NamedIntervals (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (P : Type*)
    [Preorder P] where
  lower : P → Option TypeVar
  upper : P → Option TypeVar
  consistent : ∀ p v w, lower p = some v → upper p = some w → assign v ≤ assign w
  lower_mono : ∀ {p q}, p ≤ q → ∀ {v}, lower p = some v →
    ∃ w, lower q = some w ∧ assign v ≤ assign w
  upper_mono : ∀ {p q}, p ≤ q → ∀ {w}, upper q = some w →
    ∃ v, upper p = some v ∧ assign v ≤ assign w
  saturated : ∀ p q v w, upper p = some v → lower q = some w →
    assign v ≤ assign w → p ≤ q

namespace NamedIntervals

variable {assign : TypeVar → ComparisonObserverRangeProduct.Value Δ}
    (S : NamedIntervals assign P) [Fintype P]

def shadowVars : List TypeVar :=
  Finset.univ.toList.flatMap fun p => (S.lower p).toList ++ (S.upper p).toList

theorem lower_mem {p : P} {v : TypeVar} (h : S.lower p = some v) : v ∈ S.shadowVars := by
  apply List.mem_flatMap.mpr
  exact ⟨p,Finset.mem_toList.mpr (Finset.mem_univ p),by simp [h]⟩

theorem upper_mem {p : P} {v : TypeVar} (h : S.upper p = some v) : v ∈ S.shadowVars := by
  apply List.mem_flatMap.mpr
  exact ⟨p,Finset.mem_toList.mpr (Finset.mem_univ p),by simp [h]⟩

def realize {D : Type*} [Lattice D] (value : TypeVar → D)
    (horder : ∀ v ∈ S.shadowVars, ∀ w ∈ S.shadowVars,
      value v ≤ value w ↔ assign v ≤ assign w) : IntervalData D P where
  lower p := (S.lower p).map value
  upper p := (S.upper p).map value
  consistent p a b ha hb := by
    obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨w,hw,rfl⟩ := Option.map_eq_some_iff.mp hb
    exact (horder v (S.lower_mem hv) w (S.upper_mem hw)).mpr (S.consistent p v w hv hw)
  lower_mono := by
    intro p q hpq a ha
    obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨w,hw,hle⟩ := S.lower_mono hpq hv
    exact ⟨value w,by simp [hw],(horder v (S.lower_mem hv) w (S.lower_mem hw)).mpr hle⟩
  upper_mono := by
    intro p q hpq b hb
    obtain ⟨w,hw,rfl⟩ := Option.map_eq_some_iff.mp hb
    obtain ⟨v,hv,hle⟩ := S.upper_mono hpq hw
    exact ⟨value v,by simp [hv],(horder v (S.upper_mem hv) w (S.upper_mem hw)).mpr hle⟩
  saturated p q a b ha hb hab := by
    obtain ⟨v,hv,rfl⟩ := Option.map_eq_some_iff.mp ha
    obtain ⟨w,hw,rfl⟩ := Option.map_eq_some_iff.mp hb
    exact S.saturated p q v w hv hw ((horder v (S.upper_mem hv) w (S.lower_mem hw)).mp hab)

/-- The optional interval diagram and every caller-supplied raw row coexist
in one finite range algebra, with the observer boundary's explicit bound. -/
theorem finite_realization (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (extra : List (Ty × Ty))
    (hd : ∀ p ∈ extra, p.1.DefinedUnder Δ ∧ p.2.DefinedUnder Δ)
    (hr : ∀ p ∈ extra, ∀ g,
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.1) g ≤
      ComparisonObserverMachine.value (nodes hn assign) (.ofTy p.2) g) :
    ∃ count ≤ ComparisonObserverBoundary.sizeBound
      (context Δ (orderRows assign S.shadowVars ++ extra)) (S.shadowVars.map CompareTy.var),
      ∃ machine : ComparisonObserverMachine.Machine count,
        ∃ hc : ComparisonObserverMachine.Certified
          (context Δ (orderRows assign S.shadowVars ++ extra)) machine,
        ∃ I : IntervalData (ComparisonObserverFiniteRange.Value machine) P,
          (∀ p, I.lower p = (S.lower p).map (ComparisonObserverFiniteRange.atom hc.range)) ∧
          (∀ p, I.upper p = (S.upper p).map (ComparisonObserverFiniteRange.atom hc.range)) ∧
          (∀ v ∈ S.shadowVars, ∀ w ∈ S.shadowVars,
            ComparisonObserverFiniteRange.atom hc.range v ≤
              ComparisonObserverFiniteRange.atom hc.range w ↔ assign v ≤ assign w) := by
  obtain ⟨count,hcount,machine,hc,horder⟩ := finite_named_order hn assign S.shadowVars extra hd hr
  have horder' : ∀ v ∈ S.shadowVars, ∀ w ∈ S.shadowVars,
      ComparisonObserverFiniteRange.atom hc.range v ≤
        ComparisonObserverFiniteRange.atom hc.range w ↔ assign v ≤ assign w := horder
  exact ⟨count,hcount,machine,hc,S.realize (ComparisonObserverFiniteRange.atom hc.range) horder',
    fun _ => rfl,fun _ => rfl,horder'⟩

end NamedIntervals
end
end ModalityInference.ComparisonObserverShadowPresentation
