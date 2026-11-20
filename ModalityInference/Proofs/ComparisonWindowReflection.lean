import ModalityInference.Proofs.ComparisonWindowObservers

/-! Fixed-endpoint reflection in the observer domain of a prepared input. The
checked separator keeps the input name tables and honors every declared edge. -/
namespace ModalityInference.ComparisonWindowReflection

open ComparisonWindowObservers ComparisonObserverBoundary ComparisonInterpolation
  ComparisonObserverMachine ComparisonObserverMachineSerialization ComparisonAlgebra ComparisonControls
  ComparisonStructuralLattice

private theorem scope_boundary (Δ : Bounds) (typeNames : List TypeVar) (modeNames : List ModVar)
    (ht : Δ.typeVars ⊆ typeNames.toFinset) (hm : Δ.modVars ⊆ modeNames.toFinset)
    (qs : List CompareTy) (hq : ∀ q ∈ qs, Supports (· ∈ typeNames) (· ∈ modeNames) q) :
    ∀ q ∈ boundary Δ qs, Supports (· ∈ typeNames) (· ∈ modeNames) q := by
  apply closure_support
  intro q h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨c, hc, hq⟩ := List.mem_flatMap.mp h
    cases c <;> simp only [List.not_mem_nil] at hq
    case sub a b =>
      have types_mem : a.typeVars ∪ b.typeVars ⊆ typeNames.toFinset :=
        fun _ e => ht ((Δ.mem_typeVars_iff _).mpr ⟨.sub a b, hc, e⟩)
      have modes_mem : a.modVars ∪ b.modVars ⊆ modeNames.toFinset :=
        fun _ e => hm ((Δ.mem_modVars_iff _).mpr ⟨.sub a b, hc, e⟩)
      obtain rfl | hq := List.mem_cons.mp hq
      · exact ComparisonStructuralEndpoints.ofTy_supported a
          (fun _ hv => List.mem_toFinset.mp (types_mem (Finset.mem_union_left _ hv)))
          (fun _ hv => List.mem_toFinset.mp (modes_mem (Finset.mem_union_left _ hv)))
      · cases List.mem_singleton.mp hq
        exact ComparisonStructuralEndpoints.ofTy_supported b
          (fun _ hv => List.mem_toFinset.mp (types_mem (Finset.mem_union_right _ hv)))
          (fun _ hv => List.mem_toFinset.mp (modes_mem (Finset.mem_union_right _ hv)))
  · exact hq q h

theorem subtype_iff_observers {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Δ.TypeBoundsDefined) (types : List TypeVar) (modes : List ModVar)
    (ht : Δ.typeVars ⊆ types.toFinset) (hm : Δ.modVars ⊆ modes.toFinset)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hsa : Supports (· ∈ types) (· ∈ modes) a) (hsb : Supports (· ∈ types) (· ∈ modes) b) :
    AlgebraSubtype Δ a b ↔ ∀ t : Observer Δ types modes,
      value (observerNodes Δ types modes) a t ≤ value (observerNodes Δ types modes) b t := by
  constructor
  · intro h t
    have hC := certified Δ types modes
    exact subtype_mono hC.modal hC.range hC.coherent hC.bounds hΔ ha hb h t
  · intro obs
    by_contra h
    have scope := scope_boundary Δ types modes ht hm [a,b] (by simpa using And.intro hsa hsb)
    obtain ⟨_, _, data, hd, all⟩ := bounded_descriptions_on hm hn hΔ types modes
      (fun _ => List.mem_toFinset.symm) (boundary Δ [a,b]) (closure_ports_closed _)
      (boundary_declared Δ [a,b])
      (fun q hq => (scope q hq).mono (fun _ _ => trivial) (fun _ e => List.mem_toFinset.mpr e))
      (fun q hq => (scope q hq).mono (fun _ e => e) (fun _ _ => trivial))
    obtain ⟨f,htf,hff⟩ := lattice_separator
      (show ¬ Order.of (represented (ComparisonObserverGluing.representable hn ha)) ≤
        Order.of (represented (ComparisonObserverGluing.representable hn hb)) from h)
    obtain ⟨i, hi⟩ := all f
    have e := obs (embed hd i)
    rw [embed_value, embed_value, hi a (boundary_query (by simp)) ha,
      hi b (boundary_query (by simp)) hb,
      booleanValue_represented f a (ComparisonObserverGluing.representable hn ha),
      booleanValue_represented f b (ComparisonObserverGluing.representable hn hb),
      htf, hff] at e
    exact (by decide : ¬ true ≤ false) e

end ModalityInference.ComparisonWindowReflection
