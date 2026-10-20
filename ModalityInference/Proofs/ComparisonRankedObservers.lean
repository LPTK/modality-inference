import ModalityInference.Proofs.ComparisonRankedBasis
import ModalityInference.Proofs.ComparisonObserverMachineSerialization
import ModalityInference.Proofs.ComparisonObserverMachinePadding
import ModalityInference.Proofs.ComparisonObserverMachineEncoding

/-! A fixed finite generator boundary suffices for all its lattice polynomials
simultaneously. The observer bound depends on the chosen constructor rank, not
on the sizes of the finite polynomials later reconstructed at that rank. -/
namespace ModalityInference.ComparisonRankedObservers

open ComparisonAlgebra ComparisonControls ComparisonStructuralLattice
  ComparisonObserverBoundary ComparisonObserverMachine ComparisonObserverMachineCheck
  ComparisonObserverMachineSerialization ComparisonObserverMachinePadding

theorem lattice_value {Δ : Bounds} {generators : List CompareTy}
    {S : Type} (machine : S → Node S) (i : S)
    (f : LatticeHom (Order Δ .unit) Bool)
    (h : ∀a ∈ generators, value machine a i = booleanValue f a)
    {a : CompareTy} (ha : LatticeForm generators a) :
    value machine a i = booleanValue f a := by
  induction ha with
  | atom ha => exact h _ ha
  | join _ _ ih₁ ih₂ => simpa only [value, booleanValue_join] using congrArg₂ Bool.or ih₁ ih₂
  | meet _ _ ih₁ ih₂ => simpa only [value, booleanValue_meet] using congrArg₂ Bool.and ih₁ ih₂

/-- One checked machine simultaneously preserves every polynomial over the
given generators, for every genuine observer. Its size is independent of the
number of joins and meets in those polynomials. -/
theorem bounded_polynomials {Δ : Bounds}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (generators : List CompareTy) (hg : ∀a ∈ generators, a.DefinedUnder Δ) :
    ∃count ≤ sizeBound Δ generators,
      ∃data : Fin count → Description (Fin count),
        check Δ (retainedTypes Δ generators) (retainedModes Δ generators) data = true ∧
        ∀f : LatticeHom (Order Δ .unit) Bool, ∃i : Fin count,
          ∀a, LatticeForm generators a →
            value (nodes (retainedTypes Δ generators) (retainedModes Δ generators) data) a i =
              booleanValue f a := by
  obtain ⟨count,hcount,data,hdata,hcover⟩ := bounded_descriptions_on
    (show Δ.modVars ⊆ names Δ generators from Finset.subset_union_left) hn hΔ
    (retainedTypes Δ generators) (retainedModes Δ generators)
    (mem_retainedModes Δ generators) (boundary Δ generators)
    (closure_ports_closed _) (boundary_declared Δ generators)
    (boundary_support Δ generators)
    (fun a ha => (boundary_retained_support Δ generators a ha).mono
      (fun _ h => h) (fun _ _ => trivial))
  refine ⟨count,hcount,data,hdata,fun f => ?_⟩
  obtain ⟨i,hi⟩ := hcover f
  exact ⟨i,fun _ ha => lattice_value _ i f
    (fun a ha => hi a (boundary_query ha) (hg a ha)) ha⟩

/-- The same bound covers every defined, supported endpoint at the chosen
constructor rank, including endpoints with arbitrarily many lattice operations
and conditionally defined annotations. -/
theorem bounded_rank {Δ : Bounds}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (typeNames : List TypeVar) (modeNames : List ModVar) (rank : Nat) :
    let generators := (ComparisonRankedBasis.basis typeNames modeNames rank).types
    ∃count ≤ sizeBound Δ generators,
      ∃data : Fin count → Description (Fin count),
        check Δ (retainedTypes Δ generators) (retainedModes Δ generators) data = true ∧
        ∀f : LatticeHom (Order Δ .unit) Bool, ∃i : Fin count,
          ∀a, a.DefinedUnder Δ →
            ComparisonInterpolation.Supports (·∈typeNames) (·∈modeNames) a →
            ComparisonRankedBasis.rank a ≤ rank →
            value (nodes (retainedTypes Δ generators) (retainedModes Δ generators) data) a i =
              booleanValue f a := by
  obtain ⟨count,hcount,data,hdata,hcover⟩ := bounded_polynomials hn hΔ
    (ComparisonRankedBasis.basis typeNames modeNames rank).types
    (fun a ha => (ComparisonRankedBasis.types_representable hn typeNames modeNames rank a ha).2.1)
  refine ⟨count,hcount,data,hdata,fun f => ?_⟩
  obtain ⟨i,hi⟩ := hcover f
  refine ⟨i,fun a hd hs hr => ?_⟩
  obtain ⟨t,ht,htr,he⟩ := (ComparisonRankedBasis.normal_of_supported hn typeNames modeNames hd hs).mono hr
  have hq : Order.of (represented (ComparisonObserverGluing.representable hn hd)) =
      Order.of (represented htr) := Quotient.sound he
  exact (le_antisymm (checked_subtype hdata hΔ hd htr.2.1 he.1 i)
    (checked_subtype hdata hΔ htr.2.1 hd he.2 i)).trans
      ((hi t ht).trans ((booleanValue_represented f t htr).trans
        ((congrArg f hq.symm).trans
          (booleanValue_represented f a (ComparisonObserverGluing.representable hn hd)).symm)))

/-- At a fixed constructor rank, one input-computed machine size suffices to
refute every invalid supported comparison. No polynomial-size bound or finite
quotient of all types is assumed. -/
theorem counterexample_complete {Δ : Bounds}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (typeNames : List TypeVar) (modeNames : List ModVar) (rank : Nat)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hsa : ComparisonInterpolation.Supports (·∈typeNames) (·∈modeNames) a)
    (hsb : ComparisonInterpolation.Supports (·∈typeNames) (·∈modeNames) b)
    (hra : ComparisonRankedBasis.rank a ≤ rank) (hrb : ComparisonRankedBasis.rank b ≤ rank)
    (hab : ¬AlgebraSubtype Δ a b) :
    let generators := (ComparisonRankedBasis.basis typeNames modeNames rank).types
    ∃world, (ComparisonObserverMachineEncoding.counterexample Δ
      (retainedTypes Δ generators) (retainedModes Δ generators)
      (sizeBound Δ generators) a b).eval world = true := by
  obtain ⟨f,hfa,hfb⟩ := lattice_separator
    (show ¬Order.of (represented (ComparisonObserverGluing.representable hn ha)) ≤
      Order.of (represented (ComparisonObserverGluing.representable hn hb)) from hab)
  obtain ⟨count,hcount,data,hdata,hcover⟩ := bounded_rank hn hΔ typeNames modeNames rank
  obtain ⟨i,hi⟩ := hcover f
  exact (ComparisonObserverMachineEncoding.counterexample_satisfiable _ _ _ _ _ _).mpr
    ⟨pad hcount i data,(pad_check hcount i data Δ _ _).trans hdata,i.castLE hcount,
      (pad_value hcount i data _ _ a i).trans ((hi a ha hsa hra).trans
        ((booleanValue_represented f a (ComparisonObserverGluing.representable hn ha)).trans hfa)),
      (pad_value hcount i data _ _ b i).trans ((hi b hb hsb hrb).trans
        ((booleanValue_represented f b (ComparisonObserverGluing.representable hn hb)).trans hfb))⟩

theorem counterexample_correct {Δ : Bounds}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (typeNames : List TypeVar) (modeNames : List ModVar) (rank : Nat)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hsa : ComparisonInterpolation.Supports (·∈typeNames) (·∈modeNames) a)
    (hsb : ComparisonInterpolation.Supports (·∈typeNames) (·∈modeNames) b)
    (hra : ComparisonRankedBasis.rank a ≤ rank) (hrb : ComparisonRankedBasis.rank b ≤ rank) :
    let generators := (ComparisonRankedBasis.basis typeNames modeNames rank).types
    (∃world, (ComparisonObserverMachineEncoding.counterexample Δ
      (retainedTypes Δ generators) (retainedModes Δ generators)
      (sizeBound Δ generators) a b).eval world = true) ↔ ¬AlgebraSubtype Δ a b :=
  ⟨fun ⟨_,hw⟩ => ComparisonObserverMachineEncoding.counterexample_sound hΔ ha hb hw,
    counterexample_complete hn hΔ typeNames modeNames rank ha hb hsa hsb hra hrb⟩

theorem subtype_iff_machines {Δ : Bounds}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (typeNames : List TypeVar) (modeNames : List ModVar) (rank : Nat)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hsa : ComparisonInterpolation.Supports (·∈typeNames) (·∈modeNames) a)
    (hsb : ComparisonInterpolation.Supports (·∈typeNames) (·∈modeNames) b)
    (hra : ComparisonRankedBasis.rank a ≤ rank) (hrb : ComparisonRankedBasis.rank b ≤ rank) :
    let generators := (ComparisonRankedBasis.basis typeNames modeNames rank).types
    let types := retainedTypes Δ generators
    let modes := retainedModes Δ generators
    let count := sizeBound Δ generators
    AlgebraSubtype Δ a b ↔
      ∀data : Fin count → Description (Fin count), check Δ types modes data = true →
        ∀i, value (nodes types modes data) a i ≤ value (nodes types modes data) b i := by
  refine ⟨fun hab _ hd i => checked_subtype hd hΔ ha hb hab i,fun h => ?_⟩
  exact Classical.byContradiction fun hab =>
    let ⟨world,hw⟩ := counterexample_complete hn hΔ typeNames modeNames rank ha hb hsa hsb hra hrb hab
    let ⟨hc,i,hia,hib⟩ := (ComparisonObserverMachineEncoding.counterexample_eval _ _ _ _ a b world).mp hw
    Bool.noConfusion ((Bool.le_iff_imp.mp (h _ hc i) hia).symm.trans hib)

end ModalityInference.ComparisonRankedObservers
