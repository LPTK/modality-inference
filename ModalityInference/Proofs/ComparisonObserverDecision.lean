import ModalityInference.ComparisonObserverDecision
import ModalityInference.Proofs.ComparisonObserverMachineEncoding
import ModalityInference.Proofs.ComparisonObserverMachineSerialization
import ModalityInference.Proofs.ComparisonObserverMachinePadding
import ModalityInference.Proofs.BackendComplete

/-! Exact fixed-endpoint subtyping from the finite observer query. Context
shape recursion is allowed; every written type bound and endpoint retains its
original definedness guard. -/
namespace ModalityInference.ComparisonObserverDecision

open ComparisonAlgebra ComparisonObserverGluing ComparisonObserverBoundary
  ComparisonObserverMachineSerialization ComparisonObserverMachinePadding

/-- Any nonderivable defined comparison has a Boolean model of the actual
fixed-size counterexample formula. -/
theorem counterexample_complete {Δ : Bounds} {a b : CompareTy}
    (hn : ¬ ∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) (hab : ¬ AlgebraSubtype Δ a b) :
    ∃world, (counterexample Δ a b).eval world = true := by
  obtain ⟨count,hcount,data,hdata,hcover⟩ := bounded_descriptions_on
    (show Δ.modVars ⊆ names Δ [a,b] from Finset.subset_union_left) hn hΔ
    (retainedTypes Δ [a,b]) (retainedModes Δ [a,b]) (mem_retainedModes Δ [a,b])
    (boundary Δ [a,b]) (closure_ports_closed _) (boundary_declared Δ [a,b])
    (boundary_support Δ [a,b]) (fun t ht => (boundary_retained_support Δ [a,b] t ht).mono
      (fun _ h => h) (fun _ _ => trivial))
  obtain ⟨f,hfa,hfb⟩ := lattice_separator
    (show ¬ (Order.of (represented (representable hn ha))) ≤
      Order.of (represented (representable hn hb)) from hab)
  obtain ⟨i,hi⟩ := hcover f
  apply (ComparisonObserverMachineEncoding.counterexample_satisfiable Δ
    (retainedTypes Δ [a,b]) (retainedModes Δ [a,b]) (sizeBound Δ [a,b]) a b).mpr
  refine ⟨pad hcount i data, ?_, i.castLE hcount, ?_, ?_⟩
  · rw [pad_check]
    exact hdata
  · rw [pad_value, hi a (boundary_query (by simp)) ha,
      booleanValue_represented f a (representable hn ha)]
    exact hfa
  · rw [pad_value, hi b (boundary_query (by simp)) hb,
      booleanValue_represented f b (representable hn hb)]
    exact hfb

theorem counterexample_correct {Δ : Bounds} {a b : CompareTy}
    (hn : ¬ ∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    (∃world, (counterexample Δ a b).eval world = true) ↔ ¬ AlgebraSubtype Δ a b :=
  ⟨fun ⟨_,hw⟩ => ComparisonObserverMachineEncoding.counterexample_sound hΔ ha hb hw,
    counterexample_complete hn hΔ ha hb⟩

/-- The executable query is exact for original whole declared bounds, even
when their shape equations admit no finite shape model. -/
theorem query_valid {Δ : Bounds} {a b : CompareTy}
    (hn : ¬ ∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    (∀world, (query Δ a b).eval world = true) ↔ AlgebraSubtype Δ a b := by
  have he : (∀world, (query Δ a b).eval world = true) ↔
      ¬ ∃world, (counterexample Δ a b).eval world = true := by
    simp [query, BoolExpr.eval]
  rw [he, counterexample_correct hn hΔ ha hb, not_not]

theorem run_correct {fuel Δ a b report}
    (h : run fuel Δ a b = .success report)
    (hn : ¬ ∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    report.valid = true ↔ AlgebraSubtype Δ a b :=
  (ConcreteBackend.decideFormula_correct h).trans (query_valid hn hΔ ha hb)

theorem run_refutes {fuel Δ a b report}
    (h : run fuel Δ a b = .success report)
    (hn : ¬ ∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    report.valid = false ↔ ¬ AlgebraSubtype Δ a b := by
  rw [←run_correct h hn hΔ ha hb]
  cases report.valid <;> simp

/-- Normalization and Boolean validity checking eventually return one stable
report for every finite syntactic input, including negative decisions. -/
theorem run_complete (Δ : Bounds) (a b : CompareTy) :
    ∃threshold report, ∀fuel ≥ threshold, run fuel Δ a b = .success report :=
  ConcreteBackend.decideFormula_complete (query Δ a b)

theorem run_eventual {Δ : Bounds} {a b : CompareTy}
    (hn : ¬ ∃ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) :
    ∃threshold report, (∀fuel ≥ threshold, run fuel Δ a b = .success report) ∧
      (report.valid = true ↔ AlgebraSubtype Δ a b) := by
  obtain ⟨threshold,report,hr⟩ := run_complete Δ a b
  exact ⟨threshold,report,hr,run_correct (hr threshold le_rfl) hn hΔ ha hb⟩

end ModalityInference.ComparisonObserverDecision
