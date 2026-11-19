import ModalityInference.Proofs.ComparisonObserverRangeTransfer
import ModalityInference.Proofs.ComparisonObserverMachineSerialization
import ModalityInference.Proofs.ComparisonObserverMachineModeTransport

/-! Checked finite descriptions preserve the joint values of an arbitrary
observer-range assignment. The auxiliary raw rows are checked in their defined
context; only scalar, range, and constructor laws transfer back to the original
context, whose raw type bounds may be partial. -/
namespace ModalityInference.ComparisonObserverRangeDescriptions

open ComparisonAlgebra ComparisonObserverBoundary ComparisonObserverGluing
  ComparisonObserverRepresentatives ComparisonObserverRangeProduct
  ComparisonObserverRangeTransfer ComparisonObserverMachine
  ComparisonObserverMachineCheck ComparisonObserverMachineSerialization
  ComparisonBalancedProjection

/-- The serialized machine preserves an entire query pattern at one state for
each source observer. It is obtained from coordinate representatives, rather
than by assuming that an arbitrary certified machine has coordinates. -/
theorem finite_boundary {Δ Γ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ)
    (hmodels : ∀ η, ModeModels Δ η → ModeModels Γ η)
    (hb : BoundsHold Γ (ComparisonObserverRangeTransfer.nodes hn assign))
    (hΓ : Γ.TypeBoundsDefined) (hshape : ¬ ∃ ρ, ComparisonShape.Models Γ ρ)
    (queries : List CompareTy) :
    ∃ count ≤ sizeBound Γ queries, ∃ data : Fin count → Description (Fin count),
      check Γ (retainedTypes Γ queries) (retainedModes Γ queries) data = true ∧
      ∀ g : Child Δ, ∃ i : Fin count, ∀ a ∈ queries, a.DefinedUnder Γ →
        value (ComparisonObserverMachineCheck.nodes
          (retainedTypes Γ queries) (retainedModes Γ queries) data) a i =
          value (ComparisonObserverRangeTransfer.nodes hn assign) a g := by
  obtain ⟨count,hcount,data,hdata,hcover⟩ := bounded_descriptions_on
    (show Γ.modVars ⊆ names Γ queries from Finset.subset_union_left) hshape hΓ
    (retainedTypes Γ queries) (retainedModes Γ queries) (mem_retainedModes Γ queries)
    (boundary Γ queries) (closure_ports_closed _) (boundary_declared Γ queries)
    (boundary_support Γ queries) (fun a ha => (boundary_retained_support Γ queries a ha).mono
      (fun _ h => h) (fun _ _ => trivial))
  let hc := ComparisonObserverRangeTransfer.certified hn assign hmodels hb
  refine ⟨count,hcount,data,hdata,?_⟩
  intro g
  obtain ⟨i,hi⟩ := hcover (hc.observer hΓ g)
  refine ⟨i,?_⟩
  intro a ha had
  rw [hi a (boundary_query ha) had,
    booleanValue_represented _ a (representable hshape had)]
  rfl

/-- Removing the auxiliary subtype rows preserves every local machine check.
The shape-only context has exactly the original scalar models. -/
theorem check_shadow {Δ rows types modes count}
    {data : Fin count → Description (Fin count)}
    (hc : check (context Δ rows) types modes data = true) :
    check (shapeShadow Δ) types modes data = true := by
  apply check_correct.mpr
  intro i
  have h := check_correct.mp hc i
  refine ⟨?_,h.unit,h.credit,h.atom,h.closed,h.branch,h.prod,h.sum,h.fn,?_⟩
  · apply scalarOK_correct.mpr
    rcases scalarOK_correct.mp h.scalar with he | hm
    · exact Or.inl he
    · exact Or.inr ((modeModels_shadow Δ _).mpr ((context_modes Δ rows _).mp hm))
  · apply declared_correct.mpr
    exact fun a b hab => (sub_not_mem_shadow Δ a b hab).elim

/-- Original-context operations follow from scalar equivalence alone. This
does not assert that the machine satisfies the original raw subtype bounds. -/
theorem checked_modes {Δ rows types modes count}
    {data : Fin count → Description (Fin count)}
    (hc : check (context Δ rows) types modes data = true) :
    ModalValid Δ (ComparisonObserverMachineCheck.nodes types modes data) ∧
    RangeClosed Δ (ComparisonObserverMachineCheck.nodes types modes data) ∧
    Coherent Δ (ComparisonObserverMachineCheck.nodes types modes data) :=
  ComparisonObserverMachineModeTransport.certified_modes
    (fun η => (context_modes Δ rows η).mp) (check_sound hc)

/-- Checked descriptions realize arbitrary finite defined rows and retain all
selected query values simultaneously. No definedness of the original ambient
type bounds is required. The finite retained-name lists include the rows and
queries, including any caller-supplied support markers. -/
theorem finite_rows {Δ} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (rows : List (Ty × Ty))
    (hd : ∀ p ∈ rows, p.1.DefinedUnder Δ ∧ p.2.DefinedUnder Δ)
    (hr : ∀ p ∈ rows, ∀ g,
      value (ComparisonObserverRangeTransfer.nodes hn assign) (.ofTy p.1) g ≤
        value (ComparisonObserverRangeTransfer.nodes hn assign) (.ofTy p.2) g)
    (queries : List CompareTy) :
    ∃ count ≤ sizeBound (context Δ rows) queries,
      ∃ data : Fin count → Description (Fin count),
      check (context Δ rows) (retainedTypes (context Δ rows) queries)
        (retainedModes (context Δ rows) queries) data = true ∧
      check (shapeShadow Δ) (retainedTypes (context Δ rows) queries)
        (retainedModes (context Δ rows) queries) data = true ∧
      ∀ g : Child Δ, ∃ i : Fin count, ∀ a ∈ queries, a.DefinedUnder Δ →
        value (ComparisonObserverMachineCheck.nodes
          (retainedTypes (context Δ rows) queries)
          (retainedModes (context Δ rows) queries) data) a i =
          value (ComparisonObserverRangeTransfer.nodes hn assign) a g := by
  obtain ⟨count,hcount,data,hdata,hcover⟩ := finite_boundary hn assign
    (fun η => (context_modes Δ rows η).mpr) (context_bounds hn assign rows hr)
    (context_defined hd) (context_no_shapes hn rows) queries
  refine ⟨count,hcount,data,hdata,check_shadow hdata,?_⟩
  intro g
  obtain ⟨i,hi⟩ := hcover g
  exact ⟨i,fun a ha had => hi a ha
    (fun η hη => had η ((context_modes Δ rows η).mp hη))⟩

end ModalityInference.ComparisonObserverRangeDescriptions
