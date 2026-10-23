import ModalityInference.Proofs.ComparisonObserverShadowQueries
import ModalityInference.Proofs.ComparisonObserverRangeDescriptions

/-! The optional-cut realization can be chosen with an explicit checked
description, retaining all selected query and shadow values in the same
machine. Existing interval, action, anchor, and table interfaces are unchanged. -/
namespace ModalityInference.ComparisonObserverShadowQueryDescriptions

open ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverShadowActions ComparisonObserverShadowQueries
  ComparisonObserverRangeTransfer ComparisonObserverGluing ComparisonRawHeadFiniteOrbits
  ComparisonObserverHeadCuts ComparisonObserverRangeProduct ComparisonAlgebra
  ComparisonObserverRepresentatives

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (B : Boundary Δ) (names : List ModVar) (base : Nat)

def descriptionTypes (extra : List (RawRow hn (assign hn B names base)))
    (queries : List CompareTy) : List TypeVar :=
  ComparisonObserverBoundary.retainedTypes (context Δ (diagramRows hn B names base extra))
    (queryBoundary hn B names base queries)

def descriptionModes (extra : List (RawRow hn (assign hn B names base)))
    (queries : List CompareTy) : List ModVar :=
  ComparisonObserverBoundary.retainedModes (context Δ (diagramRows hn B names base extra))
    (queryBoundary hn B names base queries)

/-- Executable description data with exact equality to its semantic machine. -/
structure MachineDescription (Γ : Bounds) (types : List TypeVar) (modes : List ModVar)
    (count : Nat) (machine : ComparisonObserverMachine.Machine count) where
  data : Fin count → ComparisonObserverMachineCheck.Description (Fin count)
  checked : ComparisonObserverMachineCheck.check Γ types modes data = true
  machine_eq : machine = ComparisonObserverMachineCheck.nodes types modes data

abbrev Described {extra : List (RawRow hn (assign hn B names base))}
    (R : Realization hn B names base extra) (queries : List CompareTy) :=
  MachineDescription (context Δ (diagramRows hn B names base extra))
    (descriptionTypes hn B names base extra queries)
    (descriptionModes hn B names base extra queries) R.count R.machine

theorem Described.checked_shadow {extra : List (RawRow hn (assign hn B names base))}
    {R : Realization hn B names base extra} {queries : List CompareTy}
    (h : Described hn B names base R queries) :
    ComparisonObserverMachineCheck.check (ComparisonBalancedProjection.shapeShadow Δ)
      (descriptionTypes hn B names base extra queries)
      (descriptionModes hn B names base extra queries) h.data = true :=
  ComparisonObserverRangeDescriptions.check_shadow h.checked

private def realize {extra : List (RawRow hn (assign hn B names base))}
    {queries : List CompareTy} {count : Nat} (machine : ComparisonObserverMachine.Machine count)
    (hc : ComparisonObserverMachine.Certified (context Δ (diagramRows hn B names base extra)) machine)
    (hcover : ∀ g : Child Δ, ∃ i : Fin count, ∀ a ∈ queryBoundary hn B names base queries,
      a.DefinedUnder Δ → ComparisonObserverMachine.value machine a i =
        ComparisonObserverMachine.value (nodes hn (assign hn B names base)) a g) :
    Realization hn B names base extra := by
  let S := presentation hn B names base
  have horder : ∀ v ∈ S.shadowVars, ∀ w ∈ S.shadowVars,
      ComparisonObserverFiniteRange.atom hc.range v ≤ ComparisonObserverFiniteRange.atom hc.range w ↔
        assign hn B names base v ≤ assign hn B names base w := by
    intro v hv w hw
    constructor
    · intro h g
      obtain ⟨i,hi⟩ := hcover g
      have hvi := hi (.var v) (List.mem_append_left _ (List.mem_map.mpr ⟨v,hv,rfl⟩)) (var_defined Δ v)
      have hwi := hi (.var w) (List.mem_append_left _ (List.mem_map.mpr ⟨w,hw,rfl⟩)) (var_defined Δ w)
      change (assign hn B names base v g).val ≤ (assign hn B names base w g).val
      change (machine i).atom v = (assign hn B names base v g).val at hvi
      change (machine i).atom w = (assign hn B names base w g).val at hwi
      rw [←hvi,←hwi]
      exact h i
    · intro h i
      exact hc.bounds i (.var v) (.var w) (context_sub.mpr
        (List.mem_append_left _ (mem_orderRows.mpr ⟨v,hv,w,hw,h,rfl,rfl⟩)))
  let I := S.realize (ComparisonObserverFiniteRange.atom hc.range) horder
  have hlo : ∀ p, I.lower p = if LowerInhabited (Δ := Δ) (shape := .unit) p.term
      then some (ComparisonObserverFiniteRange.atom hc.range (shadowName base (p,false))) else none := by
    intro p
    dsimp [I,NamedIntervals.realize,S,presentation,named,source,headIntervals]
    split <;> rfl
  have hup : ∀ p, I.upper p = if UpperInhabited (Δ := Δ) (shape := .unit) p.term
      then some (ComparisonObserverFiniteRange.atom hc.range (shadowName base (p,true))) else none := by
    intro p
    dsimp [I,NamedIntervals.realize,S,presentation,named,source,headIntervals]
    split <;> rfl
  exact ⟨count,machine,hc,I,hlo,hup⟩

theorem exists_realization (extra : List (RawRow hn (assign hn B names base)))
    (queries : List CompareTy) :
    ∃ R : Realization hn B names base extra,
      R.count ≤ ComparisonObserverBoundary.sizeBound (context Δ (diagramRows hn B names base extra))
        (queryBoundary hn B names base queries) ∧
      CoversQueries hn B names base R queries ∧ Nonempty (Described hn B names base R queries) := by
  let S := presentation hn B names base
  let raw := rows hn B names base ++ extra
  obtain ⟨count,hcount,data,hdata,_,hcover⟩ := ComparisonObserverRangeDescriptions.finite_rows
    hn (assign hn B names base) (diagramRows hn B names base extra)
    (fun p hp => (List.mem_append.mp hp).elim
      (orderRows_defined _ S.shadowVars p) (RawRow.rows_defined hn _ raw p))
    (fun p hp => (List.mem_append.mp hp).elim
      (orderRows_sound hn _ S.shadowVars p) (RawRow.rows_sound hn _ raw p))
    (queryBoundary hn B names base queries)
  let machine : ComparisonObserverMachine.Machine count := ComparisonObserverMachineCheck.nodes
    (descriptionTypes hn B names base extra queries)
    (descriptionModes hn B names base extra queries) data
  let hc := ComparisonObserverMachineCheck.check_sound hdata
  let R := realize hn B names base machine hc hcover
  exact ⟨R,hcount,hcover,⟨⟨data,hdata,rfl⟩⟩⟩

end
end ModalityInference.ComparisonObserverShadowQueryDescriptions
