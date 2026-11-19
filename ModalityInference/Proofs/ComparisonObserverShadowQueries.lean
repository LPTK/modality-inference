import ModalityInference.Proofs.ComparisonObserverShadowActions
import ModalityInference.Proofs.ComparisonObserverShadowQueryValues

/-! A finite optional-cut diagram can retain arbitrary defined query patterns
alongside all shadow names. The same finite state witnesses a whole source
pattern, so comparisons between a query and a cut are retained as well. -/
namespace ModalityInference.ComparisonObserverShadowQueries

open ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverShadowActions ComparisonObserverRangeTransfer ComparisonObserverGluing
  ComparisonRawHeadFiniteOrbits ComparisonObserverHeadCuts ComparisonObserverRangeProduct
  ComparisonAlgebra ComparisonObserverRepresentatives

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (B : Boundary Δ) (names : List ModVar) (base : Nat)

def queryBoundary (queries : List CompareTy) : List CompareTy :=
  (presentation hn B names base).shadowVars.map CompareTy.var ++ queries

/-- This is simultaneous covering, rather than only separate witnesses for
individual query inequalities. No query is inserted as a raw subtype bound. -/
def CoversQueries {extra : List (RawRow hn (assign hn B names base))}
    (R : Realization hn B names base extra) (queries : List CompareTy) : Prop :=
  ∀ g : Child Δ, ∃ i : Fin R.count, ∀ a ∈ queryBoundary hn B names base queries,
    a.DefinedUnder Δ → ComparisonObserverMachine.value R.machine a i =
      ComparisonObserverMachine.value (nodes hn (assign hn B names base)) a g

theorem exists_realization_queries (extra : List (RawRow hn (assign hn B names base)))
    (queries : List CompareTy) :
    ∃ R : Realization hn B names base extra,
      R.count ≤ ComparisonObserverBoundary.sizeBound (context Δ (diagramRows hn B names base extra))
        (queryBoundary hn B names base queries) ∧ CoversQueries hn B names base R queries := by
  let S := presentation hn B names base
  let raw := rows hn B names base ++ extra
  obtain ⟨count,hcount,machine,hc,hcover⟩ := finite_rows hn (assign hn B names base)
    (diagramRows hn B names base extra)
    (fun p hp => (List.mem_append.mp hp).elim
      (orderRows_defined _ S.shadowVars p) (RawRow.rows_defined hn _ raw p))
    (fun p hp => (List.mem_append.mp hp).elim
      (orderRows_sound hn _ S.shadowVars p) (RawRow.rows_sound hn _ raw p))
    (queryBoundary hn B names base queries)
  have hcover' : ∀ g : Child Δ, ∃ i : Fin count,
      ∀ a ∈ queryBoundary hn B names base queries, a.DefinedUnder Δ →
        ComparisonObserverMachine.value machine a i =
          ComparisonObserverMachine.value (nodes hn (assign hn B names base)) a g := by
    intro g
    obtain ⟨i,hi⟩ := hcover g
    exact ⟨i,fun a ha hd => hi a ha (fun η hη => hd η ((context_modes Δ _ η).mp hη))⟩
  have horder : ∀ v ∈ S.shadowVars, ∀ w ∈ S.shadowVars,
      ComparisonObserverFiniteRange.atom hc.range v ≤ ComparisonObserverFiniteRange.atom hc.range w ↔
        assign hn B names base v ≤ assign hn B names base w := by
    intro v hv w hw
    constructor
    · intro h g
      obtain ⟨i,hi⟩ := hcover' g
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
  exact ⟨⟨count,machine,hc,I,hlo,hup⟩,hcount,hcover'⟩

namespace CoversQueries

variable {hn B names base} {extra : List (RawRow hn (assign hn B names base))}
    {R : Realization hn B names base extra} {queries : List CompareTy}
    (h : CoversQueries hn B names base R queries)

include h

theorem compare_reflect {a b : CompareTy} (ha : a ∈ queries) (hb : b ∈ queries)
    (hda : a.DefinedUnder Δ) (hdb : b.DefinedUnder Δ)
    (hfa : ∀ v ∈ ComparisonObserverBoundary.types a, v.index < base)
    (hfb : ∀ v ∈ ComparisonObserverBoundary.types b, v.index < base)
    (hle : ComparisonObserverFiniteRange.eval R.range a hda ≤
      ComparisonObserverFiniteRange.eval R.range b hdb) : AlgebraSubtype Δ a b := by
  apply (ofType_le_iff hn a b hda hdb).mp
  intro g
  obtain ⟨i,hi⟩ := h g
  have hae := hi a (List.mem_append_right _ ha) hda
  have hbe := hi b (List.mem_append_right _ hb) hdb
  dsimp only [assign] at hae hbe
  rw [ComparisonObserverShadowQueryValues.fresh_value hn (source B names) base a hda hfa] at hae
  rw [ComparisonObserverShadowQueryValues.fresh_value hn (source B names) base b hdb hfb] at hbe
  change (ofType hn a hda g).val ≤ (ofType hn b hdb g).val
  rw [←hae,←hbe]
  exact hle i

theorem eval_le_name_reflect {a : CompareTy} (ha : a ∈ queries) (hda : a.DefinedUnder Δ)
    (hfa : ∀ v ∈ ComparisonObserverBoundary.types a, v.index < base)
    {v : TypeVar} (hv : v ∈ (presentation hn B names base).shadowVars)
    (hle : ComparisonObserverFiniteRange.eval R.range a hda ≤
      ComparisonObserverFiniteRange.atom R.certified.range v) :
    ofType hn a hda ≤ assign hn B names base v := by
  intro g
  obtain ⟨i,hi⟩ := h g
  have hae := hi a (List.mem_append_right _ ha) hda
  have hve := hi (.var v) (List.mem_append_left _ (List.mem_map.mpr ⟨v,hv,rfl⟩)) (var_defined Δ v)
  dsimp only [assign] at hae
  rw [ComparisonObserverShadowQueryValues.fresh_value hn (source B names) base a hda hfa] at hae
  change (ComparisonObserverMachine.value R.machine (.var v) i) = (assign hn B names base v g).val at hve
  change (ofType hn a hda g).val ≤ (assign hn B names base v g).val
  rw [←hae,←hve]
  exact hle i

theorem name_le_eval_reflect {a : CompareTy} (ha : a ∈ queries) (hda : a.DefinedUnder Δ)
    (hfa : ∀ v ∈ ComparisonObserverBoundary.types a, v.index < base)
    {v : TypeVar} (hv : v ∈ (presentation hn B names base).shadowVars)
    (hle : ComparisonObserverFiniteRange.atom R.certified.range v ≤
      ComparisonObserverFiniteRange.eval R.range a hda) :
    assign hn B names base v ≤ ofType hn a hda := by
  intro g
  obtain ⟨i,hi⟩ := h g
  have hae := hi a (List.mem_append_right _ ha) hda
  have hve := hi (.var v) (List.mem_append_left _ (List.mem_map.mpr ⟨v,hv,rfl⟩)) (var_defined Δ v)
  dsimp only [assign] at hae
  rw [ComparisonObserverShadowQueryValues.fresh_value hn (source B names) base a hda hfa] at hae
  change (ComparisonObserverMachine.value R.machine (.var v) i) = (assign hn B names base v g).val at hve
  change (assign hn B names base v g).val ≤ (ofType hn a hda g).val
  rw [←hae,←hve]
  exact hle i

theorem defined_boundary_reflect {a : CompareTy} (ha : a ∈ queries) (hda : a.DefinedUnder Δ)
    (hfa : ∀ v ∈ ComparisonObserverBoundary.types a, v.index < base)
    {p : Point B names}
    (hle : R.interval.Rel (.inl (ComparisonObserverFiniteRange.eval R.range a hda)) (.inr p)) :
    AlgebraSubtype Δ a p.term := by
  obtain ⟨lo,hlo,hle⟩ := hle
  have hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term := by
    by_contra hp
    rw [R.lower_eq p,if_neg hp] at hlo
    cases hlo
  have he : lo = ComparisonObserverFiniteRange.atom R.certified.range (shadowName base (p,false)) := by
    simpa only [R.lower_eq p,if_pos hp,Option.some.injEq] using hlo.symm
  rw [he] at hle
  have hv : shadowName base (p,false) ∈ (presentation hn B names base).shadowVars := by
    apply NamedIntervals.lower_mem (p := p)
    simp [presentation,named,source,headIntervals,hp]
  have hs := h.eval_le_name_reflect ha hda hfa hv hle
  rw [lower_name hn B names base p hp] at hs
  let c := represented (representable hn hda)
  have hu : UpperInhabited (Δ := Δ) (shape := .unit) a := ⟨c,.refl c.shaped⟩
  exact ComparisonObserverShadowRows.saturation hu hp
    ((ComparisonObserverShadowRows.upper_defined c).le.trans hs)

theorem boundary_defined_reflect {a : CompareTy} (ha : a ∈ queries) (hda : a.DefinedUnder Δ)
    (hfa : ∀ v ∈ ComparisonObserverBoundary.types a, v.index < base)
    {p : Point B names}
    (hle : R.interval.Rel (.inr p) (.inl (ComparisonObserverFiniteRange.eval R.range a hda))) :
    AlgebraSubtype Δ p.term a := by
  obtain ⟨up,hup,hle⟩ := hle
  have hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term := by
    by_contra hp
    rw [R.upper_eq p,if_neg hp] at hup
    cases hup
  have he : up = ComparisonObserverFiniteRange.atom R.certified.range (shadowName base (p,true)) := by
    simpa only [R.upper_eq p,if_pos hp,Option.some.injEq] using hup.symm
  rw [he] at hle
  have hv : shadowName base (p,true) ∈ (presentation hn B names base).shadowVars := by
    apply NamedIntervals.upper_mem (p := p)
    simp [presentation,named,source,headIntervals,hp]
  have hs := h.name_le_eval_reflect ha hda hfa hv hle
  rw [upper_name hn B names base p hp] at hs
  let c := represented (representable hn hda)
  have hl : LowerInhabited (Δ := Δ) (shape := .unit) a := ⟨c,.refl c.shaped⟩
  exact ComparisonObserverShadowRows.saturation hp hl
    (hs.trans (ComparisonObserverShadowRows.lower_defined c).symm.le)

end CoversQueries
end
end ModalityInference.ComparisonObserverShadowQueries
