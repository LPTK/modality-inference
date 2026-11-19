import ModalityInference.Proofs.ComparisonObserverShadowQuerySupport
import ModalityInference.Proofs.ComparisonObserverShadowQueryDescriptions

/-! Query reflection for the realization chosen together with checked machine
 descriptions. Its source model is ready for finite certificate serialization. -/
namespace ModalityInference.ComparisonFiniteCertificateQueries

open ComparisonRelativeSyntax ComparisonRawHeadFiniteOrbits ComparisonFiniteControls
  ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverShadowActions ComparisonRawHeadTrace ComparisonObserverShadowModel
  ComparisonObserverShadowQueries

noncomputable section

private abbrev inputs := ComparisonObserverShadowQuerySupport.rawInputs
private abbrev trace := ComparisonObserverShadowQuerySupport.sites

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
  (raw : List Ty) (queries : List CompareTy)

def realization : Realization hn (boundary Δ (trace Δ raw queries)) (modeNames Δ (trace Δ raw queries))
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads (trace Δ raw queries)))
    (RawInput.extraRows hn (inputs raw queries)) :=
  (ComparisonObserverShadowQueryDescriptions.exists_realization hn _ _ _ (RawInput.extraRows hn (inputs raw queries)) queries).choose

theorem covers : CoversQueries hn (boundary Δ (trace Δ raw queries)) (modeNames Δ (trace Δ raw queries))
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads (trace Δ raw queries)))
    (realization hn raw queries) queries :=
  (ComparisonObserverShadowQueryDescriptions.exists_realization hn _ _ _ (RawInput.extraRows hn (inputs raw queries)) queries).choose_spec.2.1

def description : ComparisonObserverShadowQueryDescriptions.Described hn
    (boundary Δ (trace Δ raw queries)) (modeNames Δ (trace Δ raw queries))
    (ComparisonObserverShadowAnchorRows.freshBase (rawHeads (trace Δ raw queries)))
    (realization hn raw queries) queries :=
  (ComparisonObserverShadowQueryDescriptions.exists_realization hn _ _ _
    (RawInput.extraRows hn (inputs raw queries)) queries).choose_spec.2.2.some

def table : Tables (realization hn raw queries) :=
  tables (realization hn raw queries) (RawInput.constructor_rows hn (inputs raw queries))

def model := interpretation (realization hn raw queries) (table hn raw queries)

theorem sound {a b : CompareTy} (h : AlgebraSubtype Δ a b) : (model hn raw queries).Related a b :=
  algebra_sound (realization hn raw queries) (table hn raw queries)
    (RawInput.anchor_rows hn (inputs raw queries)) (RawInput.trace_closed Δ (inputs raw queries))
    (fun _ _ hb => RawInput.bounds_mem Δ (inputs raw queries) hb) h

theorem raw_iff {a b : Ty} (ha : a ∈ raw) (hb : b ∈ raw) :
    (model hn raw queries).Related (.ofTy a) (.ofTy b) ↔ AlgebraSubtype Δ (.ofTy a) (.ofTy b) :=
  raw_related_iff (realization hn raw queries) (table hn raw queries)
    (RawInput.anchor_rows hn (inputs raw queries)) (RawInput.trace_closed Δ (inputs raw queries))
    (ComparisonObserverShadowQuerySupport.raw_mem ha) (ComparisonObserverShadowQuerySupport.raw_mem hb)

theorem denote_query {a : CompareTy} (ha : a ∈ queries) (hda : a.DefinedUnder Δ) :
    (model hn raw queries).denote a none =
      definedOrbit (realization hn raw queries).interval (realization hn raw queries).modal
        (realization hn raw queries).range
        (ComparisonObserverFiniteRange.eval (realization hn raw queries).range a hda) := by
  have he := ((table hn raw queries).agreement (context_names Δ (trace Δ raw queries))
    (trace Δ raw queries) (siteTag (realization hn raw queries))).denote_defined hda
  exact he.trans (congrArg _ (ComparisonObserverShadowQueryValues.evaluate_eq_eval
    (realization hn raw queries).range (context_names Δ (trace Δ raw queries)) a hda
    (ComparisonObserverShadowQuerySupport.query_modes ha)))

theorem defined_raw_iff {a : CompareTy} {b : Ty} (ha : a ∈ queries) (hb : b ∈ raw)
    (hda : a.DefinedUnder Δ) :
    (model hn raw queries).Related a (.ofTy b) ↔ AlgebraSubtype Δ a (.ofTy b) := by
  constructor
  · intro h
    change (model hn raw queries).denote a none ≤ (model hn raw queries).denote (.ofTy b) none at h
    have hbs := ComparisonObserverShadowQuerySupport.raw_mem (Δ := Δ) (queries := queries) hb
    have hraw : (model hn raw queries).denote (.ofTy b) none =
        (realization hn raw queries).orbit (siteTag (realization hn raw queries) (b,none)) :=
      denote_raw (realization hn raw queries) (table hn raw queries)
        (RawInput.anchor_rows hn (inputs raw queries))
        (RawInput.trace_closed Δ (inputs raw queries)) hbs
    rw [denote_query hn raw queries ha hda,definedOrbit_eq,hraw] at h
    have hr := ((realization hn raw queries).orbit_le_iff _ _).mp h
    rw [siteTag_mem _ hbs] at hr
    exact ((covers hn raw queries).defined_boundary_reflect ha hda
      (ComparisonObserverShadowQuerySupport.query_fresh ha) hr).trans
      (memberPoint_equivalent Δ _ hbs).1
  · exact sound hn raw queries

theorem raw_defined_iff {a : Ty} {b : CompareTy} (ha : a ∈ raw) (hb : b ∈ queries)
    (hdb : b.DefinedUnder Δ) :
    (model hn raw queries).Related (.ofTy a) b ↔ AlgebraSubtype Δ (.ofTy a) b := by
  constructor
  · intro h
    change (model hn raw queries).denote (.ofTy a) none ≤ (model hn raw queries).denote b none at h
    have has := ComparisonObserverShadowQuerySupport.raw_mem (Δ := Δ) (queries := queries) ha
    have hraw : (model hn raw queries).denote (.ofTy a) none =
        (realization hn raw queries).orbit (siteTag (realization hn raw queries) (a,none)) :=
      denote_raw (realization hn raw queries) (table hn raw queries)
        (RawInput.anchor_rows hn (inputs raw queries))
        (RawInput.trace_closed Δ (inputs raw queries)) has
    rw [hraw,denote_query hn raw queries hb hdb,definedOrbit_eq] at h
    have hr := ((realization hn raw queries).orbit_le_iff _ _).mp h
    rw [siteTag_mem _ has] at hr
    exact (memberPoint_equivalent Δ _ has).2.trans
      ((covers hn raw queries).boundary_defined_reflect hb hdb
        (ComparisonObserverShadowQuerySupport.query_fresh hb) hr)
  · exact sound hn raw queries

theorem defined_iff {a b : CompareTy} (ha : a ∈ queries) (hb : b ∈ queries)
    (hda : a.DefinedUnder Δ) (hdb : b.DefinedUnder Δ) :
    (model hn raw queries).Related a b ↔ AlgebraSubtype Δ a b := by
  constructor
  · intro h
    change (model hn raw queries).denote a none ≤ (model hn raw queries).denote b none at h
    rw [denote_query hn raw queries ha hda,denote_query hn raw queries hb hdb] at h
    exact (covers hn raw queries).compare_reflect ha hb hda hdb
      (ComparisonObserverShadowQuerySupport.query_fresh ha)
      (ComparisonObserverShadowQuerySupport.query_fresh hb)
      (definedOrbit_reflect _ _ _ h)
  · exact sound hn raw queries

theorem finite_carrier : Finite (ComparisonRelativeCoordinates.Coordinates
    (Control Δ (modeNames Δ (trace Δ raw queries))) (realization hn raw queries).interval.Completion) :=
  (realization hn raw queries).orbit_space_finite

end
end ModalityInference.ComparisonFiniteCertificateQueries
