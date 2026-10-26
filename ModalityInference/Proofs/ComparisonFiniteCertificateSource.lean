import ModalityInference.Proofs.ComparisonFiniteCertificateSerialization
import ModalityInference.Proofs.ComparisonExecutableAgreementEncoding
import ModalityInference.Proofs.ComparisonObserverShadowQueryDescriptions
import ModalityInference.Proofs.ComparisonObserverShadowModel

/-! A described finite shadow realization has a source presentation on finite
certificate indices, preserving every comparison in its syntax model. -/
namespace ModalityInference.ComparisonFiniteCertificate.SourceConstruction

open ComparisonFiniteControlEncoding ComparisonExecutableControls ComparisonFiniteControls
  ComparisonRelativeCoordinates ComparisonRelativeSyntax ComparisonExecutableAgreementEncoding
  ComparisonObserverShadowActions ComparisonObserverShadowModel ComparisonObserverShadowPresentation
  ComparisonObserverShadowActionRows ComparisonRawHeadFiniteOrbits ComparisonObserverShadowQueryDescriptions
  ComparisonExecutableDefinedAgreement Serialization

noncomputable section

variable {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
  {B : Boundary Δ} {names : List ModVar} {base : Nat}
  {extra : List (RawRow hn (assign hn B names base))}
  (R : Realization hn B names base extra) (T : Tables R)
  (hnames : Δ.modVars ⊆ names.toFinset) (sites : List RawSite)
  (tag : RawSite → ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names)
  {tags observations : Nat}
  (ea : Fin tags ≃ (ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names))
  (eo : Fin observations ≃ R.interval.Observation)

def indexedModel := ComparisonExecutableObservationTransport.transport
  (encodeModel (T.model hnames sites tag)) ea eo

def indexedEmbedding : LatticeHom (ComparisonObserverFiniteRange.Value R.machine)
    (ComparisonRelativeCoordinates.Coordinates (Code Δ names) (Fin observations → Bool)) := observationEmbedding
  (encodeEmbedding (definedOrbit R.interval R.modal R.range)) eo

theorem indexed_agreement : CodeDefinedAgreement (indexedModel R T hnames sites tag ea eo)
    R.modal R.range (indexedEmbedding R eo) :=
  observations_agreement _ R.modal R.range _
    (encode_agreement _ R.modal R.range hnames _ (T.agreement hnames sites tag)) ea eo

theorem indexed_related_iff (a b : CompareTy) :
    (indexedModel R T hnames sites tag ea eo).Related a b ↔ (T.model hnames sites tag).Related a b :=
  (ComparisonExecutableObservationTransport.related_iff _ ea eo a b).trans
    (ComparisonExecutableModelTransport.related_iff _ (orderIso Δ names) decode_one decode_mul a b)

theorem indexed_prod_relation (p : Option ModExpr) (m n : Code Δ names) :
    order m n = true ↔ ((indexedModel R T hnames sites tag ea eo).prodTable p).le m n := by
  change m ≤ n ↔ (T.prodTable p).le (decode m) (decode n)
  cases p with
  | none => exact (order_iff m n).trans (T.prod_le (decode m) (decode n)).symm
  | some p => exact order_iff m n

theorem indexed_sum_relation (p : Option ModExpr) (m n : Code Δ names) :
    order m n = true ↔ ((indexedModel R T hnames sites tag ea eo).sumTable p).le m n := by
  cases p with
  | none => exact (order_iff m n).trans (T.sum_le (decode m) (decode n)).symm
  | some p => exact order_iff m n

theorem indexed_fn_relation (m n : Code Δ names) :
    future m n = true ↔ (indexedModel R T hnames sites tag ea eo).fnTable.le m n :=
  (future_iff m n).trans (T.fn_le (decode m) (decode n)).symm

theorem indexed_prod_empty (p : ModExpr) (hp : p ∉ ComparisonRawHeadPrefixRows.prefixes B)
    (m : Code Δ names) (a b c : Fin tags) :
    ¬ (((indexedModel R T hnames sites tag ea eo).prodTable (some p)).table m).entry a b c :=
  fun h => hp (ComparisonRawHeadPrefixRows.entry_prefix_mem h)

theorem indexed_sum_empty (p : ModExpr) (hp : p ∉ ComparisonRawHeadPrefixRows.prefixes B)
    (m : Code Δ names) (a b c : Fin tags) :
    ¬ (((indexedModel R T hnames sites tag ea eo).sumTable (some p)).table m).entry a b c :=
  fun h => hp (ComparisonRawHeadPrefixRows.entry_prefix_mem h)

include ea eo in
theorem source_of_indices {queries : List CompareTy}
    (description : Described hn B names base R queries) :
    ∃ source : Source Δ names R.count tags observations,
      ∀ a b, source.model.Related a b ↔ (T.model hnames sites tag).Related a b := by
  have hc : ComparisonObserverMachineCheck.check (shadow Δ)
      (descriptionTypes hn B names base extra queries) (descriptionModes hn B names base extra queries)
      description.data = true := by
    simpa only [shadow_eq] using Described.checked_shadow hn B names base description
  obtain ⟨j,hj⟩ := change_nodes (indexedModel R T hnames sites tag ea eo) R.modal R.range
    (indexedEmbedding R eo) description.machine_eq (checked_laws hc).1 (checked_laws hc).2.1
      (indexed_agreement R T hnames sites tag ea eo)
  exact ⟨{
    types := descriptionTypes hn B names base extra queries
    modes := descriptionModes hn B names base extra queries
    machine := description.data
    embed := fun a o => R.interval.embed (ea a) (eo o)
    model := indexedModel R T hnames sites tag ea eo
    checked := hc
    names_supported := hnames
    keys := ComparisonRawHeadPrefixRows.prefixes B
    prod_relation := indexed_prod_relation R T hnames sites tag ea eo
    sum_relation := indexed_sum_relation R T hnames sites tag ea eo
    fn_relation := indexed_fn_relation R T hnames sites tag ea eo
    prod_empty := indexed_prod_empty R T hnames sites tag ea eo
    sum_empty := indexed_sum_empty R T hnames sites tag ea eo
    embedding := j
    agreement := hj }, indexed_related_iff R T hnames sites tag ea eo⟩

theorem exists_source {queries : List CompareTy}
    (description : Described hn B names base R queries) :
    ∃ tags observations, ∃ source : Source Δ names R.count tags observations,
      ∀ a b, source.model.Related a b ↔ (T.model hnames sites tag).Related a b := by
  letI : Fintype (ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) := Fintype.ofFinite _
  letI : Fintype R.interval.Observation := Fintype.ofFinite _
  exact ⟨_,_,source_of_indices R T hnames sites tag
    (Fintype.equivFin (ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names)).symm
    (Fintype.equivFin R.interval.Observation).symm description⟩

end
end ModalityInference.ComparisonFiniteCertificate.SourceConstruction
