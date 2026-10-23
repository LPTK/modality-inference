import ModalityInference.Proofs.ComparisonRawHeadReflectionLattice
import ModalityInference.Proofs.ComparisonRawHeadGuardedLattice

/-! Principal reflection for supported raw heads and guarded lattice terms.
Reflection is not asserted for arbitrary partial lattice polynomials. -/
namespace ModalityInference.ComparisonRawHeadRestriction

open ComparisonRawCarrierIdeals ComparisonRawCarrierSuffix
open ComparisonPartialStructuredCapsule

theorem carrier_apply_of_support {Δ H a} (s : Coordinate Δ) (hg : GuardedLattice Δ a)
    (h : support Δ a s.val.literal ⊆ H) : Carrier Δ H (s.val.apply a) :=
  (carrier_modal_total s.property).mpr (generator_of_support hg h)

private theorem indexed_represents {Δ H Index p q}
    (T : IndexedBinaryTable (core Δ H) Index p q) {m a b c S U S' U'}
    (ht : (T.table m).entry a b c)
    (hS : ∀ x, S x ↔ Direction (core Δ H) p x a)
    (hU : ∀ y, U y ↔ Direction (core Δ H) q y b)
    (hS' : ∀ x, S' x ↔ Direction (core Δ H) p a x)
    (hU' : ∀ y, U' y ↔ Direction (core Δ H) q b y) :
    Interpretation.Represents ⟨T.lower m S U,T.upper m S' U'⟩ c := by
  have eS : S = fun x => Direction (core Δ H) p x a := funext fun x => propext (hS x)
  have eU : U = fun y => Direction (core Δ H) q y b := funext fun y => propext (hU y)
  have eS' : S' = fun x => Direction (core Δ H) p a x := funext fun x => propext (hS' x)
  have eU' : U' = fun y => Direction (core Δ H) q b y := funext fun y => propext (hU' y)
  subst S; subst U; subst S'; subst U'
  exact ⟨T.lower_principal ht,T.upper_principal ht⟩

theorem denote_represents {Δ H a} (s : Coordinate Δ) (hg : GuardedLattice Δ a)
    (hc : support Δ a s.val.literal ⊆ H) (hs : a.WellShaped Δ) :
    (denote Δ H a s).Represents (s.val.apply a) := by
  induction a generalizing s with
  | modal a m ih =>
    have hchild : support Δ a (s.prepend m).val.literal ⊆ H := by
      simpa only [Coordinate.prepend, support_prepend] using hc
    exact (ih (s.prepend m) hg hchild hs).equiv
      (s.val.prepend_head_equivalent m s.property (carrier_apply_of_support s hg hc) hs).symm
  | prod a b ia ib =>
    obtain ⟨ha,hb⟩ := support_prod_children hc
    have hia := ia s hg.1 ha hs.1
    have hib := ib s hg.2 hb hs.2
    let T := indexedProdTable Δ H s.val.literal
    have ht : (T.table s.index).entry (s.val.apply a) (s.val.apply b) (s.val.apply (.prod a b)) :=
      ⟨a,b,rfl,rfl,rfl,carrier_apply_of_support s hg.1 ha,carrier_apply_of_support s hg.2 hb,
        carrier_apply_of_support s hg hc,(s.val.apply_wellShaped_iff).mpr hs.1,
        (s.val.apply_wellShaped_iff).mpr hs.2,(s.val.apply_wellShaped_iff).mpr hs⟩
    exact indexed_represents T ht hia.1 hib.1 hia.2 hib.2
  | sum a b ia ib =>
    obtain ⟨ha,hb⟩ := support_sum_children hc
    have hia := ia s hg.1 ha hs.1
    have hib := ib s hg.2 hb hs.2
    let T := indexedSumTable Δ H s.val.literal
    have ht : (T.table s.index).entry (s.val.apply a) (s.val.apply b) (s.val.apply (.sum a b)) :=
      ⟨a,b,rfl,rfl,rfl,carrier_apply_of_support s hg.1 ha,carrier_apply_of_support s hg.2 hb,
        carrier_apply_of_support s hg hc,(s.val.apply_wellShaped_iff).mpr hs.1,
        (s.val.apply_wellShaped_iff).mpr hs.2,(s.val.apply_wellShaped_iff).mpr hs⟩
    exact indexed_represents T ht hia.1 hib.1 hia.2 hib.2
  | fn a b ia ib =>
    cases hp : s.val.literal with
    | some p =>
      simp only [denote,hp,Normalized.apply,prefixApply]
      exact Interpretation.Represents.principal
    | none =>
      have hab : support Δ a none ⊆ H ∧ support Δ b none ⊆ H :=
        support_fn_children (by simp only [hp,Suffix.total]) hc
      have hca := generator_of_support (suffix := none) hg.1 hab.1
      have hcb := generator_of_support (suffix := none) hg.2 hab.2
      have hia := (ia (identityCoordinate Δ) hg.1 hab.1 hs.1).equiv
        (HeadEquivalent.identity hca hs.1).symm
      have hib := (ib (identityCoordinate Δ) hg.2 hab.2 hs.2).equiv
        (HeadEquivalent.identity hcb hs.2).symm
      let T := indexedFnTable Δ H
      have ht : (T.table s.index).entry a b (s.val.apply (.fn a b)) :=
        ⟨by simp only [Normalized.apply,hp,prefixApply,Coordinate.index],
          hca.carrier,hcb.carrier,carrier_apply_of_support s hg hc,hs.1,hs.2,(s.val.apply_wellShaped_iff).mpr hs⟩
      simpa only [denote,hp] using indexed_represents T ht hia.2 hib.1 hia.1 hib.2
  | join a b ia ib =>
    cases hp : s.val.literal with
    | some p =>
      simp only [denote,hp,Normalized.apply,prefixApply]
      exact Interpretation.Represents.principal
    | none =>
      have hab : support Δ a none ⊆ H ∧ support Δ b none ⊆ H := by
        simpa only [support,hp,Suffix.total,↓reduceIte,Set.union_subset_iff] using
          (Set.union_subset_iff.mp hc).2
      have hia := ia s (GuardedLattice.of_defined hg.1) (by simpa only [hp] using hab.1) hs.1
      have hib := ib s (GuardedLattice.of_defined hg.2) (by simpa only [hp] using hab.2) hs.2.1
      simp only [Normalized.apply,hp,prefixApply] at hia hib
      simpa only [denote,hp,Normalized.apply,prefixApply] using
        hia.modal_join hib ⟨hs,hg.1,hg.2⟩ s.property
  | meet a b ia ib =>
    cases hp : s.val.literal with
    | some p =>
      simp only [denote,hp,Normalized.apply,prefixApply]
      exact Interpretation.Represents.principal
    | none =>
      have hab : support Δ a none ⊆ H ∧ support Δ b none ⊆ H := by
        simpa only [support,hp,Suffix.total,↓reduceIte,Set.union_subset_iff] using
          (Set.union_subset_iff.mp hc).2
      have hia := ia s (GuardedLattice.of_defined hg.1) (by simpa only [hp] using hab.1) hs.1
      have hib := ib s (GuardedLattice.of_defined hg.2) (by simpa only [hp] using hab.2) hs.2.1
      simp only [Normalized.apply,hp,prefixApply] at hia hib
      simpa only [denote,hp,Normalized.apply,prefixApply] using
        hia.modal_meet hib ⟨hs,hg.1,hg.2⟩ s.property
  | var | unit | credit => exact Interpretation.Represents.principal

theorem denote_total_represents {Δ H a}
    (m : ComparisonRawCarrierRestriction.TotalIndex Δ) (hg : GuardedLattice Δ a)
    (hc : support Δ a none ⊆ H) (hs : a.WellShaped Δ) :
    (denote Δ H a (totalCoordinate m)).Represents (.modal a m.val) :=
  denote_represents (totalCoordinate m) hg hc hs

theorem denote_defined_represents {Δ H a}
    (m : ComparisonRawCarrierRestriction.TotalIndex Δ) (hd : a.DefinedUnder Δ)
    (hs : a.WellShaped Δ) :
    (denote Δ H a (totalCoordinate m)).Represents (.modal a m.val) :=
  denote_total_represents m (GuardedLattice.of_defined hd)
    (by rw [support_defined hd]; exact Set.empty_subset _) hs

theorem denote_raw_represents {Δ H} (a : Ty)
    (m : ComparisonRawCarrierRestriction.TotalIndex Δ)
    (hc : support Δ (.ofTy a) none ⊆ H) (hs : (CompareTy.ofTy a).WellShaped Δ) :
    (denote Δ H (.ofTy a) (totalCoordinate m)).Represents (.modal (.ofTy a) m.val) :=
  denote_total_represents m (GuardedLattice.ofTy Δ a) hc hs

theorem Related.of_derivation {Δ H a b}
    (ha : support Δ a none ⊆ H) (hb : support Δ b none ⊆ H)
    (hga : GuardedLattice Δ a) (hgb : GuardedLattice Δ b)
    (h : Derivation Δ H a b) : Related Δ H a b := by
  intro m
  have pa := denote_total_represents m hga ha h.shaped.1
  have pb := denote_total_represents m hgb hb h.shaped.2
  have hm := h.congr (Submode.refl m.property)
    (carrier_apply_of_support (totalCoordinate m) hga ha)
    (carrier_apply_of_support (totalCoordinate m) hgb hb)
  exact ⟨fun c hc => (pb.1 c).mpr (((pa.1 c).mp hc).trans hm),
    fun c hc => (pa.2 c).mpr (hm.trans ((pb.2 c).mp hc))⟩

theorem Related.derivation {Δ H a b}
    (ha : support Δ a none ⊆ H) (hb : support Δ b none ⊆ H)
    (hga : GuardedLattice Δ a) (hgb : GuardedLattice Δ b)
    (sa : a.WellShaped Δ) (sb : b.WellShaped Δ)
    (h : Related Δ H a b) : Derivation Δ H a b := by
  let m : ComparisonRawCarrierRestriction.TotalIndex Δ := ⟨.epsilon,fun _ _ => rfl⟩
  have hca := generator_of_support (suffix := none) hga ha
  have hcb := generator_of_support (suffix := none) hgb hb
  have pa := (denote_total_represents m hga ha sa).equiv (HeadEquivalent.identity hca sa).symm
  have pb := (denote_total_represents m hgb hb sb).equiv (HeadEquivalent.identity hcb sb).symm
  exact (pb.1 a).mp ((h m).1 a ((pa.1 a).mpr (Derivation.refl hca.carrier sa)))

theorem Related.of_derivation_defined {Δ H a b} (ha : a.DefinedUnder Δ)
    (hb : b.DefinedUnder Δ) (h : Derivation Δ H a b) : Related Δ H a b :=
  Related.of_derivation (by rw [support_defined ha]; exact Set.empty_subset _)
    (by rw [support_defined hb]; exact Set.empty_subset _)
    (GuardedLattice.of_defined ha) (GuardedLattice.of_defined hb) h

theorem Related.derivation_defined {Δ H a b} (ha : a.DefinedUnder Δ)
    (hb : b.DefinedUnder Δ) (sa : a.WellShaped Δ) (sb : b.WellShaped Δ)
    (h : Related Δ H a b) : Derivation Δ H a b :=
  Related.derivation (by rw [support_defined ha]; exact Set.empty_subset _)
    (by rw [support_defined hb]; exact Set.empty_subset _)
    (GuardedLattice.of_defined ha) (GuardedLattice.of_defined hb) sa sb h

end ModalityInference.ComparisonRawHeadRestriction
