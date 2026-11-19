import ModalityInference.Proofs.ComparisonRawHeadInterpretation

/-! Principal reflection for lattice operations and guarded modal distribution.
No principal interpretation of arbitrary partial lattice terms under a total
action is assumed. -/
namespace ModalityInference.ComparisonRawHeadRestriction

open ComparisonRawCarrierIdeals ComparisonRawCarrierSuffix

namespace Interpretation

def Represents {Δ H} (S : Interpretation Δ H) (a : CompareTy) : Prop :=
  (∀ c, S.lower.mem c ↔ Derivation Δ H c a) ∧
    (∀ c, S.upper.mem c ↔ Derivation Δ H a c)

theorem Represents.principal {Δ H a} : (Interpretation.principal Δ H a).Represents a :=
  ⟨fun _ => Iff.rfl,fun _ => Iff.rfl⟩

theorem Represents.equiv {Δ H S a b} (hs : @Represents Δ H S a)
    (h : HeadEquivalent Δ H a b) : S.Represents b := by
  constructor
  · intro c
    exact ⟨fun hc => ((hs.1 c).mp hc).trans h.1,
      fun hc => (hs.1 c).mpr (hc.trans h.2)⟩
  · intro c
    exact ⟨fun hc => h.2.trans ((hs.2 c).mp hc),
      fun hc => (hs.2 c).mpr (h.1.trans hc)⟩

theorem Represents.join {Δ H S T a b} (hs : @Represents Δ H S a)
    (ht : T.Represents b) (ha : Carrier Δ H a) (hb : Carrier Δ H b)
    (hab : (.join a b : CompareTy).WellShaped Δ) : (S.join T).Represents (.join a b) := by
  constructor
  · intro c
    constructor
    · intro hc
      apply LowerClosure.lift (core Δ H) hc (.principal _ (.join a b))
      rintro x (hx | hx) _ _
      · exact ((hs.1 x).mp hx).trans ((core Δ H).joinLeft ha hb hab)
      · exact ((ht.1 x).mp hx).trans ((core Δ H).joinRight ha hb hab)
    · intro hc
      apply (S.join T).lower.lower hc
      exact .join hab
        (.base ha hab.1 (Or.inl ((hs.1 a).mpr (.refl ha hab.1))))
        (.base hb hab.2.1 (Or.inr ((ht.1 b).mpr (.refl hb hab.2.1))))
  · intro c
    constructor
    · intro hc
      exact .joinLeast ((hs.2 c).mp hc.1) ((ht.2 c).mp hc.2)
    · intro hc
      exact ⟨(hs.2 c).mpr (((core Δ H).joinLeft ha hb hab).trans hc),
        (ht.2 c).mpr (((core Δ H).joinRight ha hb hab).trans hc)⟩

theorem Represents.meet {Δ H S T a b} (hs : @Represents Δ H S a)
    (ht : T.Represents b) (ha : Carrier Δ H a) (hb : Carrier Δ H b)
    (hab : (.meet a b : CompareTy).WellShaped Δ) : (S.meet T).Represents (.meet a b) := by
  constructor
  · intro c
    constructor
    · intro hc
      exact .meetGreatest ((hs.1 c).mp hc.1) ((ht.1 c).mp hc.2)
    · intro hc
      exact ⟨(hs.1 c).mpr (hc.trans ((core Δ H).meetLeft ha hb hab)),
        (ht.1 c).mpr (hc.trans ((core Δ H).meetRight ha hb hab))⟩
  · intro c
    constructor
    · intro hc
      apply UpperClosure.lift (core Δ H) hc (.principal _ (.meet a b))
      rintro x (hx | hx) _ _
      · exact ((core Δ H).meetLeft ha hb hab).trans ((hs.2 x).mp hx)
      · exact ((core Δ H).meetRight ha hb hab).trans ((ht.2 x).mp hx)
    · intro hc
      apply (S.meet T).upper.upper hc
      exact .meet hab
        (.base ha hab.1 (Or.inl ((hs.2 a).mpr (.refl ha hab.1))))
        (.base hb hab.2.1 (Or.inr ((ht.2 b).mpr (.refl hb hab.2.1))))

theorem Represents.modal_join {Δ H S T a b m}
    (hs : @Represents Δ H S (.modal a m)) (ht : T.Represents (.modal b m))
    (hab : ComparisonAlgebra.Compatible Δ a b) (hm : Entails Δ (.defined m)) :
    (S.join T).Represents (.modal (.join a b) m) := by
  have he : ComparisonAlgebra.Equation Δ (.modal (.join a b) m)
      (.join (.modal a m) (.modal b m)) := .modal true hab hm
  have hd := ComparisonDefinedCovers.equation_defined he
  apply (hs.join ht (carrier_modal_defined hab.2.1 hm)
    (carrier_modal_defined hab.2.2 hm) hab.1).equiv
  exact ⟨.atom (carrier_defined hd.2) (carrier_defined hd.1) (.equationRev he),
    .atom (carrier_defined hd.1) (carrier_defined hd.2) (.equation he)⟩

theorem Represents.modal_meet {Δ H S T a b m}
    (hs : @Represents Δ H S (.modal a m)) (ht : T.Represents (.modal b m))
    (hab : ComparisonAlgebra.Compatible Δ a b) (hm : Entails Δ (.defined m)) :
    (S.meet T).Represents (.modal (.meet a b) m) := by
  have he : ComparisonAlgebra.Equation Δ (.modal (.meet a b) m)
      (.meet (.modal a m) (.modal b m)) := .modal false hab hm
  have hd := ComparisonDefinedCovers.equation_defined he
  apply (hs.meet ht (carrier_modal_defined hab.2.1 hm)
    (carrier_modal_defined hab.2.2 hm) hab.1).equiv
  exact ⟨.atom (carrier_defined hd.2) (carrier_defined hd.1) (.equationRev he),
    .atom (carrier_defined hd.1) (carrier_defined hd.2) (.equation he)⟩

end Interpretation
end ModalityInference.ComparisonRawHeadRestriction
