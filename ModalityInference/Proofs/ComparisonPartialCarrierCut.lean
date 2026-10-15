import ModalityInference.Proofs.ComparisonPartialCarrierRules
import ModalityInference.Proofs.ComparisonPartialCarrierStructural
import ModalityInference.Proofs.ComparisonPartialCarrierModal
import ModalityInference.Proofs.ComparisonDefinedCoverMonotonicity

namespace ModalityInference.ComparisonPartialCarrier

 theorem shaped_related {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) {a b : CompareTy}
    (h : ShapedSubtype Δ a b) : Related Δ a b := by
  induction h with
  | refl => exact .refl _
  | trans _ _ ihab ihbc => exact ihab.trans ihbc
  | bound hb => exact .carriers (Carrier.of_public _) (Carrier.of_public _) (.shaped (.bound hb))
  | identity => exact .identity hΔ _
  | identityRev => exact .identityRev hΔ _
  | compose hs => exact (Related.compose hΔ hs _ _).1
  | composeRev hs => exact (Related.compose hΔ hs _ _).2
  | congr _ hm ih => exact ih.congr hm
  | prod hac hbd ihac ihbd => exact .prod hΔ (.shaped hac) (.shaped hbd) ihac ihbd
  | sum hac hbd ihac ihbd => exact .sum hΔ (.shaped hac) (.shaped hbd) ihac ihbd
  | fn _ _ hm ihca ihbd => exact .fn hΔ ihca ihbd hm
  | joinLeft => exact .joinLeft _ _
  | joinRight => exact .joinRight _ _
  | joinLeast _ _ iha ihb => exact iha.joinLeast ihb
  | meetLeft => exact .meetLeft _ _
  | meetRight => exact .meetRight _ _
  | meetGreatest _ _ iha ihb => exact iha.meetGreatest ihb

 theorem algebra_related {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined) {a b : CompareTy}
    (h : AlgebraSubtype Δ a b) : Related Δ a b := by
  induction h with
  | shaped h => exact shaped_related hΔ h
  | trans _ _ ihab ihbc => exact ihab.trans ihbc
  | equation he =>
    have hd := ComparisonDefinedCovers.equation_defined he
    exact .carriers (.of_defined hd.1) (.of_defined hd.2) (.equation he)
  | equationRev he =>
    have hd := ComparisonDefinedCovers.equation_defined he
    exact .carriers (.of_defined hd.2) (.of_defined hd.1) (.equationRev he)
  | congr _ hm ih => exact ih.congr hm
  | prod hac hbd ihac ihbd => exact .prod hΔ hac hbd ihac ihbd
  | sum hac hbd ihac ihbd => exact .sum hΔ hac hbd ihac ihbd
  | fn _ _ hm ihca ihbd => exact .fn hΔ ihca ihbd hm
  | joinLeast _ _ iha ihb => exact iha.joinLeast ihb
  | meetGreatest _ _ iha ihb => exact iha.meetGreatest ihb
  | clamp hba hat hm hba' hat' _ _ =>
    have hd := ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm
    exact .carriers (.of_defined hd.1) (.of_defined hd.2) (.clamp hba hat hm hba' hat')
  | clampRev hba hat hm hba' hat' _ _ =>
    have hd := ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm
    exact .carriers (.of_defined hd.2) (.of_defined hd.1) (.clampRev hba hat hm hba' hat')

/-- Every lower carrier boundary admits a carrier cover before a total action. -/
theorem carrier_lower_modal_cover {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a w : CompareTy} {m : ModExpr} (ha : Carrier Δ a)
    (hm : Entails Δ (.defined m)) (h : AlgebraSubtype Δ a (.modal w m)) :
    ∃ c, Carrier Δ c ∧ AlgebraSubtype Δ c w ∧ AlgebraSubtype Δ a (.modal c m) := by
  have hi := (algebra_related hΔ h).1 a (denote_self ha h.wellShaped_left).1
  obtain ⟨c, hc, hac⟩ := denote_modal_lower_factor hΔ hm hi
  exact ⟨c, (denote Δ w).lower.carrier c hc, (denote_sound (a := w) h.wellShaped_right).1 c hc, hac⟩

/-- The dual cover retains a carrier upper boundary after a total action. -/
theorem carrier_upper_modal_cover {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a w : CompareTy} {m : ModExpr} (ha : Carrier Δ a)
    (hm : Entails Δ (.defined m)) (h : AlgebraSubtype Δ (.modal w m) a) :
    ∃ c, Carrier Δ c ∧ AlgebraSubtype Δ w c ∧ AlgebraSubtype Δ (.modal c m) a := by
  have hi := (algebra_related hΔ h).2 a (denote_self ha h.wellShaped_right).2
  obtain ⟨c, hc, hca⟩ := denote_modal_upper_factor hΔ hm hi
  exact ⟨c, (denote Δ w).upper.carrier c hc, (denote_sound (a := w) h.wellShaped_left).2 c hc, hca⟩

/-- Partial carriers are join-prime, even across arbitrary internal cuts. -/
theorem carrier_partial_join_prime {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a x y : CompareTy} (ha : Carrier Δ a) (hn : ¬a.DefinedUnder Δ)
    (h : AlgebraSubtype Δ a (.join x y)) :
    AlgebraSubtype Δ a x ∨ AlgebraSubtype Δ a y := by
  have hi := (algebra_related hΔ h).1 a (denote_self ha h.wellShaped_left).1
  obtain ⟨c, hc, hac⟩ := LowerClosure.partial hΔ hi hn
  rcases hc with hc | hc
  · exact .inl (hac.trans ((denote_sound h.wellShaped_right.1).1 c hc))
  · exact .inr (hac.trans ((denote_sound h.wellShaped_right.2.1).1 c hc))

/-- Partial carriers are meet-prime in the dual comparison direction. -/
theorem carrier_partial_meet_prime {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a x y : CompareTy} (ha : Carrier Δ a) (hn : ¬a.DefinedUnder Δ)
    (h : AlgebraSubtype Δ (.meet x y) a) :
    AlgebraSubtype Δ x a ∨ AlgebraSubtype Δ y a := by
  have hi := (algebra_related hΔ h).2 a (denote_self ha h.wellShaped_right).2
  obtain ⟨c, hc, hca⟩ := UpperClosure.partial hΔ hi hn
  rcases hc with hc | hc
  · exact .inl (((denote_sound h.wellShaped_left.1).2 c hc).trans hca)
  · exact .inr (((denote_sound h.wellShaped_left.2.1).2 c hc).trans hca)

/-- A partial carrier below an acted join selects one uniform branch. -/
theorem carrier_partial_modal_join_prime {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a x y : CompareTy} {m : ModExpr} (ha : Carrier Δ a) (hn : ¬a.DefinedUnder Δ)
    (hm : Entails Δ (.defined m)) (h : AlgebraSubtype Δ a (.modal (.join x y) m)) :
    AlgebraSubtype Δ a (.modal x m) ∨ AlgebraSubtype Δ a (.modal y m) := by
  obtain ⟨c, hc, hcxy, hac⟩ := carrier_lower_modal_cover hΔ ha hm h
  have hcn : ¬c.DefinedUnder Δ := fun hd =>
    hn (ha.defined_of_below hΔ (CompareTy.definedUnder_modal_iff.mpr ⟨hd, hm⟩) hac)
  rcases carrier_partial_join_prime hΔ hc hcn hcxy with hx | hy
  · exact .inl (hac.trans (.congr hx (.refl hm)))
  · exact .inr (hac.trans (.congr hy (.refl hm)))

theorem carrier_partial_modal_meet_prime {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a x y : CompareTy} {m : ModExpr} (ha : Carrier Δ a) (hn : ¬a.DefinedUnder Δ)
    (hm : Entails Δ (.defined m)) (h : AlgebraSubtype Δ (.modal (.meet x y) m) a) :
    AlgebraSubtype Δ (.modal x m) a ∨ AlgebraSubtype Δ (.modal y m) a := by
  obtain ⟨c, hc, hxyc, hca⟩ := carrier_upper_modal_cover hΔ ha hm h
  have hcn : ¬c.DefinedUnder Δ := fun hd =>
    hn (ha.defined_of_above hΔ (CompareTy.definedUnder_modal_iff.mpr ⟨hd, hm⟩) hca)
  rcases carrier_partial_meet_prime hΔ hc hcn hxyc with hx | hy
  · exact .inl ((AlgebraSubtype.congr hx (.refl hm)).trans hca)
  · exact .inr ((AlgebraSubtype.congr hy (.refl hm)).trans hca)

/-- A frozen outer action exposes the literal carrier status of its operand. -/
theorem carrier_of_partial_modal_upper {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a w : CompareTy} {m : ModExpr} (ha : Carrier Δ a)
    (hm : ¬Entails Δ (.defined m)) (h : AlgebraSubtype Δ a (.modal w m)) : Carrier Δ w :=
  denote_partial_lower_carrier hm
    ((algebra_related hΔ h).1 a (denote_self ha h.wellShaped_left).1)

theorem carrier_of_partial_modal_lower {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a w : CompareTy} {m : ModExpr} (ha : Carrier Δ a)
    (hm : ¬Entails Δ (.defined m)) (h : AlgebraSubtype Δ (.modal w m) a) : Carrier Δ w :=
  denote_partial_upper_carrier hm
    ((algebra_related hΔ h).2 a (denote_self ha h.wellShaped_right).2)

/-- Carrier cover extraction respects both total and frozen partial actions. -/
theorem carrier_lower_modal_cover_general {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a w : CompareTy} {m : ModExpr} (ha : Carrier Δ a)
    (h : AlgebraSubtype Δ a (.modal w m)) :
    ∃ c, Carrier Δ c ∧ AlgebraSubtype Δ c w ∧ AlgebraSubtype Δ a (.modal c m) := by
  by_cases hm : Entails Δ (.defined m)
  · exact carrier_lower_modal_cover hΔ ha hm h
  · exact ⟨w, carrier_of_partial_modal_upper hΔ ha hm h, .refl h.wellShaped_right, h⟩

theorem carrier_upper_modal_cover_general {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a w : CompareTy} {m : ModExpr} (ha : Carrier Δ a)
    (h : AlgebraSubtype Δ (.modal w m) a) :
    ∃ c, Carrier Δ c ∧ AlgebraSubtype Δ w c ∧ AlgebraSubtype Δ (.modal c m) a := by
  by_cases hm : Entails Δ (.defined m)
  · exact carrier_upper_modal_cover hΔ ha hm h
  · exact ⟨w, carrier_of_partial_modal_lower hΔ ha hm h, .refl h.wellShaped_left, h⟩

theorem public_partial_modal_join_prime {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a : Ty} {x y : CompareTy} {m : ModExpr} (ha : ¬a.DefinedUnder Δ)
    (hm : Entails Δ (.defined m)) (h : AlgebraSubtype Δ (.ofTy a) (.modal (.join x y) m)) :
    AlgebraSubtype Δ (.ofTy a) (.modal x m) ∨ AlgebraSubtype Δ (.ofTy a) (.modal y m) :=
  carrier_partial_modal_join_prime hΔ (Carrier.of_public a)
    (fun h => ha ((CompareTy.definedUnder_ofTy _ _).mp h)) hm h

theorem public_partial_modal_meet_prime {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a : Ty} {x y : CompareTy} {m : ModExpr} (ha : ¬a.DefinedUnder Δ)
    (hm : Entails Δ (.defined m)) (h : AlgebraSubtype Δ (.modal (.meet x y) m) (.ofTy a)) :
    AlgebraSubtype Δ (.modal x m) (.ofTy a) ∨ AlgebraSubtype Δ (.modal y m) (.ofTy a) :=
  carrier_partial_modal_meet_prime hΔ (Carrier.of_public a)
    (fun h => ha ((CompareTy.definedUnder_ofTy _ _).mp h)) hm h

end ModalityInference.ComparisonPartialCarrier
