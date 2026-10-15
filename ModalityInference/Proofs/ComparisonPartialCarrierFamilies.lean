import ModalityInference.Proofs.ComparisonPartialCarrierCut
import ModalityInference.Proofs.ComparisonPartialCovers

namespace ModalityInference.ComparisonPartialCarrier

open ComparisonPartialCovers

/-- The partial lattice structure contains one carrier per lower or upper
boundary; lattice nodes inside the carriers themselves are defined. -/
inductive FamilyForm (Δ : Bounds) (lowerArity upperArity : Nat) : CompareTy → Prop where
  | carrier {a} : Carrier Δ a → FamilyForm Δ lowerArity upperArity a
  | lower {head rest} : (∀ c ∈ head :: rest, Carrier Δ c) →
      (head :: rest).length = lowerArity →
      FamilyForm Δ lowerArity upperArity (ComparisonInterpolation.join head rest)
  | upper {head rest} : (∀ c ∈ head :: rest, Carrier Δ c) →
      (head :: rest).length = upperArity →
      FamilyForm Δ lowerArity upperArity (ComparisonInterpolation.meet head rest)

 theorem lower_cover_list {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (ds : List Demand) {w : CompareTy}
    (hs : ∀ d ∈ ds, Carrier Δ d.endpoint)
    (hw : ∀ d ∈ ds, Lower Δ d w) :
    ∃ cs : List CompareTy, cs.length = ds.length ∧
      (∀ c ∈ cs, Carrier Δ c ∧ AlgebraSubtype Δ c w) ∧
      (∀ d ∈ ds, ∃ c ∈ cs, Lower Δ d c) := by
  induction ds with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons d ds ih =>
    obtain ⟨c, hc, hcw, hdc⟩ := carrier_lower_modal_cover_general hΔ
      (hs d (by simp)) (hw d (by simp))
    obtain ⟨cs, hlen, hcs, hdcs⟩ := ih
      (fun d hd => hs d (by simp [hd])) (fun d hd => hw d (by simp [hd]))
    refine ⟨c :: cs, by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hc, hcw⟩
      · exact hcs x hx
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨c, by simp, hdc⟩
      · obtain ⟨c', hc', hxc'⟩ := hdcs x hx
        exact ⟨c', by simp [hc'], hxc'⟩

 theorem upper_cover_list {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (ds : List Demand) {w : CompareTy}
    (hs : ∀ d ∈ ds, Carrier Δ d.endpoint)
    (hw : ∀ d ∈ ds, Upper Δ d w) :
    ∃ cs : List CompareTy, cs.length = ds.length ∧
      (∀ c ∈ cs, Carrier Δ c ∧ AlgebraSubtype Δ w c) ∧
      (∀ d ∈ ds, ∃ c ∈ cs, Upper Δ d c) := by
  induction ds with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons d ds ih =>
    obtain ⟨c, hc, hwc, hcd⟩ := carrier_upper_modal_cover_general hΔ
      (hs d (by simp)) (hw d (by simp))
    obtain ⟨cs, hlen, hcs, hdcs⟩ := ih
      (fun d hd => hs d (by simp [hd])) (fun d hd => hw d (by simp [hd]))
    refine ⟨c :: cs, by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨hc, hwc⟩
      · exact hcs x hx
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨c, by simp, hcd⟩
      · obtain ⟨c', hc', hxc'⟩ := hdcs x hx
        exact ⟨c', by simp [hc'], hxc'⟩

/-- Arbitrary finite acted carrier intervals admit a bounded partial-lattice
form. Frozen actions force the witness itself to be a carrier; otherwise the
finite lower or upper cover family preserves every interval obligation. -/
theorem finite_family_normal_form {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (lowers uppers : List Demand) {w : CompareTy}
    (hl : ∀ d ∈ lowers, Carrier Δ d.endpoint)
    (hu : ∀ d ∈ uppers, Carrier Δ d.endpoint)
    (hwl : ∀ d ∈ lowers, Lower Δ d w)
    (hwu : ∀ d ∈ uppers, Upper Δ d w) :
    ∃ t, t.WellShaped Δ ∧ FamilyForm Δ lowers.length uppers.length t ∧
      (∀ d ∈ lowers, Lower Δ d t) ∧ (∀ d ∈ uppers, Upper Δ d t) := by
  classical
  by_cases hlt : ∀ d ∈ lowers, Total Δ d
  · by_cases hut : ∀ d ∈ uppers, Total Δ d
    · cases lowers with
      | nil =>
        cases uppers with
        | nil => exact ⟨.unit, True.intro, .carrier True.intro, by simp, by simp⟩
        | cons u us =>
          obtain ⟨cs, hlen, hcs, hdcs⟩ := upper_cover_list hΔ (u :: us) hu hwu
          cases cs with
          | nil => simp at hlen
          | cons c cs =>
            have hc : ∀ t ∈ c :: cs, AlgebraSubtype Δ w t := fun t ht => (hcs t ht).2
            have hshape := (meet_cover hc).wellShaped_right
            refine ⟨ComparisonInterpolation.meet c cs, hshape,
              .upper (fun t ht => (hcs t ht).1) hlen, by simp, ?_⟩
            intro d hd
            exact upper_meet hshape (hut d hd) (hdcs d hd)
      | cons l ls =>
        obtain ⟨cs, hlen, hcs, hdcs⟩ := lower_cover_list hΔ (l :: ls) hl hwl
        cases cs with
        | nil => simp at hlen
        | cons c cs =>
          have hc : ∀ t ∈ c :: cs, AlgebraSubtype Δ t w := fun t ht => (hcs t ht).2
          refine ⟨ComparisonInterpolation.join c cs, (join_cover hc).wellShaped_left,
            .lower (fun t ht => (hcs t ht).1) hlen, ?_, ?_⟩
          · intro d hd
            exact lower_join hc (hlt d hd) (hdcs d hd)
          · intro d hd
            exact lower_join_preserves_upper hc (hut d hd) (hwu d hd)
    · push_neg at hut
      obtain ⟨d, hd, hnt⟩ := hut
      have hn : ¬Entails Δ (.defined d.action) := fun h => hnt (.refl h)
      have hw := carrier_of_partial_modal_lower hΔ (hu d hd) hn (hwu d hd)
      exact ⟨w, (hwu d hd).wellShaped_left, .carrier hw, hwl, hwu⟩
  · push_neg at hlt
    obtain ⟨d, hd, hnt⟩ := hlt
    have hn : ¬Entails Δ (.defined d.action) := fun h => hnt (.refl h)
    have hw := carrier_of_partial_modal_upper hΔ (hl d hd) hn (hwl d hd)
    exact ⟨w, (hwl d hd).wellShaped_right, .carrier hw, hwl, hwu⟩

end ModalityInference.ComparisonPartialCarrier
