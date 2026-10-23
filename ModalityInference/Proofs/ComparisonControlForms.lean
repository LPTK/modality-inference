import ModalityInference.ComparisonControlForms
import ModalityInference.Proofs.ComparisonRawHeadModeOrbits

/-! The executable reference family is exactly the existing complete family
of supported total controls. -/
namespace ModalityInference.ComparisonControlForms

open ComparisonControls

theorem band_eq (c : Channel) (e : BoolExpr) (p : Bool) :
    band c e p = ComparisonObserverProfiles.band c e p := by
  induction e generalizing p with
  | const b => rfl
  | atom i => rfl
  | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    cases p <;> simp only [band,ComparisonObserverProfiles.band,iha,ihb]

theorem truthForms_eq (is : List Nat) : truthForms is = ComparisonRawHeadModeOrbits.truthForms is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [truthForms,ComparisonRawHeadModeOrbits.truthForms,ih]
    rfl

theorem channelAtoms_eq (c : Channel) (names : List ModVar) :
    channelAtoms c names = ComparisonRawHeadModeOrbits.channelAtoms c names := by cases c <;> rfl

theorem representatives_eq (names : List ModVar) :
    representatives names = ComparisonRawHeadModeOrbits.representatives names := by
  simp only [representatives,ComparisonRawHeadModeOrbits.representatives,truthForms_eq,channelAtoms_eq]
  simp_rw [combine,band_eq]
  rfl

theorem representatives_total {Δ names r} (h : r ∈ representatives names) :
    Entails Δ (.defined r) :=
  ComparisonRawHeadModeOrbits.representatives_total (by simpa only [representatives_eq] using h)

theorem representatives_support {names r} (h : r ∈ representatives names) :
    r.vars ⊆ names.toFinset :=
  ComparisonRawHeadModeOrbits.representatives_support (by simpa only [representatives_eq] using h)

theorem representatives_complete {Δ : Bounds} {names : List ModVar} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names.toFinset) :
    ∃ r ∈ representatives names, Submode Δ m r ∧ Submode Δ r m := by
  simpa only [representatives_eq] using ComparisonRawHeadModeOrbits.representatives_complete hm hs

theorem representatives_length (names : List ModVar) :
    (representatives names).length = 2 ^ (2 ^ names.length + 2 * 2 ^ (2 * names.length)) := by
  simpa only [representatives_eq] using ComparisonRawHeadModeOrbits.representatives_length names

end ModalityInference.ComparisonControlForms
