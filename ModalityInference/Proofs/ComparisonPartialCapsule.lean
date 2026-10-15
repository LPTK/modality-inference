import ModalityInference.Proofs.ComparisonPartialCarrierInterpretationSoundness
import ModalityInference.Proofs.ComparisonDefinedCoverMonotonicity
import ModalityInference.Proofs.ComparisonPartialModes

/-! Partial carriers of atomic shape retain a literal frozen modal boundary.
Total outer actions and root composition steps preserve this boundary; no
normalization is performed inside a partial annotation. -/

namespace ModalityInference.ComparisonPartialCapsule

open ComparisonPartialCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

def size : CompareTy → Nat
  | .var _ | .unit | .credit => 1
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => size a + size b + 1
  | .modal a m => size a + ComparisonPartialModes.expressionSize m

theorem mode_size_pos (m : ModExpr) : 0 < ComparisonPartialModes.expressionSize m := by
  cases m <;> simp [ComparisonPartialModes.expressionSize]

theorem size_pos (a : CompareTy) : 0 < size a := by
  induction a <;> simp only [size] <;> omega

def observe (Δ : Bounds) : CompareTy → Set (CompareTy × ModExpr)
  | .modal a (.compose m n) => observe Δ (.modal (.modal a m) n)
  | .modal a m => if m = .epsilon ∨ Entails Δ (.defined m) then observe Δ a else {(a, m)}
  | .join a b => observe Δ a ∪ observe Δ b
  | .meet a b => observe Δ a ∩ observe Δ b
  | _ => ∅
termination_by a => size a
decreasing_by
  all_goals simp_wf
  all_goals simp only [size, ComparisonPartialModes.expressionSize]
  all_goals first | omega | have := mode_size_pos m; omega

theorem observe_compose (Δ : Bounds) (a : CompareTy) (m n : ModExpr) :
    observe Δ (.modal a (.compose m n)) = observe Δ (.modal (.modal a m) n) := by
  rw [observe]

theorem observe_modal_total {Δ : Bounds} {m : ModExpr} (hm : Entails Δ (.defined m))
    (a : CompareTy) : observe Δ (.modal a m) = observe Δ a := by
  induction m generalizing a with
  | compose m n ihm ihn =>
    obtain ⟨hm, hn⟩ := Entails.defined_compose_iff.mp hm
    rw [observe_compose, ihn hn, ihm hm]
  | _ => rw [observe] <;> simp_all

theorem observe_identity (Δ : Bounds) (a : CompareTy) :
    observe Δ (.modal a .epsilon) = observe Δ a :=
  observe_modal_total (m := .epsilon) (fun _ _ => rfl) a

theorem observe_defined {Δ : Bounds} {a : CompareTy} (ha : a.DefinedUnder Δ) :
    observe Δ a = ∅ := by
  induction a with
  | var | unit | credit | prod | sum | fn => rw [observe] <;> simp
  | modal a m ih =>
    have hd := CompareTy.definedUnder_modal_iff.mp ha
    rw [observe_modal_total hd.2, ih hd.1]
  | join a b iha ihb =>
    have hd := CompareTy.definedUnder_join_iff.mp ha
    rw [observe, iha hd.1, ihb hd.2, Set.empty_union]
  | meet a b iha ihb =>
    have hd := CompareTy.definedUnder_meet_iff.mp ha
    rw [observe, iha hd.1, ihb hd.2, Set.empty_inter]

def Atomic : ComparisonShape → Prop
  | .var _ | .unit | .credit => True
  | _ => False

theorem shaped_sound {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (h : ShapedSubtype Δ a b) :
    Atomic (a.shape.subst ρ) → observe Δ a ⊆ observe Δ b := by
  induction h
  case prod | sum | fn => exact fun ha => False.elim ha
  case refl => exact fun _ => Set.Subset.rfl
  case trans hab hbc ihab ihbc =>
    intro ha
    exact (ihab ha).trans (ihbc (by rw [←hab.shape_equivalent ρ hρ]; exact ha))
  case bound a b hab =>
    intro _
    rw [observe_defined ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ a b hab).1)]
    exact Set.empty_subset _
  case identity a ha => intro _; rw [observe_identity]
  case identityRev a ha => intro _; rw [observe_identity]
  case compose a m n ha => intro _; rw [observe_compose]
  case composeRev a m n ha => intro _; rw [observe_compose]
  case congr hab hm ih =>
    intro ha
    simpa only [observe_modal_total hm.defined.1, observe_modal_total hm.defined.2] using ih ha
  case joinLeft a b hab => intro _; rw [observe]; exact Set.subset_union_left
  case joinRight a b hab => intro _; rw [observe]; exact Set.subset_union_right
  case joinLeast a b c hac hbc ihac ihbc =>
    intro ha
    rw [observe]
    exact Set.union_subset (ihac ha) (ihbc (by
      rw [hbc.shape_equivalent ρ hρ, ←hac.shape_equivalent ρ hρ]; exact ha))
  case meetLeft a b hab => intro _; rw [observe]; exact Set.inter_subset_left
  case meetRight a b hab => intro _; rw [observe]; exact Set.inter_subset_right
  case meetGreatest hab hac ihab ihac =>
    intro ha
    rw [observe]
    exact Set.subset_inter (ihab ha) (ihac ha)

theorem algebra_sound {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (h : AlgebraSubtype Δ a b) :
    Atomic (a.shape.subst ρ) → observe Δ a ⊆ observe Δ b := by
  induction h
  case shaped h => exact shaped_sound hΔ hρ h
  case trans hab hbc ihab ihbc =>
    intro ha
    exact (ihab ha).trans (ihbc (by rw [←hab.shape_equivalent ρ hρ]; exact ha))
  case equation he =>
    intro _
    rw [observe_defined (ComparisonDefinedCovers.equation_defined he).1]
    exact Set.empty_subset _
  case equationRev he =>
    intro _
    rw [observe_defined (ComparisonDefinedCovers.equation_defined he).2]
    exact Set.empty_subset _
  case congr hab hm ih =>
    intro ha
    simpa only [observe_modal_total hm.defined.1, observe_modal_total hm.defined.2] using ih ha
  case prod | sum | fn => exact fun ha => False.elim ha
  case joinLeast a b c hac hbc ihac ihbc =>
    intro ha
    rw [observe]
    exact Set.union_subset (ihac ha) (ihbc (by
      rw [hbc.shape_equivalent ρ hρ, ←hac.shape_equivalent ρ hρ]; exact ha))
  case meetGreatest hab hac ihab ihac =>
    intro ha
    rw [observe]
    exact Set.subset_inter (ihab ha) (ihac ha)
  case clamp hba hat hm h₁ h₂ ih₁ ih₂ =>
    intro _
    rw [observe_defined (ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm).1]
    exact Set.empty_subset _
  case clampRev hba hat hm h₁ h₂ ih₁ ih₂ =>
    intro _
    rw [observe_defined (ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm).2]
    exact Set.empty_subset _


theorem not_epsilon_of_partial {Δ : Bounds} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) : m ≠ .epsilon := by
  intro h
  subst m
  exact hm (fun _ _ => rfl)

theorem observe_modal_partial_singleton {Δ : Bounds} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (a : CompareTy) :
    ∃ token, observe Δ (.modal a m) = {token} := by
  have he := not_epsilon_of_partial hm
  induction m generalizing a with
  | compose m n ihm ihn =>
    rw [observe_compose]
    by_cases hn : Entails Δ (.defined n)
    · rw [observe_modal_total hn]
      have hm' : ¬Entails Δ (.defined m) :=
        fun h => hm (Entails.defined_compose_iff.mpr ⟨h, hn⟩)
      exact ihm hm' a (not_epsilon_of_partial hm')
    · exact ihn hn (.modal a m) (not_epsilon_of_partial hn)
  | _ => rw [observe] <;> simp_all


theorem carrier_partial_singleton {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {a : CompareTy} (hc : Carrier Δ a) (ha : Atomic (a.shape.subst ρ))
    (hn : ¬a.DefinedUnder Δ) : ∃ token, observe Δ a = {token} := by
  induction a with
  | var | unit | credit =>
    exact False.elim (hn (by simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]))
  | prod | sum | fn => exact False.elim ha
  | join a b _ _ => exact False.elim (hn (CompareTy.definedUnder_join_iff.mpr hc))
  | meet a b _ _ => exact False.elim (hn (CompareTy.definedUnder_meet_iff.mpr hc))
  | modal a m ih =>
    by_cases hm : Entails Δ (.defined m)
    · rw [observe_modal_total hm]
      exact ih hc ha (fun hd => hn (CompareTy.definedUnder_modal_iff.mpr ⟨hd, hm⟩))
    · exact observe_modal_partial_singleton hm a

theorem carrier_capsule_eq {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (ha : Carrier Δ a) (hb : Carrier Δ b)
    (hatom : Atomic (a.shape.subst ρ)) (hn : ¬a.DefinedUnder Δ)
    (hab : AlgebraSubtype Δ a b) :
    ∃ token, observe Δ a = {token} ∧ observe Δ b = {token} := by
  obtain ⟨p, hp⟩ := carrier_partial_singleton ha hatom hn
  have hnb : ¬b.DefinedUnder Δ := fun hd => hn ((ha.defined_iff hΔ hb hab).mpr hd)
  obtain ⟨q, hq⟩ := carrier_partial_singleton hb
    (by rw [←hab.shape_equivalent ρ hρ]; exact hatom) hnb
  have hsub := algebra_sound hΔ hρ hab hatom
  rw [hp, hq] at hsub
  have hpq : p = q := by simpa only [Set.mem_singleton_iff] using hsub (by simp)
  exact ⟨p, hp, hpq ▸ hq⟩

end
end ModalityInference.ComparisonPartialCapsule
