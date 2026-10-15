import ModalityInference.Proofs.ComparisonPartialCapsuleProvenance

/-! At an atomic shape, partial carriers compare exactly by a literal frozen
capsule and the order of its total suffix. The downset model retains mode
composition while validating the guarded comparison algebra. -/

namespace ModalityInference.ComparisonPartialCapsuleScalar

open ComparisonPartialCapsule

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Token := CompareTy × ModExpr
abbrev Point := Token × Mode

def Down (S : Set Point) : Prop :=
  ∀ token m n, Mode.le m n = true → (token, n) ∈ S → (token, m) ∈ S

def principal (token : Token) (m : Mode) : Set Point :=
  {p | p.1 = token ∧ Mode.le p.2 m = true}

def action (m : Mode) (S : Set Point) : Set Point :=
  {p | ∃ q ∈ S, p.1 = q.1 ∧ Mode.le p.2 (q.2.compose m) = true}

theorem principal_down (token : Token) (m : Mode) : Down (principal token m) := by
  intro t a b hab hb
  exact ⟨hb.1, Mode.le_trans hab hb.2⟩

theorem action_down (m : Mode) (S : Set Point) : Down (action m S) := by
  intro t a b hab hb
  obtain ⟨q, hq, he, hbq⟩ := hb
  exact ⟨q, hq, he, Mode.le_trans hab hbq⟩

theorem action_mono {m n : Mode} {S T : Set Point}
    (hmn : Mode.le m n = true) (hst : S ⊆ T) : action m S ⊆ action n T := by
  intro p hp
  obtain ⟨q, hq, he, hpq⟩ := hp
  exact ⟨q, hst hq, he, Mode.le_trans hpq (Mode.compose_le_left q.2 hmn)⟩

theorem action_identity {S : Set Point} (hs : Down S) : action .identity S = S := by
  ext ⟨token, m⟩
  constructor
  · rintro ⟨⟨t, n⟩, hn, he, hm⟩
    cases he
    exact hs _ _ _ (by simpa only [Mode.compose_identity] using hm) hn
  · intro hm
    exact ⟨(token, m), hm, rfl, by simp⟩

theorem action_compose (m n : Mode) (S : Set Point) :
    action n (action m S) = action (m.compose n) S := by
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, hqr, hle⟩, hpq, hp⟩
    exact ⟨r, hr, hpq.trans hqr, by
      simpa only [Mode.compose_assoc] using Mode.le_trans hp (Mode.compose_le_right n hle)⟩
  · rintro ⟨r, hr, he, hp⟩
    exact ⟨(r.1, r.2.compose m), ⟨r, hr, rfl, Mode.le_refl _⟩, he,
      by simpa only [Mode.compose_assoc] using hp⟩

theorem action_principal (token : Token) (m n : Mode) :
    action n (principal token m) = principal token (m.compose n) := by
  ext p
  constructor
  · rintro ⟨q, ⟨hq, hqm⟩, hpq, hp⟩
    exact ⟨hpq.trans hq, Mode.le_trans hp (Mode.compose_le_right n hqm)⟩
  · intro hp
    exact ⟨(token, m), ⟨rfl, Mode.le_refl _⟩, hp.1, hp.2⟩

theorem action_empty (m : Mode) : action m ∅ = ∅ := by
  ext p
  simp [action]

def value (η : ModVar → Mode) (m : ModExpr) : Mode :=
  (m.eval (some ∘ η)).getD .identity

theorem value_compose {η : ModVar → Mode} {m n : ModExpr}
    (hm : m.WellFormed η) (hn : n.WellFormed η) :
    value η (.compose m n) = (value η m).compose (value η n) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hm
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hn
  simp [value, ModExpr.eval, hx, hy]

theorem value_submode {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    {m n : ModExpr} (h : Submode Δ m n) : Mode.le (value η m) (value η n) = true := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h.denote hη
  simpa only [value, hx, hy, Option.getD_some] using hxy


def denote (Δ : Bounds) (η : ModVar → Mode) : CompareTy → Set Point
  | .modal a (.compose m n) => denote Δ η (.modal (.modal a m) n)
  | .modal a m => if Entails Δ (.defined m) then action (value η m) (denote Δ η a)
      else principal (a, m) .identity
  | .join a b => denote Δ η a ∪ denote Δ η b
  | .meet a b => denote Δ η a ∩ denote Δ η b
  | _ => ∅
termination_by a => size a
decreasing_by
  all_goals simp_wf
  all_goals simp only [size, ComparisonPartialModes.expressionSize]
  all_goals first | omega | have := mode_size_pos m; omega

theorem denote_compose (Δ : Bounds) (η : ModVar → Mode) (a : CompareTy) (m n : ModExpr) :
    denote Δ η (.modal a (.compose m n)) = denote Δ η (.modal (.modal a m) n) := by
  rw [denote]

theorem denote_modal_total {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    {m : ModExpr} (hm : Entails Δ (.defined m)) (a : CompareTy) :
    denote Δ η (.modal a m) = action (value η m) (denote Δ η a) := by
  induction m generalizing a with
  | compose m n ihm ihn =>
    obtain ⟨hm, hn⟩ := Entails.defined_compose_iff.mp hm
    rw [denote_compose, ihn hn, ihm hm, action_compose, value_compose (hm η hη) (hn η hη)]
  | _ => rw [denote] <;> simp_all

theorem denote_down (Δ : Bounds) (η : ModVar → Mode) (a : CompareTy) : Down (denote Δ η a) := by
  match a with
  | .modal a m =>
    cases m
    case compose m n =>
      rw [denote_compose]
      exact denote_down Δ η (.modal (.modal a m) n)
    all_goals
      rw [denote]
      · split
        · exact action_down _ _
        · exact principal_down _ _
      · simp
  | .join a b =>
    rw [denote]
    intro token m n hmn h
    exact h.elim (fun h => Or.inl (denote_down Δ η a token m n hmn h))
      (fun h => Or.inr (denote_down Δ η b token m n hmn h))
  | .meet a b =>
    rw [denote]
    intro token m n hmn h
    exact ⟨denote_down Δ η a token m n hmn h.1, denote_down Δ η b token m n hmn h.2⟩
  | .var _ | .unit | .credit | .prod _ _ | .sum _ _ | .fn _ _ =>
    rw [denote] <;> simp [Down]
termination_by size a
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [size, ComparisonPartialModes.expressionSize]
  all_goals omega

theorem denote_identity {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    (a : CompareTy) : denote Δ η (.modal a .epsilon) = denote Δ η a := by
  rw [denote_modal_total hη (m := .epsilon) (fun _ _ => rfl)]
  exact action_identity (denote_down Δ η a)

theorem denote_defined {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    {a : CompareTy} (ha : a.DefinedUnder Δ) : denote Δ η a = ∅ := by
  induction a with
  | var | unit | credit | prod | sum | fn => rw [denote] <;> simp
  | modal a m ih =>
    have hd := CompareTy.definedUnder_modal_iff.mp ha
    rw [denote_modal_total hη hd.2, ih hd.1, action_empty]
  | join a b iha ihb =>
    have hd := CompareTy.definedUnder_join_iff.mp ha
    rw [denote, iha hd.1, ihb hd.2, Set.empty_union]
  | meet a b iha ihb =>
    have hd := CompareTy.definedUnder_meet_iff.mp ha
    rw [denote, iha hd.1, ihb hd.2, Set.empty_inter]

theorem shaped_sound {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {η : ModVar → Mode} (hη : ModeModels Δ η)
    {a b : CompareTy} (h : ShapedSubtype Δ a b) :
    Atomic (a.shape.subst ρ) → denote Δ η a ⊆ denote Δ η b := by
  induction h
  case prod | sum | fn => exact fun ha => False.elim ha
  case refl => exact fun _ => Set.Subset.rfl
  case trans hab hbc ihab ihbc =>
    intro ha
    exact (ihab ha).trans (ihbc (by rw [←hab.shape_equivalent ρ hρ]; exact ha))
  case bound a b hab =>
    intro _
    rw [denote_defined hη ((CompareTy.definedUnder_ofTy _ _).mpr (hΔ a b hab).1)]
    exact Set.empty_subset _
  case identity a ha => intro _; rw [denote_identity hη]
  case identityRev a ha => intro _; rw [denote_identity hη]
  case compose a m n ha => intro _; rw [denote_compose]
  case composeRev a m n ha => intro _; rw [denote_compose]
  case congr hab hm ih =>
    intro ha
    rw [denote_modal_total hη hm.defined.1, denote_modal_total hη hm.defined.2]
    exact action_mono (value_submode hη hm) (ih ha)
  case joinLeft a b hab => intro _; rw [denote]; exact Set.subset_union_left
  case joinRight a b hab => intro _; rw [denote]; exact Set.subset_union_right
  case joinLeast a b c hac hbc ihac ihbc =>
    intro ha
    rw [denote]
    exact Set.union_subset (ihac ha) (ihbc (by
      rw [hbc.shape_equivalent ρ hρ, ←hac.shape_equivalent ρ hρ]; exact ha))
  case meetLeft a b hab => intro _; rw [denote]; exact Set.inter_subset_left
  case meetRight a b hab => intro _; rw [denote]; exact Set.inter_subset_right
  case meetGreatest hab hac ihab ihac =>
    intro ha
    rw [denote]
    exact Set.subset_inter (ihab ha) (ihac ha)

theorem algebra_sound {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {η : ModVar → Mode} (hη : ModeModels Δ η)
    {a b : CompareTy} (h : AlgebraSubtype Δ a b) :
    Atomic (a.shape.subst ρ) → denote Δ η a ⊆ denote Δ η b := by
  induction h
  case shaped h => exact shaped_sound hΔ hρ hη h
  case trans hab hbc ihab ihbc =>
    intro ha
    exact (ihab ha).trans (ihbc (by rw [←hab.shape_equivalent ρ hρ]; exact ha))
  case equation he =>
    intro _
    rw [denote_defined hη (ComparisonDefinedCovers.equation_defined he).1]
    exact Set.empty_subset _
  case equationRev he =>
    intro _
    rw [denote_defined hη (ComparisonDefinedCovers.equation_defined he).2]
    exact Set.empty_subset _
  case congr hab hm ih =>
    intro ha
    rw [denote_modal_total hη hm.defined.1, denote_modal_total hη hm.defined.2]
    exact action_mono (value_submode hη hm) (ih ha)
  case prod | sum | fn => exact fun ha => False.elim ha
  case joinLeast a b c hac hbc ihac ihbc =>
    intro ha
    rw [denote]
    exact Set.union_subset (ihac ha) (ihbc (by
      rw [hbc.shape_equivalent ρ hρ, ←hac.shape_equivalent ρ hρ]; exact ha))
  case meetGreatest hab hac ihab ihac =>
    intro ha
    rw [denote]
    exact Set.subset_inter (ihab ha) (ihac ha)
  case clamp hba hat hm h₁ h₂ ih₁ ih₂ =>
    intro _
    rw [denote_defined hη (ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm).1]
    exact Set.empty_subset _
  case clampRev hba hat hm h₁ h₂ ih₁ ih₂ =>
    intro _
    rw [denote_defined hη (ComparisonDefinedCovers.clamp_endpoints_defined hba hat hm).2]
    exact Set.empty_subset _




def Frozen (Δ : Bounds) (token : Token) : Prop :=
  (¬Entails Δ (.defined token.2)) ∧ ∀ m n, token.2 ≠ .compose m n

theorem observe_frozen {Δ : Bounds} (a : CompareTy) {token : Token}
    (h : token ∈ observe Δ a) : Frozen Δ token := by
  match a with
  | .modal a m =>
    cases m
    case compose m n =>
      rw [observe_compose] at h
      exact observe_frozen (.modal (.modal a m) n) h
    all_goals
      rw [observe] at h
      · split at h
        · exact observe_frozen a h
        · next hn =>
          have he := Set.mem_singleton_iff.mp h
          subst token
          exact ⟨fun hd => hn (Or.inr hd), by simp⟩
      · simp
  | .join a b =>
    rw [observe] at h
    exact h.elim (observe_frozen a) (observe_frozen b)
  | .meet a b =>
    rw [observe] at h
    exact observe_frozen a h.1
  | .var _ | .unit | .credit | .prod _ _ | .sum _ _ | .fn _ _ =>
    rw [observe] at h <;> simp_all
termination_by size a
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [size, ComparisonPartialModes.expressionSize]
  all_goals omega

theorem denote_frozen {Δ : Bounds} (η : ModVar → Mode) {token : Token}
    (h : Frozen Δ token) :
    denote Δ η (.modal token.1 token.2) = principal token .identity := by
  obtain ⟨a, m⟩ := token
  cases m
  case compose m n => exact False.elim (h.2 m n rfl)
  all_goals rw [denote] <;> simp_all [Frozen]

theorem frozen_suffix_necessary {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {token : Token} (hf : Frozen Δ token) (ha : Atomic (token.1.shape.subst ρ))
    {m n : ModExpr} (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (h : AlgebraSubtype Δ (.modal (.modal token.1 token.2) m)
      (.modal (.modal token.1 token.2) n)) : Submode Δ m n := by
  apply Submode.valid
  intro η hη
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hn η hη)
  refine ⟨x, y, hx, hy, ?_⟩
  have hsub := algebra_sound hΔ hρ hη h ha
  rw [denote_modal_total hη hm, denote_modal_total hη hn,
    denote_frozen η hf, action_principal, action_principal, Mode.identity_compose,
    Mode.identity_compose] at hsub
  have hmem : (token, x) ∈ principal token (value η m) := by
    exact ⟨rfl, by simp [value, hx]⟩
  have hout := (hsub hmem).2
  simpa only [value, hy, Option.getD_some] using hout

theorem frozen_suffix_iff {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {token : Token} (hf : Frozen Δ token) (hs : token.1.WellShaped Δ)
    (ha : Atomic (token.1.shape.subst ρ))
    {m n : ModExpr} (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    AlgebraSubtype Δ (.modal (.modal token.1 token.2) m)
      (.modal (.modal token.1 token.2) n) ↔ Submode Δ m n :=
  ⟨frozen_suffix_necessary hΔ hρ hf ha hm hn,
    fun h => .congr (.refl hs) h⟩


/-- Normal partial capsules compare exactly by their literal boundary and the
order of their total suffixes. -/
theorem normal_compare_iff {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (sa : Normal Δ a) (sb : Normal Δ b)
    (ha : Atomic (a.shape.subst ρ)) :
    AlgebraSubtype Δ a b ↔ sa.token = sb.token ∧ Submode Δ sa.suffix sb.suffix := by
  have hf : Frozen Δ sa.token := observe_frozen a (sa.observation ▸ Set.mem_singleton _)
  have hatom : Atomic (sa.token.1.shape.subst ρ) := by
    change Atomic ((.modal (.modal sa.token.1 sa.token.2) sa.suffix : CompareTy).shape.subst ρ)
    rw [←sa.forward.shape_equivalent ρ hρ]
    exact ha
  constructor
  · intro hab
    have hsub := ComparisonPartialCapsule.algebra_sound hΔ hρ hab ha
    rw [sa.observation, sb.observation] at hsub
    have he : sa.token = sb.token := by
      simpa only [Set.mem_singleton_iff] using hsub (Set.mem_singleton _)
    refine ⟨he, ?_⟩
    have h : AlgebraSubtype Δ (.modal (.modal sa.token.1 sa.token.2) sa.suffix)
        (.modal (.modal sb.token.1 sb.token.2) sb.suffix) :=
      (AlgebraSubtype.shaped sa.backward).trans (hab.trans (.shaped sb.forward))
    rw [←he] at h
    exact frozen_suffix_necessary hΔ hρ hf hatom sa.total sb.total h
  · rintro ⟨he, hmode⟩
    have h : AlgebraSubtype Δ (.modal (.modal sa.token.1 sa.token.2) sa.suffix)
        (.modal (.modal sb.token.1 sb.token.2) sb.suffix) := by
      rw [←he]
      exact .congr (.refl sa.forward.wellShaped_right) hmode
    exact (AlgebraSubtype.shaped sa.forward).trans (h.trans (.shaped sb.backward))

/-- Shared source images produce shared suffix variables; each total occurrence
wrapper contributes composition to its scalar inequality. -/
theorem normal_context_iff {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (sa : Normal Δ a) (sb : Normal Δ b)
    (ha : Atomic (a.shape.subst ρ))
    {m n : ModExpr} (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    AlgebraSubtype Δ (.modal a m) (.modal b n) ↔
      sa.token = sb.token ∧ Submode Δ (.compose sa.suffix m) (.compose sb.suffix n) :=
  normal_compare_iff hΔ hρ (sa.modal hm) (sb.modal hn) ha

end
end ModalityInference.ComparisonPartialCapsuleScalar
