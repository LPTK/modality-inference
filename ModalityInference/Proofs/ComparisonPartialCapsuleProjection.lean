import ModalityInference.Proofs.ComparisonPartialCapsuleScalar

/-! Mixed partial intervals of atomic shape reconstruct one common capsule with
one shared total suffix. Projection computes that suffix through arbitrary
internal lattice nesting, preserving every boundary demand simultaneously. -/

namespace ModalityInference.ComparisonPartialCapsuleScalar

open ComparisonPartialCapsule
open ComparisonLattice (mode_join_le mode_le_meet)

noncomputable section
attribute [local instance] Classical.propDecidable

structure SliceSup (token : Token) (S : Set Point) (q : Mode) : Prop where
  nonempty : ∃ m, (token, m) ∈ S
  upper : ∀ m, (token, m) ∈ S → Mode.le m q = true
  least : ∀ r, (∀ m, (token, m) ∈ S → Mode.le m r = true) → Mode.le q r = true

theorem SliceSup.principal (token : Token) (q : Mode) :
    SliceSup token (principal token q) q :=
  ⟨⟨q, rfl, Mode.le_refl _⟩, fun _ h => h.2,
    fun _ h => h q ⟨rfl, Mode.le_refl _⟩⟩

theorem SliceSup.union {token : Token} {S T : Set Point} {q r : Mode}
    (hs : SliceSup token S q) (ht : SliceSup token T r) :
    SliceSup token (S ∪ T) (q.join r) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hs.nonempty
    exact ⟨m, Or.inl hm⟩
  · intro m hm
    have hq := (mode_join_le q r (q.join r)).mp (Mode.le_refl _)
    exact hm.elim (fun hm => Mode.le_trans (hs.upper m hm) hq.1)
      (fun hm => Mode.le_trans (ht.upper m hm) hq.2)
  · intro p hp
    exact (mode_join_le q r p).mpr
      ⟨hs.least p (fun m hm => hp m (Or.inl hm)), ht.least p (fun m hm => hp m (Or.inr hm))⟩

def implication (q r : Mode) : Mode :=
  ⟨!q.isLocal || r.isLocal, !q.once || r.once, !q.unique && r.unique⟩

theorem meet_le_iff_implication (p q r : Mode) :
    Mode.le (p.meet q) r = true ↔ Mode.le p (implication q r) = true := by
  simp only [Mode.le_iff, Mode.meet, implication, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff]
  tauto

theorem meet_comm (p q : Mode) : p.meet q = q.meet p := by
  cases p; cases q; simp [Mode.meet, Bool.and_comm, Bool.or_comm]

theorem SliceSup.inter {token : Token} {S T : Set Point} {q r : Mode}
    (hS : Down S) (hT : Down T)
    (hs : SliceSup token S q) (ht : SliceSup token T r) :
    SliceSup token (S ∩ T) (q.meet r) := by
  have hmem {m n : Mode} (hm : (token, m) ∈ S) (hn : (token, n) ∈ T) :
      (token, m.meet n) ∈ S ∩ T := by
    have hh := (mode_le_meet (m.meet n) m n).mp (Mode.le_refl _)
    exact ⟨hS _ _ _ hh.1 hm, hT _ _ _ hh.2 hn⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hs.nonempty
    obtain ⟨n, hn⟩ := ht.nonempty
    exact ⟨m.meet n, hmem hm hn⟩
  · intro m hm
    exact (mode_le_meet m q r).mpr ⟨hs.upper m hm.1, ht.upper m hm.2⟩
  · intro p hp
    have hq : ∀ n, (token, n) ∈ T → Mode.le (q.meet n) p = true := by
      intro n hn
      apply (meet_le_iff_implication _ _ _).mpr
      exact hs.least _ (fun m hm => (meet_le_iff_implication _ _ _).mp (hp _ (hmem hm hn)))
    rw [meet_comm]
    apply (meet_le_iff_implication _ _ _).mpr
    exact ht.least _ (fun n hn => (meet_le_iff_implication _ _ _).mp
      (by rw [meet_comm]; exact hq n hn))

theorem SliceSup.action {token : Token} {S : Set Point} {q : Mode}
    (hs : SliceSup token S q) (m : Mode) : SliceSup token (action m S) (q.compose m) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := hs.nonempty
    exact ⟨n.compose m, (token, n), hn, rfl, Mode.le_refl _⟩
  · rintro n ⟨⟨t, p⟩, hp, he, hnp⟩
    cases he
    exact Mode.le_trans hnp (Mode.compose_le_right m (hs.upper p hp))
  · intro r hr
    obtain ⟨n, hn⟩ := hs.nonempty
    have hnr := hr (n.compose m) ⟨(token, n), hn, rfl, Mode.le_refl _⟩
    obtain ⟨s, hms, _⟩ := (Mode.le_rightResidual_iff n m r).mpr hnr
    apply (Mode.le_rightResidual_iff q m r).mp
    refine ⟨s, hms, hs.least s ?_⟩
    intro p hp
    have hpr := hr (p.compose m) ⟨(token, p), hp, rfl, Mode.le_refl _⟩
    obtain ⟨s', hs', hps⟩ := (Mode.le_rightResidual_iff p m r).mpr hpr
    cases Option.some.inj (hms.symm.trans hs')
    exact hps


theorem SliceSup.congr {token : Token} {S T : Set Point} {q : Mode}
    (hs : SliceSup token S q) (he : ∀ m, (token, m) ∈ S ↔ (token, m) ∈ T) :
    SliceSup token T q := by
  refine ⟨?_, fun m hm => hs.upper m ((he m).mpr hm), ?_⟩
  · obtain ⟨m, hm⟩ := hs.nonempty
    exact ⟨m, (he m).mp hm⟩
  · intro r hr
    exact hs.least r (fun m hm => hr m ((he m).mp hm))

def joinOption : Option ModExpr → Option ModExpr → Option ModExpr
  | none, n => n
  | m, none => m
  | some m, some n => some (.join m n)

def meetOption : Option ModExpr → Option ModExpr → Option ModExpr
  | some m, some n => some (.meet m n)
  | _, _ => none

def SliceSpec (Δ : Bounds) (η : ModVar → Mode) (token : Token) (S : Set Point) :
    Option ModExpr → Prop
  | none => ∀ m, (token, m) ∉ S
  | some q => Entails Δ (.defined q) ∧ SliceSup token S (value η q)

theorem total_join {Δ : Bounds} {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    Entails Δ (.defined (.join m n)) := by
  intro η hη
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hn η hη)
  simp [ModExpr.WellFormed, ModExpr.eval, hx, hy]

theorem total_meet {Δ : Bounds} {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n)) :
    Entails Δ (.defined (.meet m n)) := by
  intro η hη
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hn η hη)
  simp [ModExpr.WellFormed, ModExpr.eval, hx, hy]

theorem value_join {η : ModVar → Mode} {m n : ModExpr}
    (hm : m.WellFormed η) (hn : n.WellFormed η) :
    value η (.join m n) = (value η m).join (value η n) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hm
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hn
  simp [value, ModExpr.eval, hx, hy]

theorem value_meet {η : ModVar → Mode} {m n : ModExpr}
    (hm : m.WellFormed η) (hn : n.WellFormed η) :
    value η (.meet m n) = (value η m).meet (value η n) := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hm
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hn
  simp [value, ModExpr.eval, hx, hy]

theorem SliceSpec.union {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    {token : Token} {S T : Set Point} {m n : Option ModExpr}
    (hs : SliceSpec Δ η token S m) (ht : SliceSpec Δ η token T n) :
    SliceSpec Δ η token (S ∪ T) (joinOption m n) := by
  cases m with
  | none =>
    cases n with
    | none => intro p hp; exact hp.elim (hs p) (ht p)
    | some n =>
      refine ⟨ht.1, ht.2.congr ?_⟩
      intro p
      simp only [Set.mem_union]
      exact ⟨Or.inr, fun h => h.elim (fun h => (hs p h).elim) id⟩
  | some m =>
    cases n with
    | none =>
      refine ⟨hs.1, hs.2.congr ?_⟩
      intro p
      simp only [Set.mem_union]
      exact ⟨Or.inl, fun h => h.elim id (fun h => (ht p h).elim)⟩
    | some n =>
      refine ⟨total_join hs.1 ht.1, ?_⟩
      rw [value_join (hs.1 η hη) (ht.1 η hη)]
      exact hs.2.union ht.2

theorem SliceSpec.inter {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    {token : Token} {S T : Set Point} {m n : Option ModExpr}
    (hS : Down S) (hT : Down T)
    (hs : SliceSpec Δ η token S m) (ht : SliceSpec Δ η token T n) :
    SliceSpec Δ η token (S ∩ T) (meetOption m n) := by
  cases m with
  | none => cases n <;> exact fun p hp => hs p hp.1
  | some m =>
    cases n with
    | none => exact fun p hp => ht p hp.2
    | some n =>
      refine ⟨total_meet hs.1 ht.1, ?_⟩
      rw [value_meet (hs.1 η hη) (ht.1 η hη)]
      exact hs.2.inter hS hT ht.2

theorem SliceSpec.action {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    {token : Token} {S : Set Point} {q : Option ModExpr}
    (hs : SliceSpec Δ η token S q) {m : ModExpr} (hm : Entails Δ (.defined m)) :
    SliceSpec Δ η token (action (value η m) S) (q.map (ModExpr.compose · m)) := by
  cases q with
  | none =>
    rintro p ⟨⟨t, r⟩, hr, he, _⟩
    cases he
    exact hs r hr
  | some q =>
    refine ⟨Entails.defined_compose_iff.mpr ⟨hs.1, hm⟩, ?_⟩
    rw [value_compose (hs.1 η hη) (hm η hη)]
    exact hs.2.action _


/-- The supremum of one literal capsule's semantic slice. Absence is tracked
separately because total actions need not preserve an empty slice's supremum. -/
def project (Δ : Bounds) (token : Token) : CompareTy → Option ModExpr
  | .modal a (.compose m n) => project Δ token (.modal (.modal a m) n)
  | .modal a m => if Entails Δ (.defined m) then (project Δ token a).map (ModExpr.compose · m)
      else if (a, m) = token then some .epsilon else none
  | .join a b => joinOption (project Δ token a) (project Δ token b)
  | .meet a b => meetOption (project Δ token a) (project Δ token b)
  | _ => none
termination_by a => ComparisonPartialCapsule.size a
decreasing_by
  all_goals simp_wf
  all_goals simp only [ComparisonPartialCapsule.size, ComparisonPartialModes.expressionSize]
  all_goals first | omega | have := mode_size_pos m; omega

theorem project_spec {Δ : Bounds} {η : ModVar → Mode} (hη : ModeModels Δ η)
    (token : Token) (a : CompareTy) :
    SliceSpec Δ η token (denote Δ η a) (project Δ token a) := by
  match a with
  | .modal a m =>
    cases m
    case compose m n =>
      rw [project, denote_compose]
      exact project_spec hη token (.modal (.modal a m) n)
    all_goals
      rw [project]
      · rw [denote]
        · split
          · next hm => exact (project_spec hη token a).action hη hm
          · split
            · next he =>
              cases he
              exact ⟨(fun _ _ => rfl), SliceSup.principal _ _⟩
            · next he =>
              intro p hp
              exact he hp.1.symm
        · simp
      · simp
  | .join a b =>
    rw [project, denote]
    exact (project_spec hη token a).union hη (project_spec hη token b)
  | .meet a b =>
    rw [project, denote]
    exact (project_spec hη token a).inter hη (denote_down _ _ a) (denote_down _ _ b)
      (project_spec hη token b)
  | .var _ | .unit | .credit | .prod _ _ | .sum _ _ | .fn _ _ =>
    rw [project, denote] <;> simp [SliceSpec]
termination_by ComparisonPartialCapsule.size a
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [ComparisonPartialCapsule.size, ComparisonPartialModes.expressionSize]
  all_goals omega


theorem joinOption_isSome (m n : Option ModExpr) :
    (joinOption m n).isSome = true ↔ m.isSome = true ∨ n.isSome = true := by
  cases m <;> cases n <;> simp [joinOption]

theorem meetOption_isSome (m n : Option ModExpr) :
    (meetOption m n).isSome = true ↔ m.isSome = true ∧ n.isSome = true := by
  cases m <;> cases n <;> simp [meetOption]

theorem project_present (Δ : Bounds) (token : Token) (a : CompareTy) :
    (project Δ token a).isSome = true ↔ token ∈ observe Δ a := by
  match a with
  | .modal a m =>
    cases m
    case compose m n =>
      rw [project, observe_compose]
      exact project_present Δ token (.modal (.modal a m) n)
    all_goals
      rw [project, observe]
      · split
        · next hm => simp [hm, project_present Δ token a]
        · next hm =>
          have he := not_epsilon_of_partial hm
          simp only [hm, he, false_or, if_false, Set.mem_singleton_iff]
          split
          · next ht => simp [ht]
          · next ht =>
            simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
            exact Ne.symm ht
      · simp
      · simp
  | .join a b =>
    rw [project, observe, joinOption_isSome, project_present Δ token a, project_present Δ token b]
    rfl
  | .meet a b =>
    rw [project, observe, meetOption_isSome, project_present Δ token a, project_present Δ token b]
    rfl
  | .var _ | .unit | .credit | .prod _ _ | .sum _ _ | .fn _ _ =>
    rw [project, observe] <;> simp
termination_by ComparisonPartialCapsule.size a
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [ComparisonPartialCapsule.size, ComparisonPartialModes.expressionSize]
  all_goals omega

theorem project_total {Δ : Bounds} {token : Token} {a : CompareTy} {q : ModExpr}
    (h : project Δ token a = some q) : Entails Δ (.defined q) := by
  intro η hη
  have hh := project_spec hη token a
  rw [h] at hh
  exact hh.1 η hη

theorem submode_of_values {Δ : Bounds} {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (h : ∀ η, ModeModels Δ η → Mode.le (value η m) (value η n) = true) : Submode Δ m n := by
  apply Submode.valid
  intro η hη
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hm η hη)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hn η hη)
  refine ⟨x, y, hx, hy, ?_⟩
  simpa only [value, hx, hy, Option.getD_some] using h η hη

theorem project_lower {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {token : Token} (hf : Frozen Δ token) (ha : Atomic (token.1.shape.subst ρ))
    {W : CompareTy} {q m r : ModExpr} (hp : project Δ token W = some q)
    (hm : Entails Δ (.defined m)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal token.1 token.2) r) (.modal W m)) :
    Submode Δ r (.compose q m) := by
  have hq := project_total hp
  apply submode_of_values hr (Entails.defined_compose_iff.mpr ⟨hq, hm⟩)
  intro η hη
  have hs := project_spec hη token W
  rw [hp] at hs
  have hsub := algebra_sound hΔ hρ hη h ha
  rw [denote_modal_total hη hr, denote_frozen η hf, action_principal,
    Mode.identity_compose, denote_modal_total hη hm] at hsub
  have hmem := hsub (show (token, value η r) ∈ principal token (value η r)
    from ⟨rfl, Mode.le_refl _⟩)
  rw [value_compose (hq η hη) (hm η hη)]
  exact (hs.2.action (value η m)).upper _ hmem

theorem project_upper {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {token : Token} (hf : Frozen Δ token) (ha : Atomic (token.1.shape.subst ρ))
    {W : CompareTy} {q m r : ModExpr} (hp : project Δ token W = some q)
    (hm : Entails Δ (.defined m)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal W m) (.modal (.modal token.1 token.2) r)) :
    Submode Δ (.compose q m) r := by
  have hq := project_total hp
  apply submode_of_values (Entails.defined_compose_iff.mpr ⟨hq, hm⟩) hr
  intro η hη
  have hs := project_spec hη token W
  rw [hp] at hs
  have hW : Atomic ((.modal W m : CompareTy).shape.subst ρ) := by
    rw [h.shape_equivalent ρ hρ]
    exact ha
  have hsub := algebra_sound hΔ hρ hη h hW
  rw [denote_modal_total hη hr, denote_frozen η hf, action_principal,
    Mode.identity_compose, denote_modal_total hη hm] at hsub
  rw [value_compose (hq η hη) (hm η hη)]
  exact (hs.2.action (value η m)).least _ (fun p hp => (hsub hp).2)


theorem frozen_observation {Δ : Bounds} {token : Token} (hf : Frozen Δ token) :
    observe Δ (.modal token.1 token.2) = {token} := by
  obtain ⟨a, m⟩ := token
  cases m
  case compose m n => exact False.elim (hf.2 m n rfl)
  all_goals
    have he := not_epsilon_of_partial hf.1
    rw [observe] <;> simp_all [Frozen]

theorem project_from_lower {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {token : Token} (hf : Frozen Δ token) (ha : Atomic (token.1.shape.subst ρ))
    {W : CompareTy} {m r : ModExpr}
    (hm : Entails Δ (.defined m)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal token.1 token.2) r) (.modal W m)) :
    ∃ q, project Δ token W = some q := by
  apply Option.isSome_iff_exists.mp
  apply (project_present Δ token W).mpr
  have hsub := ComparisonPartialCapsule.algebra_sound hΔ hρ h ha
  rw [observe_modal_total hr, observe_modal_total hm, frozen_observation hf] at hsub
  exact hsub (Set.mem_singleton _)

theorem project_lower_reconstruct {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {token : Token} (hf : Frozen Δ token) (ha : Atomic (token.1.shape.subst ρ))
    {W : CompareTy} {q m r : ModExpr} (hp : project Δ token W = some q)
    (hm : Entails Δ (.defined m)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal (.modal token.1 token.2) r) (.modal W m)) :
    AlgebraSubtype Δ (.modal (.modal token.1 token.2) r)
      (.modal (.modal (.modal token.1 token.2) q) m) := by
  have hscalar := project_lower hΔ hρ hf ha hp hm hr h
  exact (AlgebraSubtype.congr (.refl (a := .modal token.1 token.2) h.wellShaped_left) hscalar).trans
    (.shaped (.composeRev (a := .modal token.1 token.2) h.wellShaped_left))

theorem project_upper_reconstruct {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {token : Token} (hf : Frozen Δ token) (ha : Atomic (token.1.shape.subst ρ))
    {W : CompareTy} {q m r : ModExpr} (hp : project Δ token W = some q)
    (hm : Entails Δ (.defined m)) (hr : Entails Δ (.defined r))
    (h : AlgebraSubtype Δ (.modal W m) (.modal (.modal token.1 token.2) r)) :
    AlgebraSubtype Δ (.modal (.modal (.modal token.1 token.2) q) m)
      (.modal (.modal token.1 token.2) r) := by
  have hscalar := project_upper hΔ hρ hf ha hp hm hr h
  exact (AlgebraSubtype.shaped (.compose (a := .modal token.1 token.2) h.wellShaped_right)).trans
    (.congr (.refl h.wellShaped_right) hscalar)

/-- One lower partial demand determines a nonempty capsule slice. Its symbolic
supremum preserves every lower and upper demand for that capsule simultaneously,
even when the original image has arbitrary partial lattice nesting. -/
theorem simultaneous_capsule_reconstruction {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {token : Token} (hf : Frozen Δ token) (ha : Atomic (token.1.shape.subst ρ))
    {W : CompareTy} {m₀ r₀ : ModExpr}
    (hm₀ : Entails Δ (.defined m₀)) (hr₀ : Entails Δ (.defined r₀))
    (h₀ : AlgebraSubtype Δ (.modal (.modal token.1 token.2) r₀) (.modal W m₀)) :
    ∃ q, Entails Δ (.defined q) ∧
      (∀ m r, Entails Δ (.defined m) → Entails Δ (.defined r) →
        AlgebraSubtype Δ (.modal (.modal token.1 token.2) r) (.modal W m) →
        AlgebraSubtype Δ (.modal (.modal token.1 token.2) r)
          (.modal (.modal (.modal token.1 token.2) q) m)) ∧
      (∀ m r, Entails Δ (.defined m) → Entails Δ (.defined r) →
        AlgebraSubtype Δ (.modal W m) (.modal (.modal token.1 token.2) r) →
        AlgebraSubtype Δ (.modal (.modal (.modal token.1 token.2) q) m)
          (.modal (.modal token.1 token.2) r)) := by
  obtain ⟨q, hq⟩ := project_from_lower hΔ hρ hf ha hm₀ hr₀ h₀
  exact ⟨q, project_total hq,
    fun _ _ hm hr h => project_lower_reconstruct hΔ hρ hf ha hq hm hr h,
    fun _ _ hm hr h => project_upper_reconstruct hΔ hρ hf ha hq hm hr h⟩


theorem opposite_tokens_eq {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b W : CompareTy} (sa : Normal Δ a) (sb : Normal Δ b)
    (ha : Atomic (a.shape.subst ρ)) {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hl : AlgebraSubtype Δ a (.modal W m))
    (hu : AlgebraSubtype Δ (.modal W n) b) : sa.token = sb.token := by
  have hW : Atomic ((.modal W n : CompareTy).shape.subst ρ) := by
    change Atomic ((.modal W m : CompareTy).shape.subst ρ)
    rw [←hl.shape_equivalent ρ hρ]
    exact ha
  have hlow := ComparisonPartialCapsule.algebra_sound hΔ hρ hl ha
  have hupp := ComparisonPartialCapsule.algebra_sound hΔ hρ hu hW
  rw [sa.observation, observe_modal_total hm] at hlow
  rw [sb.observation, observe_modal_total hn] at hupp
  exact Set.mem_singleton_iff.mp (hupp (hlow (Set.mem_singleton _)))

/-- A mixed family of atomic partial boundary demands has one common literal
capsule and one shared total suffix. Every request becomes its exact composed
scalar inequality; the original image may contain arbitrary internal joins,
meets, and partial annotations. -/
theorem mixed_normal_scalar_reconstruction {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b W : CompareTy} (sa : Normal Δ a) (sb : Normal Δ b)
    (ha : Atomic (a.shape.subst ρ)) {m n : ModExpr}
    (hm : Entails Δ (.defined m)) (hn : Entails Δ (.defined n))
    (hl : AlgebraSubtype Δ a (.modal W m))
    (hu : AlgebraSubtype Δ (.modal W n) b) :
    ∃ q, Entails Δ (.defined q) ∧
      (∀ c (sc : Normal Δ c) k, Entails Δ (.defined k) →
        AlgebraSubtype Δ c (.modal W k) →
        sc.token = sa.token ∧ Submode Δ sc.suffix (.compose q k)) ∧
      (∀ c (sc : Normal Δ c) k, Entails Δ (.defined k) →
        AlgebraSubtype Δ (.modal W k) c →
        sc.token = sa.token ∧ Submode Δ (.compose q k) sc.suffix) := by
  have hf : Frozen Δ sa.token := observe_frozen a (sa.observation ▸ Set.mem_singleton _)
  have hatom : Atomic (sa.token.1.shape.subst ρ) := by
    change Atomic ((.modal (.modal sa.token.1 sa.token.2) sa.suffix : CompareTy).shape.subst ρ)
    rw [←sa.forward.shape_equivalent ρ hρ]
    exact ha
  have hW : Atomic (W.shape.subst ρ) := by
    change Atomic ((.modal W m : CompareTy).shape.subst ρ)
    rw [←hl.shape_equivalent ρ hρ]
    exact ha
  have hab := opposite_tokens_eq hΔ hρ sa sb ha hm hn hl hu
  have hlow := (AlgebraSubtype.shaped sa.backward).trans hl
  obtain ⟨q, hq⟩ := project_from_lower hΔ hρ hf hatom hm sa.total hlow
  refine ⟨q, project_total hq, ?_, ?_⟩
  · intro c sc k hk hc
    have hcatom : Atomic (c.shape.subst ρ) := by
      rw [hc.shape_equivalent ρ hρ]
      exact hW
    have he := (opposite_tokens_eq hΔ hρ sc sb hcatom hk hn hc hu).trans hab.symm
    refine ⟨he, ?_⟩
    have h := (AlgebraSubtype.shaped sc.backward).trans hc
    rw [he] at h
    exact project_lower hΔ hρ hf hatom hq hk sc.total h
  · intro c sc k hk hc
    have he := opposite_tokens_eq hΔ hρ sa sc ha hm hk hl hc
    refine ⟨he.symm, ?_⟩
    have h := hc.trans (.shaped sc.forward)
    rw [←he] at h
    exact project_upper hΔ hρ hf hatom hq hk sc.total h

end
end ModalityInference.ComparisonPartialCapsuleScalar
