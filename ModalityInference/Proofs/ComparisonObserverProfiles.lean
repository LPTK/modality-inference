import ModalityInference.Proofs.ComparisonObserverActions
import ModalityInference.Proofs.ComparisonModeRestriction

/-! Finite signed controls determine a guarded Boolean modal transfer on a
fixed finite name set. The normal form keeps partiality in the original guard;
its signed-control representation is total. -/
namespace ModalityInference.ComparisonObserverProfiles

open ComparisonAlgebra ComparisonControls ComparisonObserverActions

def signedAtom (c : Channel) (i : Nat) (positive : Bool) : ModExpr :=
  match atomControl c i positive with
  | some q => q.expression
  | none => .const (channelMode c false)

def band (c : Channel) : BoolExpr → Bool → ModExpr
  | .const b, p => .const (channelMode c (b == p))
  | .atom i, p => signedAtom c i p
  | .and a b, true => .meet (band c a true) (band c b true)
  | .and a b, false => .join (band c a false) (band c b false)
  | .or a b, true => .join (band c a true) (band c b true)
  | .or a b, false => .meet (band c a false) (band c b false)
  | .imp a b, true => .join (band c a false) (band c b true)
  | .imp a b, false => .meet (band c a true) (band c b false)

/-- The only leaves are constants and the ten signed controls per retained name. -/
inductive Generated (names : Finset ModVar) : ModExpr → Prop where
  | const (m : Mode) : Generated names (.const m)
  | control (q : Control) (hq : q.name ∈ names) : Generated names q.expression
  | compose {m n} : Generated names m → Generated names n → Generated names (.compose m n)
  | join {m n} : Generated names m → Generated names n → Generated names (.join m n)
  | meet {m n} : Generated names m → Generated names n → Generated names (.meet m n)

theorem signedAtom_eval {c i p} (hi : c.Accepts i) (η : ModVar → Mode) :
    (signedAtom c i p).eval (some ∘ η) = some (channelMode c (encodeModes η i == p)) := by
  obtain ⟨q, hq⟩ := atomControl_exists c i p hi
  obtain ⟨hc, ha, hp, _⟩ := atomControl_spec hq
  simp only [signedAtom, hq]
  simpa only [BandScalar.control, hc, ha, hp] using (BandScalar.control (Δ := []) q).eval η (by simp [ModeModels])

theorem signedAtom_generated {names c i p} (hi : c.Accepts i)
    (hn : SymbolicModes.atomVariable i ∈ names) : Generated names (signedAtom c i p) := by
  obtain ⟨q, hq⟩ := atomControl_exists c i p hi
  simp only [signedAtom, hq]
  exact .control q (by simpa only [(atomControl_spec hq).2.2.2] using hn)

theorem band_eval {c e} (h : ∀ i ∈ e.atoms, c.Accepts i) (p : Bool) (η : ModVar → Mode) :
    (band c e p).eval (some ∘ η) = some (channelMode c (e.eval (encodeModes η) == p)) := by
  induction e generalizing p with
  | const b => rfl
  | atom i => exact signedAtom_eval (h i (by simp [BoolExpr.atoms])) η
  | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    have ha : ∀ i ∈ a.atoms, c.Accepts i := fun i hi => h i (by simp [BoolExpr.atoms, hi])
    have hb : ∀ i ∈ b.atoms, c.Accepts i := fun i hi => h i (by simp [BoolExpr.atoms, hi])
    cases p <;> simp only [band, ModExpr.eval, iha ha, ihb hb, bind, Option.bind,
      pure, channelMode_join, channelMode_meet, BoolExpr.eval]
    all_goals cases a.eval (encodeModes η) <;> cases b.eval (encodeModes η) <;> rfl

theorem band_generated {names c e}
    (h : ∀ i ∈ e.atoms, c.Accepts i ∧ SymbolicModes.atomVariable i ∈ names) (p : Bool) :
    Generated names (band c e p) := by
  induction e generalizing p with
  | const b => exact .const _
  | atom i =>
      exact signedAtom_generated (h i (by simp [BoolExpr.atoms])).1
        (h i (by simp [BoolExpr.atoms])).2
  | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    have ha : ∀ i ∈ a.atoms, c.Accepts i ∧ SymbolicModes.atomVariable i ∈ names :=
      fun i hi => h i (by simp [BoolExpr.atoms, hi])
    have hb : ∀ i ∈ b.atoms, c.Accepts i ∧ SymbolicModes.atomVariable i ∈ names :=
      fun i hi => h i (by simp [BoolExpr.atoms, hi])
    cases p
    all_goals first | exact .join (iha ha _) (ihb hb _) | exact .meet (iha ha _) (ihb hb _)


def normal (m : ModExpr) : ModExpr :=
  .compose (band .locality m.project.locality true)
    (.compose (band .affinity m.project.affinity true) (band .lower m.project.uniqueness false))

theorem normal_generated {names : Finset ModVar} {m : ModExpr}
    (hs : m.vars ⊆ names) : Generated names (normal m) := by
  have h := project_support m
  refine .compose (band_generated ?_ _) (.compose (band_generated ?_ _) (band_generated ?_ _))
  · intro i hi
    exact ⟨(h.1 i hi).1, hs ((ModExpr.mem_freeVariables _ _).mp (h.1 i hi).2)⟩
  · intro i hi
    exact ⟨(h.2.1 i hi).1, hs ((ModExpr.mem_freeVariables _ _).mp (h.2.1 i hi).2)⟩
  · intro i hi
    exact ⟨(h.2.2 i hi).1, hs ((ModExpr.mem_freeVariables _ _).mp (h.2.2 i hi).2)⟩

theorem normal_eval {Δ : Bounds} {m : ModExpr} (hm : Entails Δ (.defined m))
    {η : ModVar → Mode} (hη : ModeModels Δ η) :
    (normal m).eval (some ∘ η) = m.eval (some ∘ η) := by
  have h := project_support m
  have hd : m.project.defined.eval (encodeModes η) = true := by
    apply (m.project_defined _).mpr
    simpa only [projectedModes_encodeModes] using hm η hη
  have he := m.project_correct (encodeModes η)
  rw [projectedModes_encodeModes] at he
  rw [← he]
  simp [normal, ModExpr.eval, band_eval (c := .locality) (fun i hi => (h.1 i hi).1),
    band_eval (c := .affinity) (fun i hi => (h.2.1 i hi).1), band_eval (c := .lower) (fun i hi => (h.2.2 i hi).1),
    channelMode, Mode.compose, Projection.eval, hd]

theorem Generated.defined {Δ names m} (h : Generated names m) : Entails Δ (.defined m) := by
  induction h with
  | const m => intro η _; rfl
  | control q _ => intro η _; exact control_total q η
  | compose _ _ ih₁ ih₂ => exact Entails.defined_compose_iff.mpr ⟨ih₁, ih₂⟩
  | join _ _ ih₁ ih₂ => exact ComparisonDefinedCovers.modeOp_defined true ih₁ ih₂
  | meet _ _ ih₁ ih₂ => exact ComparisonDefinedCovers.modeOp_defined false ih₁ ih₂

theorem Transition.generated_agree {Δ names} (t u : Transition Δ)
    (hc : ∀ m x, t.apply (.const m) x = u.apply (.const m) x)
    (hv : ∀ q : Control, q.name ∈ names → ∀ x, t.apply q.expression x = u.apply q.expression x)
    {m} (h : Generated names m) : ∀ x, t.apply m x = u.apply m x := by
  induction h with
  | const m => exact hc m
  | control q hq => exact hv q hq
  | compose h₁ h₂ ih₁ ih₂ =>
    intro x
    rw [t.compose _ _ h₁.defined h₂.defined, u.compose _ _ h₁.defined h₂.defined,
      ih₁, ih₂]
  | join h₁ h₂ ih₁ ih₂ =>
    intro x
    rw [t.join _ _ h₁.defined h₂.defined, u.join _ _ h₁.defined h₂.defined, ih₁, ih₂]
  | meet h₁ h₂ ih₁ ih₂ =>
    intro x
    rw [t.meet _ _ h₁.defined h₂.defined, u.meet _ _ h₁.defined h₂.defined, ih₁, ih₂]

theorem Transition.normal_apply {Δ m} (t : Transition Δ) (hm : Entails Δ (.defined m)) (x : Bool) :
    t.apply (normal m) x = t.apply m x := by
  have hleft : Submode Δ (normal m) m := .valid fun η hη => by
    simpa only [ModExpr.Below, normal_eval hm hη] using (Submode.refl hm).denote hη
  have hright : Submode Δ m (normal m) := .valid fun η hη => by
    simpa only [ModExpr.Below, normal_eval hm hη] using (Submode.refl hm).denote hη
  exact le_antisymm (t.submode _ _ hleft x) (t.submode _ _ hright x)

/-- A finite generator table determines every guarded action over its names. -/
theorem Transition.supported_agree {Δ names} (t u : Transition Δ)
    (hc : ∀ m x, t.apply (.const m) x = u.apply (.const m) x)
    (hv : ∀ q : Control, q.name ∈ names → ∀ x, t.apply q.expression x = u.apply q.expression x)
    {m} (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names) (x : Bool) :
    t.apply m x = u.apply m x := by
  rw [← Transition.normal_apply t hm x, ← Transition.normal_apply u hm x]
  exact Transition.generated_agree t u hc hv (normal_generated hs) x


noncomputable def generators (names : Finset ModVar) : List ModExpr :=
  Mode.all.map ModExpr.const ++ (names.toList.flatMap controls).map Control.expression

theorem const_mem_generators (names : Finset ModVar) (m : Mode) :
    ModExpr.const m ∈ generators names := by
  have hm : m ∈ Mode.all := by
    obtain ⟨l, o, u⟩ := m
    cases l <;> cases o <;> cases u <;> decide
  exact List.mem_append_left _ (List.mem_map.mpr ⟨m, hm, rfl⟩)

theorem control_mem_generators {names : Finset ModVar} (q : Control) (hq : q.name ∈ names) :
    q.expression ∈ generators names := by
  have hself : q ∈ controls q.name := by
    cases q with
    | locality v p => cases p <;> simp [controls, Control.name]
    | affinity v u p | uniqueness v u p => cases u <;> cases p <;> simp [controls, Control.name]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨q,
    List.mem_flatMap.mpr ⟨q.name, Finset.mem_toList.mpr hq, hself⟩, rfl⟩)

theorem generators_length (names : Finset ModVar) :
    (generators names).length = 8 + 10 * names.card := by
  have hlen (vs : List ModVar) : (vs.flatMap controls).length = 10 * vs.length := by
    induction vs with
    | nil => rfl
    | cons v vs ih =>
      simp [controls, ih, Nat.mul_add, Nat.add_comm]
      omega
  simp [generators, hlen, Mode.all]
  omega

/-- Both Boolean fibers are recorded; the table has eight constant rows and
ten signed-control rows per retained name. -/
noncomputable def profile {Δ} (t : Transition Δ) (names : Finset ModVar) : List (Bool × Bool) :=
  (generators names).map fun m => (t.apply m false, t.apply m true)

theorem profile_generator {Δ names} {t u : Transition Δ} (h : profile t names = profile u names)
    {m} (hm : m ∈ generators names) (x : Bool) : t.apply m x = u.apply m x := by
  have he := List.map_eq_map_iff.mp h m hm
  cases x
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem profile_supported {Δ names} {t u : Transition Δ} (h : profile t names = profile u names)
    {m} (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names) (x : Bool) :
    t.apply m x = u.apply m x :=
  Transition.supported_agree t u
    (fun m x => profile_generator h (const_mem_generators names m) x)
    (fun q hq x => profile_generator h (control_mem_generators q hq) x) hm hs x

/-- Restricting unused names is an action on the full modality language, not
merely a table for the finitely many labels appearing at the boundary. -/
def restricted {Δ names} (t : Transition Δ) (hs : Δ.modVars ⊆ names) : Transition Δ where
  apply m x := t.apply (m.subst (ComparisonModeRestriction.restrict names)) x
  monotone _ hm := t.monotone _ ((ComparisonModeRestriction.restrict_fixed Δ names hs).defined hm)
  epsilon x := t.epsilon x
  compose _ _ hm hn x := t.compose _ _
    ((ComparisonModeRestriction.restrict_fixed Δ names hs).defined hm)
    ((ComparisonModeRestriction.restrict_fixed Δ names hs).defined hn) x
  join _ _ hm hn x := t.join _ _
    ((ComparisonModeRestriction.restrict_fixed Δ names hs).defined hm)
    ((ComparisonModeRestriction.restrict_fixed Δ names hs).defined hn) x
  meet _ _ hm hn x := t.meet _ _
    ((ComparisonModeRestriction.restrict_fixed Δ names hs).defined hm)
    ((ComparisonModeRestriction.restrict_fixed Δ names hs).defined hn) x
  submode _ _ h x := t.submode _ _ ((ComparisonModeRestriction.restrict_fixed Δ names hs).submode h) x

/-- A concrete finite profile determines the entire restricted guarded action. -/
theorem profile_restricted {Δ names} {t u : Transition Δ} (hs : Δ.modVars ⊆ names)
    (h : profile t names = profile u names) {m} (hm : Entails Δ (.defined m)) (x : Bool) :
    (restricted t hs).apply m x = (restricted u hs).apply m x :=
  profile_supported h ((ComparisonModeRestriction.restrict_fixed Δ names hs).defined hm)
    (ComparisonModeRestriction.restrict_support names m) x

end ModalityInference.ComparisonObserverProfiles
