import ModalityInference.Proofs.GenerationContextTyping
import ModalityInference.Proofs.SchemeInstantiation

/-! Fresh scheme binders relative to ambient bounds. Identity substitutions can
carry a finite support while preserving every original instance. -/
namespace ModalityInference

theorem Substitution.identity_bounds_entails {σ : Substitution}
    (ht : σ.type = TypeExpr.var) (hm : σ.mode = ModExpr.var) (cs Δ : Bounds) :
    EntailsAll Δ (σ.bounds cs) ↔ EntailsAll Δ cs := by
  have ht0 : σ.type = ({} : Substitution).type := by funext v; rw [ht]; cases v <;> rfl
  have hm0 : σ.mode = ({} : Substitution).mode := by funext v; rw [hm]; cases v <;> rfl
  simp only [EntailsAll, Substitution.bounds, List.forall_mem_map]
  exact forall_congr' fun c => forall_congr' fun _ => by
    simpa only [Substitution.empty_constraint] using Substitution.constraint_entails_congr ht0 hm0 c Δ

def Substitution.mapImages (τ σ : Substitution) : Substitution :=
  {types := σ.types.map fun (n, a) => (n, τ.ty a)
   modes := σ.modes.map fun (n, m) => (n, m.subst τ.mode)}

theorem Substitution.mapImages_type (τ σ : Substitution) (v : TypeVar)
    (hv : τ.type v = .var v) : (τ.mapImages σ).type v = τ.ty (σ.type v) := by
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [mapImages, type, lookup_map_values]
    cases σ.types.lookup n <;> simp [Substitution.ty, TypeExpr.subst, hv]

theorem Substitution.mapImages_mode (τ σ : Substitution) (v : ModVar)
    (hv : τ.mode v = .var v) : (τ.mapImages σ).mode v = (σ.mode v).subst τ.mode := by
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [mapImages, mode, lookup_map_values]
    cases σ.modes.lookup n <;> simp [ModExpr.subst, hv]

theorem Instantiates.mapImages {s : Scheme} {σ : Substitution} (h : Instantiates s σ)
    (τ : Substitution) : Instantiates s (τ.mapImages σ) := by
  simpa [Instantiates, Substitution.mapImages, List.map_map, Function.comp_def] using h

theorem Instantiates.subst_type_lt {s : Scheme} {σ θ : Substitution}
    (h : Instantiates (s.subst σ) θ) {v : TypeVar}
    (hv : v.index < (s.fresheningIndices σ).1) : θ.type v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply θ.type_fresh
    exact fun hn =>
      let ⟨i, _, he⟩ := List.mem_map.mp (h.1.mem_iff.mp hn)
      (Nat.not_lt.mpr (he ▸ Nat.le_add_right (s.fresheningIndices σ).1 i)) hv

theorem Instantiates.subst_mode_lt {s : Scheme} {σ θ : Substitution}
    (h : Instantiates (s.subst σ) θ) {v : ModVar}
    (hv : v.index < (s.fresheningIndices σ).2) : θ.mode v = .var v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    apply θ.mode_fresh
    exact fun hn =>
      let ⟨i, _, he⟩ := List.mem_map.mp (h.2.mem_iff.mp hn)
      (Nat.not_lt.mpr (he ▸ Nat.le_add_right (s.fresheningIndices σ).2 i)) hv

theorem Instantiates.unsubstitute_identity {s : Scheme} {σ θ : Substitution}
    (h : Instantiates (s.subst σ) θ) (ht : σ.type = TypeExpr.var) (hm : σ.mode = ModExpr.var) :
    ∃ θ', Instantiates s θ' ∧ θ'.ty s.body = θ.ty (s.subst σ).body ∧
      ∀ Δ, EntailsAll Δ (θ'.bounds s.bounds) ↔ EntailsAll Δ (θ.bounds (s.subst σ).bounds) := by
  have hid (a : Ty) : σ.ty a = a := by
    simpa only [Substitution.ty, ht, hm] using a.subst_id
  have htype (v : TypeVar) (hv : v.index < (s.fresheningIndices σ).1) :
      (θ.mapImages (s.binderRenaming σ)).type v = (θ.compose (s.substitutionAction σ)).type v := by
    simpa only [Scheme.substitutionAction, Substitution.type_compose, hid] using
      θ.mapImages_type (s.binderRenaming σ) v (h.subst_type_lt hv)
  have hmode (v : ModVar) (hv : v.index < (s.fresheningIndices σ).2) :
      (θ.mapImages (s.binderRenaming σ)).mode v = (θ.compose (s.substitutionAction σ)).mode v := by
    simpa only [Scheme.substitutionAction, Substitution.mode_compose, hm, ModExpr.subst_id] using
      θ.mapImages_mode (s.binderRenaming σ) v (h.subst_mode_lt hv)
  refine ⟨θ.mapImages (s.binderRenaming σ),
    (s.freshSubstitution_instantiates _ _ _).mapImages θ, ?_, ?_⟩
  · rw [Scheme.subst_body_action, Substitution.ty_compose]
    exact s.body.subst_congr
      (fun v hv => htype v (((s.body.bounded_iff _ _).mp (s.freshening_bounded σ).1.1).1 v hv))
      (fun v hv => hmode v (((s.body.bounded_iff _ _).mp (s.freshening_bounded σ).1.1).2 v hv))
  · simp only [Scheme.subst_bounds_action, EntailsAll, Substitution.bounds,
      List.forall_mem_map, Substitution.constraint_compose]
    exact fun Δ => forall_congr' fun c => forall_congr' fun hc =>
      Substitution.constraint_entails_congr_on c Δ
        (fun v hv => htype v (((c.bounded_iff _ _).mp ((s.freshening_bounded σ).1.2 c hc)).1 v hv))
        (fun v hv => hmode v (((c.bounded_iff _ _).mp ((s.freshening_bounded σ).1.2 c hc)).2 v hv))

theorem Scheme.subsumes_subst_identity (s : Scheme) (Δ : Bounds) {σ : Substitution}
    (ht : σ.type = TypeExpr.var) (hm : σ.mode = ModExpr.var) :
    Subsumes Δ s (s.subst σ).withAssumptions := by
  let target := (s.subst σ).withAssumptions
  let θ := (s.subst σ).freshSubstitution (s.subsumptionIndices Δ target).1
    (s.subsumptionIndices Δ target).2 true
  obtain ⟨θ', hi, ha, hb⟩ := ((s.subst σ).freshSubstitution_instantiates
    (s.subsumptionIndices Δ target).1 (s.subsumptionIndices Δ target).2 true).unsubstitute_identity ht hm
  refine ⟨θ', hi, (hb _).mpr (θ.assumptions_renaming_entails (s.subst σ).bounds Δ
    ((s.subst σ).freshSubstitution_type_variable _ _ _)), ?_⟩
  simpa only [ha] using (Subtype.refl (Δ := Δ ++ θ.bounds target.bounds) (a := θ.ty target.body))

theorem Scheme.subst_identity_instances (s : Scheme) {σ : Substitution}
    (ht : σ.type = TypeExpr.var) (hm : σ.mode = ModExpr.var) (Δ : Bounds) (a : Ty) :
    (∃ θ, Instantiates (s.subst σ) θ ∧ EntailsAll Δ (θ.bounds (s.subst σ).bounds) ∧
      θ.ty (s.subst σ).body = a) ↔
    (∃ θ, Instantiates s θ ∧ EntailsAll Δ (θ.bounds s.bounds) ∧ θ.ty s.body = a) := by
  constructor
  · rintro ⟨θ, hi, hb, ha⟩
    obtain ⟨θ', hi', ha', hb'⟩ := hi.unsubstitute_identity ht hm
    exact ⟨θ', hi', (hb' Δ).mpr hb, ha'.trans ha⟩
  · rintro ⟨θ, hi, hb, ha⟩
    obtain ⟨θ', hi', ha', hb'⟩ := hi.substitute σ
    exact ⟨θ', hi', (hb' Δ).mpr ((Substitution.identity_bounds_entails ht hm _ _).mpr hb),
      by simpa only [Substitution.ty, ht, hm, TypeExpr.subst_id] using ha'.trans (congrArg σ.ty ha)⟩

def Substitution.identityAt (nt nm : Nat) : Substitution :=
  {types := [(nt, .var (.flex nt))], modes := [(nm, .var (.flex nm))]}

theorem Substitution.identityAt_type (nt nm : Nat) : (identityAt nt nm).type = TypeExpr.var := by
  funext v
  cases v with
  | rigid n => rfl
  | flex n =>
    cases he : n == nt <;> simp [Substitution.identityAt, Substitution.type, List.lookup_cons, he]
    exact (beq_iff_eq.mp he).symm

theorem Substitution.identityAt_mode (nt nm : Nat) : (identityAt nt nm).mode = ModExpr.var := by
  funext v
  cases v with
  | rigid n => rfl
  | flex n =>
    cases he : n == nm <;> simp [Substitution.identityAt, Substitution.mode, List.lookup_cons, he]
    exact (beq_iff_eq.mp he).symm

theorem Scheme.freshening_identityAt (s : Scheme) (nt nm : Nat) :
    nt < (s.fresheningIndices (.identityAt nt nm)).1 ∧
      nm < (s.fresheningIndices (.identityAt nt nm)).2 := by
  exact ⟨((s.freshening_bounded (.identityAt nt nm)).2.types nt (.var (.flex nt)) (by simp [Substitution.identityAt])).1,
    ((s.freshening_bounded (.identityAt nt nm)).2.modes nm (.var (.flex nm)) (by simp [Substitution.identityAt])).1⟩

theorem Scheme.subst_freshForBounds (s : Scheme) (σ : Substitution) (Δ : Bounds)
    (ht : Δ.freshTypeIndex ≤ (s.fresheningIndices σ).1)
    (hm : Δ.freshModeIndex ≤ (s.fresheningIndices σ).2) : (s.subst σ).FreshForBounds Δ := by
  constructor
  · intro n hn hv
    obtain ⟨i, _, he⟩ := List.mem_map.mp hn
    exact (Nat.not_lt.mpr (he ▸ Nat.le_add_right (s.fresheningIndices σ).1 i))
      ((Bounds.lt_freshTypeIndex ((Bounds.mem_typeVariables Δ _).mpr hv)).trans_le ht)
  · intro n hn hv
    obtain ⟨i, _, he⟩ := List.mem_map.mp hn
    exact (Nat.not_lt.mpr (he ▸ Nat.le_add_right (s.fresheningIndices σ).2 i))
      ((Bounds.lt_freshModeIndex ((Bounds.mem_modeVariables Δ _).mpr hv)).trans_le hm)

def Scheme.freshenedFor (s : Scheme) (avoid : Bounds) : Scheme :=
  (s.subst (.identityAt avoid.freshTypeIndex avoid.freshModeIndex)).withAssumptions

theorem Scheme.freshenedFor_fresh (s : Scheme) (avoid : Bounds) :
    (s.freshenedFor avoid).FreshForBounds avoid :=
  s.subst_freshForBounds _ _ (s.freshening_identityAt _ _).1.le (s.freshening_identityAt _ _).2.le

theorem Scheme.subsumes_freshenedFor (s : Scheme) (Δ avoid : Bounds) :
    Subsumes Δ s (s.freshenedFor avoid) :=
  s.subsumes_subst_identity Δ (Substitution.identityAt_type _ _) (Substitution.identityAt_mode _ _)

theorem Scheme.freshenedFor_instances (s : Scheme) (avoid Δ : Bounds) (a : Ty) :
    (∃ θ, Instantiates (s.freshenedFor avoid) θ ∧
      EntailsAll Δ (θ.bounds (s.freshenedFor avoid).bounds) ∧ θ.ty (s.freshenedFor avoid).body = a) ↔
    (∃ θ, Instantiates s θ ∧ EntailsAll Δ (θ.bounds s.bounds) ∧ θ.ty s.body = a) := by
  exact (exists_congr fun θ => (s.subst _).withAssumptions_instance θ Δ a).trans
    (s.subst_identity_instances (Substitution.identityAt_type _ _) (Substitution.identityAt_mode _ _) Δ a)

theorem Scheme.FreshForBounds.of_subset {s : Scheme} {Δ Ξ : Bounds}
    (h : s.FreshForBounds Ξ) (hΔ : Δ ⊆ Ξ) : s.FreshForBounds Δ := by
  constructor
  · intro n hn hv
    obtain ⟨c, hc, hv⟩ := (Δ.mem_typeVars_iff _).mp hv
    exact h.1 n hn ((Ξ.mem_typeVars_iff _).mpr ⟨c, hΔ hc, hv⟩)
  · intro n hn hv
    obtain ⟨c, hc, hv⟩ := (Δ.mem_modVars_iff _).mp hv
    exact h.2 n hn ((Ξ.mem_modVars_iff _).mpr ⟨c, hΔ hc, hv⟩)

theorem Scheme.FreshForBounds.defined {s : Scheme} {Δ : Bounds} {m : ModExpr}
    (h : s.FreshForBounds Δ) (hm : Constraint.defined m ∈ Δ) : s.FreshForMode m :=
  fun n hn hv => h.2 n hn ((Δ.mem_modVars_iff _).mpr ⟨.defined m, hm, hv⟩)

def Context.freshenedFor (Γ : Context) (avoid : Bounds) : Context :=
  Γ.map (Option.map (fun s => s.freshenedFor avoid))

theorem Context.freshenedFor_le (Γ : Context) (Δ avoid : Bounds) :
    ContextLe Δ Γ (Γ.freshenedFor avoid) := by
  induction Γ with
  | nil => exact .nil
  | cons entry Γ ih =>
    cases entry with
    | none => exact .drop ih
    | some s => exact .keep ih (s.subsumes_freshenedFor Δ avoid)

theorem Context.freshenedFor_fresh (Γ : Context) (avoid : Bounds) {s : Scheme}
    (hs : some s ∈ Γ.freshenedFor avoid) : s.FreshForBounds avoid := by
  obtain ⟨entry, _, he⟩ := List.mem_map.mp hs
  cases entry with
  | none => cases he
  | some source =>
    cases he
    exact source.freshenedFor_fresh avoid

theorem Context.freshenedFor_lock (Γ : Context) (Δ : Bounds) (m : ModExpr) :
    let fresh := Γ.freshenedFor (Δ ++ [.defined m])
    ∃ source, ContextLe Δ fresh source ∧
      Lock Δ m source (fresh.map (Option.map (fun s => (s.lock m).withAssumptions))) := by
  dsimp only
  generalize he : Γ.freshenedFor (Δ ++ [.defined m]) = fresh
  have hf (s : Scheme) (hs : some s ∈ fresh) : s.FreshForBounds (Δ ++ [.defined m]) :=
    Γ.freshenedFor_fresh _ (he.symm ▸ hs)
  apply Context.lock_withAssumptions fresh Δ m
  · exact fun s hs => (hf s hs).of_subset (fun _ hc => List.mem_append_left _ hc)
  · exact fun s hs => (hf s hs).defined (by simp)

end ModalityInference
