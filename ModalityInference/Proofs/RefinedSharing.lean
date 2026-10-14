import ModalityInference.Proofs.NestedLockRefinement
import ModalityInference.Proofs.TypingAdmissibility

/-! Recover base instances from modal refinements and compare refined shared captures. -/
namespace ModalityInference

/-- Remove a quantified modality from a finite instance without changing its other images. -/
def Substitution.dropMode (σ : Substitution) (p : Nat) : Substitution :=
  {σ with modes := σ.modes.filter (fun entry => entry.1 != p)}

theorem Substitution.dropMode_type (σ : Substitution) (p : Nat) :
    (σ.dropMode p).type = σ.type := rfl

theorem Substitution.dropMode_mode (σ : Substitution) (p : Nat) {v : ModVar}
    (hv : v ≠ .flex p) : (σ.dropMode p).mode v = σ.mode v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    simp only [dropMode, mode]
    induction σ.modes with
    | nil => rfl
    | cons entry entries ih =>
      cases entry with
      | mk k m =>
        by_cases he : k = p <;> simp_all [List.lookup_cons]
        all_goals split <;> simp_all [beq_iff_eq]

theorem Instantiates.drop_refineMode {s : Scheme} {σ : Substitution} {p : Nat}
    (hi : Instantiates (s.refineMode p) σ) (hp : p ∉ s.modParams) :
    Instantiates s (σ.dropMode p) := by
  refine ⟨hi.1, ?_⟩
  have he : s.modParams.filter (fun n => n != p) = s.modParams :=
    List.filter_eq_self.mpr (fun n hn => bne_iff_ne.mpr (fun h => hp (h ▸ hn)))
  simpa [Substitution.dropMode, Scheme.refineMode, List.filter_map, he] using
    hi.2.filter (fun n => n != p)

theorem Substitution.dropMode_ty (σ : Substitution) (p : Nat) (a : Ty)
    (hp : .flex p ∉ a.modVars) : (σ.dropMode p).ty a = σ.ty a := by
  exact a.subst_congr (fun _ _ => rfl)
    (fun v hv => σ.dropMode_mode p (fun he => hp (he ▸ hv)))

theorem Substitution.dropMode_modExpr (σ : Substitution) (p : Nat) (m : ModExpr)
    (hp : .flex p ∉ m.vars) : m.subst (σ.dropMode p).mode = m.subst σ.mode := by
  exact m.subst_congr (fun v hv => σ.dropMode_mode p (fun he => hp (he ▸ hv)))

theorem Substitution.dropMode_bounds (σ : Substitution) (p : Nat) (cs Δ : Bounds)
    (hp : .flex p ∉ cs.modVars) :
    EntailsAll Δ ((σ.dropMode p).bounds cs) ↔ EntailsAll Δ (σ.bounds cs) := by
  simp only [EntailsAll, Substitution.bounds, List.forall_mem_map]
  exact forall_congr' fun c => forall_congr' fun hc =>
    Substitution.constraint_entails_congr_on c Δ (fun _ _ => rfl)
      (fun v hv => σ.dropMode_mode p (fun he => hp
        ((cs.mem_modVars_iff _).mpr ⟨c, hc, he ▸ hv⟩)))

theorem Scheme.refineMode_instance_body (s : Scheme) (σ : Substitution) (p : Nat) :
    σ.ty (s.refineMode p).body = .modal (σ.ty s.body) (σ.mode (.flex p)) := rfl

theorem Scheme.refineMode_instance_bounds (s : Scheme) (σ : Substitution) (p : Nat) (Δ : Bounds) :
    EntailsAll Δ (σ.bounds (s.refineMode p).bounds) ↔
      EntailsAll Δ (σ.bounds s.bounds) ∧
        Entails Δ (.sub (σ.ty s.body) (.modal (σ.ty s.body) (σ.mode (.flex p)))) := by
  simp [Scheme.refineMode, EntailsAll, Substitution.bounds, Substitution.constraint, Constraint.subst,
    Substitution.ty, TypeExpr.subst, ModExpr.subst, or_imp, forall_and]

theorem Scheme.refined_shared_lockAll_instance {s : Scheme} {σ : Substitution} {p q : Nat}
    {ms : List ModExpr} {Δ : Bounds} (hi : Instantiates ((s.share.refineMode q).lockAll ms) σ)
    (hp : s.freshModeIndex ≤ p) (hq : s.freshModeIndex ≤ q)
    (hmp : ∀ m ∈ ms, .flex p ∉ m.vars) (hmq : ∀ m ∈ ms, .flex q ∉ m.vars)
    (hb : EntailsAll Δ (σ.bounds ((s.share.refineMode q).lockAll ms).bounds)) :
    ∃ τ, Instantiates ((s.refineMode p).lockAll ms) τ ∧
      EntailsAll Δ (τ.bounds ((s.refineMode p).lockAll ms).bounds) ∧
      Subtype Δ (τ.ty ((s.refineMode p).lockAll ms).body)
        (σ.ty ((s.share.refineMode q).lockAll ms).body) ∧
      Subtype Δ (σ.ty ((s.share.refineMode q).lockAll ms).body)
        (τ.ty ((s.refineMode p).lockAll ms).body) := by
  have hi₀ : Instantiates s (σ.dropMode q) :=
    (((s.share.refineMode q).lockAll_instantiates ms σ).mp hi).drop_refineMode
      (Scheme.refineMode_fresh hq).1
  have hr := (s.share.refineMode_instance_bounds σ q Δ).mp (Scheme.lockAll_base_bounds hb)
  have hs := (s.share_instance_bounds σ Δ).mp hr.1
  let k := ModExpr.compose (.const Mode.aliased) (σ.mode (.flex q))
  have hk : Entails Δ (.defined k) := Entails.defined_compose_iff.mpr
    ⟨fun _ _ => rfl, (TypeExpr.definedUnder_modal.mp hr.2.2.2).2⟩
  have he₀ := σ.dropMode_ty q s.body (Scheme.refineMode_fresh hq).2.1
  have he : ((σ.dropMode q).extendMode p k).ty (s.refineMode p).body = .modal (σ.ty s.body) k :=
    (hi₀.refineMode_body hp k).trans (congrArg (fun a => TypeExpr.modal a k) he₀)
  have hd : (TypeExpr.modal (σ.ty s.body) k).DefinedUnder Δ :=
    TypeExpr.definedUnder_modal.mpr ⟨hs.2.2.1, hk⟩
  have hw : Subtype Δ (σ.ty s.body) (.modal (σ.ty s.body) k) :=
    (Subtype.identityRev.trans (.congr .refl (.valid fun _ _ =>
      ⟨_, _, rfl, rfl, by decide⟩))).trans (hr.2.1.trans .compose)
  have hbounds := (hi₀.refineMode_bounds hp k Δ).mpr
    ⟨(σ.dropMode_bounds q s.bounds Δ (Scheme.refineMode_fresh hq).2.2).mpr hs.1,
      he₀.symm ▸ ⟨hw, hs.2.2.1, hd⟩⟩
  have hl := Scheme.lockAll_transport (t := s.share.refineMode q) (τ := σ)
    hbounds (he.symm ▸ hd) (he.symm ▸ Subtype.composeRev) (he.symm ▸ Subtype.compose)
    ms (fun m hm => ((σ.dropMode q).extendMode_modExpr p k m (hmp m hm)).trans
      (σ.dropMode_modExpr q m (hmq m hm))) hb
  exact ⟨(σ.dropMode q).extendMode p k,
    ((s.refineMode p).lockAll_instantiates ms _).mpr (hi₀.refineMode p k), hl.1, hl.2.2⟩

theorem Scheme.refined_shared_lockAll_many {s : Scheme} {σ : Substitution} {q : Nat}
    {ms : List ModExpr} {Δ : Bounds}
    (hb : EntailsAll Δ (σ.bounds ((s.share.refineMode q).lockAll ms).bounds)) :
    Subtype Δ (σ.ty ((s.share.refineMode q).lockAll ms).body)
      (.modal (σ.ty ((s.share.refineMode q).lockAll ms).body) (.const Mode.many)) := by
  have hr := (s.share.refineMode_instance_bounds σ q Δ).mp (Scheme.lockAll_base_bounds hb)
  exact Scheme.lockAll_instance_many
    ((((s.share_instance_bounds σ Δ).mp hr.1).2.1.modal_many
      (m := .const Mode.aliased) (fun _ _ => rfl)).modal_many
        (TypeExpr.definedUnder_modal.mp hr.2.2.2).2) hb

theorem Scheme.refineMode_lockAll_subsumes_refined_shared {s : Scheme} {p q : Nat}
    {ms : List ModExpr} (hp : s.freshModeIndex ≤ p) (hq : s.freshModeIndex ≤ q)
    (hmp : ∀ m ∈ ms, .flex p ∉ m.vars) (hmq : ∀ m ∈ ms, .flex q ∉ m.vars) (Δ : Bounds) :
    Subsumes Δ ((s.refineMode p).lockAll ms).withAssumptions
      (((s.share.refineMode q).lockAll ms).withAssumptions.modal (.const Mode.many)) := by
  refine Subsumes.of_instances (fun Ξ σ hi hb => ?_)
  obtain ⟨τ, hτ, hbounds, hsub, _⟩ :=
    s.refined_shared_lockAll_instance hi hp hq hmp hmq hb.of_subst_assumptions
  exact ⟨τ, hτ, hbounds.subst_assumptions,
    hsub.trans (Scheme.refined_shared_lockAll_many hb.of_subst_assumptions)⟩

theorem Subtype.modal_aliased {Δ a m}
    (ha : Subtype Δ (.modal a (.const Mode.aliased)) a) (hm : Entails Δ (.defined m)) :
    Subtype Δ (.modal (.modal a m) (.const Mode.aliased)) (.modal a m) :=
  (Subtype.modal_comm (n := .const Mode.aliased) hm (fun _ _ => rfl)).trans (.congr ha (.refl hm))

theorem Scheme.refined_shared_lockAll_join {s : Scheme} {q : Nat} {ms : List ModExpr} {Δ : Bounds}
    (hf : (s.refineMode q).FreshForBounds Δ) :
    ContextJoin Δ [some ((s.share.refineMode q).lockAll ms).withAssumptions]
      [some ((s.share.refineMode q).lockAll ms).withAssumptions]
      [some (((s.share.refineMode q).lockAll ms).withAssumptions.modal (.const Mode.many))] := by
  refine .shared .nil ?_ (Scheme.lockAll_aliased
    ((Subtype.aliased_idempotent _ _).modal_aliased (m := .var (.flex q)) (fun _ _ => rfl))
    (Bounds.assumptions_entails_append _ _))
  simpa only [FreshForBounds, withAssumptions, ((s.share.refineMode q).lockAll_params ms).1,
    ((s.share.refineMode q).lockAll_params ms).2] using
    (show (s.share.refineMode q).FreshForBounds Δ from hf)

end ModalityInference
