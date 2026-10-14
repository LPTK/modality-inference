import ModalityInference.Proofs.SchemeFreshening

/-! Quantified modal weakening of schemes and its syntactic instance contracts. -/
namespace ModalityInference

def Substitution.extendMode (σ : Substitution) (p : Nat) (m : ModExpr) : Substitution :=
  {σ with modes := σ.modes ++ [(p, m)]}

theorem Substitution.extendMode_type (σ : Substitution) (p : Nat) (m : ModExpr) :
    (σ.extendMode p m).type = σ.type := rfl

theorem Substitution.extendMode_mode (σ : Substitution) (p : Nat) (m : ModExpr)
    {v : ModVar} (hv : v ≠ .flex p) : (σ.extendMode p m).mode v = σ.mode v := by
  cases v <;> simp_all [extendMode, mode, List.lookup_append, List.lookup_cons]
  split <;> simp_all [beq_iff_eq]

theorem Substitution.extendMode_at (σ : Substitution) (p : Nat) (m : ModExpr)
    (hp : p ∉ σ.modes.map Prod.fst) : (σ.extendMode p m).mode (.flex p) = m := by
  have he : σ.modes.lookup p = none := List.lookup_eq_none_iff.mpr fun q hq =>
    bne_iff_ne.mpr (fun h => hp (List.mem_map.mpr ⟨q, hq, h.symm⟩))
  simp [extendMode, mode, List.lookup_append, he]

theorem Substitution.extendMode_ty (σ : Substitution) (p : Nat) (m : ModExpr)
    (a : Ty) (hp : .flex p ∉ a.modVars) : (σ.extendMode p m).ty a = σ.ty a := by
  exact a.subst_congr (fun _ _ => rfl)
    (fun v hv => σ.extendMode_mode p m (fun he => hp (he ▸ hv)))

theorem Substitution.extendMode_modExpr (σ : Substitution) (p : Nat) (m n : ModExpr)
    (hp : .flex p ∉ n.vars) : n.subst (σ.extendMode p m).mode = n.subst σ.mode := by
  exact n.subst_congr (fun v hv => σ.extendMode_mode p m (fun he => hp (he ▸ hv)))

theorem Substitution.extendMode_bounds (σ : Substitution) (p : Nat) (m : ModExpr)
    (cs Δ : Bounds) (hp : .flex p ∉ cs.modVars) :
    EntailsAll Δ ((σ.extendMode p m).bounds cs) ↔ EntailsAll Δ (σ.bounds cs) := by
  simp only [EntailsAll, Substitution.bounds, List.forall_mem_map]
  exact forall_congr' fun c => forall_congr' fun hc =>
    Substitution.constraint_entails_congr_on c Δ (fun _ _ => rfl)
      (fun v hv => σ.extendMode_mode p m (fun he => hp
        ((cs.mem_modVars_iff _).mpr ⟨c, hc, he ▸ hv⟩)))

theorem Instantiates.refineMode {s : Scheme} {σ : Substitution} (h : Instantiates s σ)
    (p : Nat) (m : ModExpr) : Instantiates (s.refineMode p) (σ.extendMode p m) := by
  exact ⟨h.1, by simpa [Substitution.extendMode, Scheme.refineMode] using h.2.append_right [p]⟩

theorem Scheme.refineMode_freshSubstitution (s : Scheme) (p nt nm : Nat) (rigid : Bool) :
    (s.refineMode p).freshSubstitution nt nm rigid =
      (s.freshSubstitution nt nm rigid).extendMode p
        (.var (if rigid then .rigid (nm + s.modParams.length) else .flex (nm + s.modParams.length))) := by
  simp [refineMode, freshSubstitution, Substitution.extendMode, List.zipIdx_append]

theorem Scheme.refineMode_fresh {s : Scheme} {p : Nat} (hp : s.freshModeIndex ≤ p) :
    p ∉ s.modParams ∧ .flex p ∉ s.body.modVars ∧ .flex p ∉ s.bounds.modVars := by
  exact ⟨fun h => (Nat.not_lt.mpr hp) (s.modeParam_lt_freshModeIndex h),
    fun h => (Nat.not_lt.mpr hp) (s.lt_freshModeIndex (Finset.mem_union_left _ h)),
    fun h => (Nat.not_lt.mpr hp) (s.lt_freshModeIndex (Finset.mem_union_right _ h))⟩

theorem Instantiates.refineMode_body {s : Scheme} {σ : Substitution} {p : Nat}
    (h : Instantiates s σ) (hp : s.freshModeIndex ≤ p) (m : ModExpr) :
    (σ.extendMode p m).ty (s.refineMode p).body = .modal (σ.ty s.body) m := by
  change TypeExpr.modal ((σ.extendMode p m).ty s.body) ((σ.extendMode p m).mode (.flex p)) = _
  rw [σ.extendMode_ty p m s.body (Scheme.refineMode_fresh hp).2.1,
    σ.extendMode_at p m (fun hn => (Scheme.refineMode_fresh hp).1 (h.2.mem_iff.mp hn))]

theorem Instantiates.refineMode_bounds {s : Scheme} {σ : Substitution} {p : Nat}
    (h : Instantiates s σ) (hp : s.freshModeIndex ≤ p) (m : ModExpr) (Δ : Bounds) :
    EntailsAll Δ ((σ.extendMode p m).bounds (s.refineMode p).bounds) ↔
      EntailsAll Δ (σ.bounds s.bounds) ∧ Entails Δ (.sub (σ.ty s.body) (.modal (σ.ty s.body) m)) := by
  change Solution (s.bounds ++ [.sub s.body (s.refineMode p).body]) Δ (σ.extendMode p m) ↔ _
  rw [Solution.append, Solution, σ.extendMode_bounds p m s.bounds Δ (Scheme.refineMode_fresh hp).2.2]
  apply and_congr Iff.rfl
  change EntailsAll Δ [.sub ((σ.extendMode p m).ty s.body)
    ((σ.extendMode p m).ty (s.refineMode p).body)] ↔ _
  simp [EntailsAll, h.refineMode_body hp m,
    σ.extendMode_ty p m s.body (Scheme.refineMode_fresh hp).2.1]

theorem Scheme.subsumes_refineMode {s : Scheme} {p : Nat} (hp : s.freshModeIndex ≤ p)
    (Δ : Bounds) : Subsumes Δ s (s.refineMode p) := by
  simp only [Subsumes, Scheme.instantiate, refineMode_freshSubstitution]
  let σ := s.freshSubstitution (s.subsumptionIndices Δ (s.refineMode p)).1
    (s.subsumptionIndices Δ (s.refineMode p)).2 true
  let m := ModExpr.var (.rigid ((s.subsumptionIndices Δ (s.refineMode p)).2 + s.modParams.length))
  have hi : Instantiates s σ := s.freshSubstitution_instantiates _ _ _
  have hb := (hi.refineMode_bounds hp m
    (Δ ++ ((σ.extendMode p m).bounds (s.refineMode p).bounds).assumptions)).mp
      (Bounds.assumptions_entails_append _ _)
  exact ⟨σ, hi, hb.1, (hi.refineMode_body hp m).symm ▸ hb.2.1⟩

theorem Instantiates.refineMode_lock_body {s : Scheme} {σ : Substitution} {p : Nat}
    (h : Instantiates s σ) (hp : s.freshModeIndex ≤ p) (m n : ModExpr)
    (hn : .flex p ∉ n.vars) :
    (σ.extendMode p m).ty ((s.refineMode p).lock n).body =
      .modal (.modal (σ.ty s.body) m) (.capture (n.subst σ.mode)) := by
  change TypeExpr.modal ((σ.extendMode p m).ty (s.refineMode p).body)
    (.capture (n.subst (σ.extendMode p m).mode)) = _
  rw [h.refineMode_body hp m, σ.extendMode_modExpr p m n hn]

theorem Scheme.lock_instance_bounds (s : Scheme) (σ : Substitution) (m : ModExpr) (Δ : Bounds) :
    EntailsAll Δ (σ.bounds (s.lock m).bounds) ↔
      EntailsAll Δ (σ.bounds s.bounds) ∧
        Entails Δ (.sub (σ.ty s.body) (.modal (σ.ty s.body) (.future (m.subst σ.mode)))) := by
  simp [Scheme.lock, EntailsAll, Substitution.bounds, Substitution.constraint, Constraint.subst,
    Substitution.ty, TypeExpr.subst, ModExpr.subst, or_imp, forall_and]

theorem Instantiates.refineMode_lock_bounds {s : Scheme} {σ : Substitution} {p : Nat}
    (h : Instantiates s σ) (hp : s.freshModeIndex ≤ p) (m n : ModExpr)
    (hn : .flex p ∉ n.vars) (Δ : Bounds) :
    EntailsAll Δ ((σ.extendMode p m).bounds ((s.refineMode p).lock n).bounds) ↔
      EntailsAll Δ (σ.bounds s.bounds) ∧
        Entails Δ (.sub (σ.ty s.body) (.modal (σ.ty s.body) m)) ∧
        Entails Δ (.sub (.modal (σ.ty s.body) m)
          (.modal (.modal (σ.ty s.body) m) (.future (n.subst σ.mode)))) := by
  simp only [Scheme.lock_instance_bounds, h.refineMode_bounds hp m Δ,
    h.refineMode_body hp m, σ.extendMode_modExpr p m n hn, and_assoc]

theorem Scheme.refineMode_retains_instance {s : Scheme} {σ : Substitution} {p : Nat} {Δ : Bounds}
    (hi : Instantiates s σ) (hp : s.freshModeIndex ≤ p)
    (hb : EntailsAll Δ (σ.bounds s.bounds)) (hd : (σ.ty s.body).DefinedUnder Δ) :
    ∃ θ, Instantiates (s.refineMode p) θ ∧ EntailsAll Δ (θ.bounds (s.refineMode p).bounds) ∧
      Subtype Δ (θ.ty (s.refineMode p).body) (σ.ty s.body) ∧
      Subtype Δ (σ.ty s.body) (θ.ty (s.refineMode p).body) := by
  refine ⟨σ.extendMode p .epsilon, hi.refineMode p .epsilon,
    (hi.refineMode_bounds hp .epsilon Δ).mpr ⟨hb, .identityRev, hd, ?_⟩,
    (hi.refineMode_body hp .epsilon).symm ▸ Subtype.identity,
    (hi.refineMode_body hp .epsilon).symm ▸ Subtype.identityRev⟩
  exact TypeExpr.definedUnder_modal.mpr ⟨hd, fun _ _ => rfl⟩

theorem Scheme.refineMode_freshForBounds (s : Scheme) (p : Nat) (Δ : Bounds) :
    (s.refineMode p).FreshForBounds Δ ↔ s.FreshForBounds Δ ∧ .flex p ∉ Δ.modVars := by
  simp [FreshForBounds, refineMode, List.mem_append, or_imp, forall_and, and_assoc]

theorem Scheme.refineMode_freshForMode (s : Scheme) (p : Nat) (m : ModExpr) :
    (s.refineMode p).FreshForMode m ↔ s.FreshForMode m ∧ .flex p ∉ m.vars := by
  simp [FreshForMode, refineMode, List.mem_append, or_imp, forall_and]

theorem Scheme.subsumes_refineMode_addAssumptions {s : Scheme} {p : Nat}
    (hp : s.freshModeIndex ≤ p) (cs Δ : Bounds) :
    Subsumes Δ s {s.refineMode p with bounds := ((s.refineMode p).bounds ++ cs).assumptions} := by
  let target := {s.refineMode p with bounds := ((s.refineMode p).bounds ++ cs).assumptions}
  have he (nt nm : Nat) (rigid : Bool) : target.freshSubstitution nt nm rigid =
      (s.refineMode p).freshSubstitution nt nm rigid := rfl
  change Subsumes Δ s target
  simp only [Subsumes, Scheme.instantiate, he, refineMode_freshSubstitution]
  let σ := s.freshSubstitution (s.subsumptionIndices Δ target).1 (s.subsumptionIndices Δ target).2 true
  let m := ModExpr.var (.rigid ((s.subsumptionIndices Δ target).2 + s.modParams.length))
  have hi : Instantiates s σ := s.freshSubstitution_instantiates _ _ _
  have hx : EntailsAll (Δ ++ ((σ.extendMode p m).bounds target.bounds).assumptions)
      ((σ.extendMode p m).bounds target.bounds) := Bounds.assumptions_entails_append _ _
  have hb := (hi.refineMode_bounds hp m _).mp
    (Solution.append.mp (EntailsAll.of_subst_assumptions hx)).1
  exact ⟨σ, hi, hb.1, (hi.refineMode_body hp m).symm ▸ hb.2.1⟩

theorem Scheme.refineMode_lock {s : Scheme} {p : Nat} {Δ : Bounds} {m : ModExpr}
    (hp : s.freshModeIndex ≤ p) (hb : (s.refineMode p).FreshForBounds Δ)
    (hm : (s.refineMode p).FreshForMode m) :
    ∃ source, Subsumes Δ s source ∧
      Lock Δ m [some source] [some ((s.refineMode p).lock m).withAssumptions] := by
  refine ⟨{s.refineMode p with bounds := ((s.refineMode p).lock m).bounds.assumptions},
    s.subsumes_refineMode_addAssumptions hp
      [.sub (s.refineMode p).body (.modal (s.refineMode p).body (.future m))] Δ,
    .keep .nil hb hm (.bound ?_)⟩
  simp [Scheme.lock, Bounds.assumptions, Constraint.assumptions]

theorem Scheme.share_instance_bounds (s : Scheme) (σ : Substitution) (Δ : Bounds) :
    EntailsAll Δ (σ.bounds s.share.bounds) ↔
      EntailsAll Δ (σ.bounds s.bounds) ∧
        Entails Δ (.sub (σ.ty s.body) (.modal (σ.ty s.body) (.const Mode.many))) := by
  simp [Scheme.share, EntailsAll, Substitution.bounds, Substitution.constraint, Constraint.subst,
    Substitution.ty, TypeExpr.subst, ModExpr.subst, or_imp, forall_and]

theorem Scheme.refineMode_lock_shared_instance {s : Scheme} {σ : Substitution} {p : Nat}
    {n : ModExpr} {Δ : Bounds} (hi : Instantiates (s.share.lock n) σ)
    (hp : s.freshModeIndex ≤ p) (hn : .flex p ∉ n.vars)
    (hb : EntailsAll Δ (σ.bounds (s.share.lock n).bounds)) :
    ∃ θ, Instantiates ((s.refineMode p).lock n) θ ∧
      EntailsAll Δ (θ.bounds ((s.refineMode p).lock n).bounds) ∧
      θ.ty ((s.refineMode p).lock n).body = σ.ty (s.share.lock n).body := by
  have hl := (s.share.lock_instance_bounds σ n Δ).mp hb
  have hs := (s.share_instance_bounds σ Δ).mp hl.1
  have hi₀ : Instantiates s σ := hi
  refine ⟨σ.extendMode p (.const Mode.aliased), hi₀.refineMode p (.const Mode.aliased),
    (hi₀.refineMode_lock_bounds hp (.const Mode.aliased) n hn Δ).mpr ⟨hs.1, ?_, hl.2⟩,
    hi₀.refineMode_lock_body hp (.const Mode.aliased) n hn⟩
  exact ⟨Subtype.identityRev.trans (.congr .refl (.valid fun _ _ =>
    ⟨_, _, rfl, rfl, by decide⟩)), hs.2.2.1,
    TypeExpr.definedUnder_modal.mpr ⟨hs.2.2.1, fun _ _ => rfl⟩⟩

theorem Subtype.modal_many {Δ a m} (h : Subtype Δ a (.modal a (.const Mode.many)))
    (hm : Entails Δ (.defined m)) :
    Subtype Δ (.modal a m) (.modal (.modal a m) (.const Mode.many)) :=
  (Subtype.congr h (.refl hm)).trans (Subtype.modal_comm (fun _ _ => rfl) hm)

theorem Entails.defined_capture_of_future {Δ m} (h : Entails Δ (.defined (.future m))) :
    Entails Δ (.defined (.capture m)) := by
  intro η hη
  cases he : m.eval (some ∘ η)
  · simpa [ModExpr.WellFormed, ModExpr.eval, he] using h η hη
  · simp [ModExpr.WellFormed, ModExpr.eval, he]

theorem Scheme.refineMode_lock_subsumes_shared {s : Scheme} {p : Nat} {n : ModExpr}
    (hp : s.freshModeIndex ≤ p) (hn : .flex p ∉ n.vars) (Δ : Bounds) :
    Subsumes Δ ((s.refineMode p).lock n).withAssumptions
      ((s.share.lock n).withAssumptions.modal (.const Mode.many)) := by
  refine Subsumes.of_instances (fun Ξ σ hi hb => ?_)
  obtain ⟨θ, hθ, hbounds, hbody⟩ := s.refineMode_lock_shared_instance hi hp hn hb.of_subst_assumptions
  have hl := (s.share.lock_instance_bounds σ n Ξ).mp hb.of_subst_assumptions
  refine ⟨θ, hθ, hbounds.subst_assumptions, hbody.symm ▸ ?_⟩
  exact (((s.share_instance_bounds σ Ξ).mp hl.1).2.1.modal_many
    (m := .const Mode.aliased) (fun _ _ => rfl)).modal_many
    (Entails.defined_capture_of_future (TypeExpr.definedUnder_modal.mp hl.2.2.2).2)

theorem Scheme.shared_lock_join {s : Scheme} {n : ModExpr} {Δ : Bounds}
    (hf : s.FreshForBounds Δ) :
    ContextJoin Δ [some (s.share.lock n).withAssumptions] [some (s.share.lock n).withAssumptions]
      [some ((s.share.lock n).withAssumptions.modal (.const Mode.many))] := by
  have hn : Entails (Δ ++ (s.share.lock n).withAssumptions.bounds) (.defined (.future n)) :=
    fun η hη => hη (.defined (.future n)) (by simp [Scheme.withAssumptions, Scheme.lock, Bounds.assumptions,
      Constraint.assumptions, TypeExpr.wellFormedBounds])
  exact .shared .nil hf
    ((Subtype.modal_comm (n := .const Mode.aliased) hn.defined_capture_of_future (fun _ _ => rfl)).trans
      (.congr (Subtype.aliased_idempotent _ _) (.refl hn.defined_capture_of_future)))

theorem Scheme.refineMode_lock_instance {s : Scheme} {σ : Substitution} {p : Nat}
    {n : ModExpr} {Δ : Bounds} (hi : Instantiates (s.lock n) σ)
    (hp : s.freshModeIndex ≤ p) (hn : .flex p ∉ n.vars)
    (hb : EntailsAll Δ (σ.bounds (s.lock n).bounds)) :
    ∃ θ, Instantiates ((s.refineMode p).lock n) θ ∧
      EntailsAll Δ (θ.bounds ((s.refineMode p).lock n).bounds) ∧
      Subtype Δ (θ.ty ((s.refineMode p).lock n).body) (σ.ty (s.lock n).body) ∧
      Subtype Δ (σ.ty (s.lock n).body) (θ.ty ((s.refineMode p).lock n).body) := by
  have hl := (s.lock_instance_bounds σ n Δ).mp hb
  have hi₀ : Instantiates s σ := hi
  have hf := (TypeExpr.definedUnder_modal.mp hl.2.2.2).2
  have hd : (TypeExpr.modal (σ.ty s.body) .epsilon).DefinedUnder Δ :=
    TypeExpr.definedUnder_modal.mpr ⟨hl.2.2.1, fun _ _ => rfl⟩
  refine ⟨σ.extendMode p .epsilon, hi₀.refineMode p .epsilon,
    (hi₀.refineMode_lock_bounds hp .epsilon n hn Δ).mpr
      ⟨hl.1, ⟨.identityRev, hl.2.2.1, hd⟩, ⟨?_, hd, TypeExpr.definedUnder_modal.mpr ⟨hd, hf⟩⟩⟩,
    (hi₀.refineMode_lock_body hp .epsilon n hn).symm ▸
      Subtype.congr .identity (.refl (Entails.defined_capture_of_future hf)),
    (hi₀.refineMode_lock_body hp .epsilon n hn).symm ▸
      Subtype.congr .identityRev (.refl (Entails.defined_capture_of_future hf))⟩
  exact Subtype.identity.trans (hl.2.1.trans (.congr .identityRev (.refl hf)))

theorem Scheme.refineMode_lock_subsumes {s : Scheme} {p : Nat} {n : ModExpr}
    (hp : s.freshModeIndex ≤ p) (hn : .flex p ∉ n.vars) (Δ : Bounds) :
    Subsumes Δ ((s.refineMode p).lock n).withAssumptions (s.lock n).withAssumptions := by
  apply Subsumes.of_instances
  intro Ξ σ hi hb
  obtain ⟨θ, hθ, hbounds, hsub, _⟩ := s.refineMode_lock_instance hi hp hn hb.of_subst_assumptions
  exact ⟨θ, hθ, hbounds.subst_assumptions, hsub⟩

theorem Scheme.freshened_refineMode_lock (s : Scheme) (Δ : Bounds) (m : ModExpr) :
    let avoid := Δ ++ [.defined m]
    let fresh := s.freshenedFor avoid
    let p := max fresh.freshModeIndex avoid.freshModeIndex
    ∃ source, Subsumes Δ s fresh ∧ Subsumes Δ fresh source ∧
      Lock Δ m [some source] [some ((fresh.refineMode p).lock m).withAssumptions] := by
  dsimp only
  let avoid := Δ ++ [.defined m]
  let fresh := s.freshenedFor avoid
  let p := max fresh.freshModeIndex avoid.freshModeIndex
  have hp : ModVar.flex p ∉ avoid.modVars := fun hv =>
    (Nat.not_lt.mpr (Nat.le_max_right fresh.freshModeIndex avoid.freshModeIndex))
      (Bounds.lt_freshModeIndex ((avoid.mem_modeVariables _).mpr hv))
  have hf : (fresh.refineMode p).FreshForBounds avoid :=
    (fresh.refineMode_freshForBounds p avoid).mpr ⟨s.freshenedFor_fresh avoid, hp⟩
  obtain ⟨source, hsource, hlock⟩ := fresh.refineMode_lock (m := m) (Nat.le_max_left _ _)
    (hf.of_subset (fun _ hc => List.mem_append_left _ hc)) (hf.defined (by simp [avoid]))
  exact ⟨source, s.subsumes_freshenedFor Δ avoid, hsource, hlock⟩

end ModalityInference
