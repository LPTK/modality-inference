import ModalityInference.Proofs.GuardedRefinedReuse
import ModalityInference.Proofs.GenerationSoundness

/-! Hygienic generation produces source derivations with guarded scheme replacement. -/
namespace ModalityInference

theorem Generates.Hygienic.guarded_typing_refined {Γ t a cs} {hg : Generates Γ t a cs}
    (hh : hg.Hygienic) (hΓ : Γ.LocksScoped) {Δ σ}
    (hs : Solution cs Δ σ) (hσ : σ.WellFormedUnder Δ) :
    ∃ needed : Bounds, Δ ⊆ needed ∧ ∀ avoid : Bounds, needed ⊆ avoid →
      ∃ lower, ∀ p ≥ lower,
        GuardedRawTyping Δ ((Γ.substAvoid σ avoid).refinedContext p) t (σ.ty a) := by
  induction hh generalizing Δ σ
  case defn Γ rhs body a b cs ds residual τ hc hr hsolve hb hhr hhb ihr ihb =>
    obtain ⟨neededR, _, hR⟩ := ihr trivial hsolve.1 hsolve.2.2
    obtain ⟨nR, hR⟩ := hR neededR (fun _ h => h)
    obtain ⟨rhs', hrerase, hrt⟩ := hR nR (Nat.le_refl _)
    obtain ⟨needed, hΔ, hB⟩ := ihb hΓ hs hσ
    refine ⟨needed, hΔ, fun avoid havoid => ?_⟩
    obtain ⟨nB, hB⟩ := hB avoid havoid
    refine ⟨max nB ((Scheme.generalize residual (τ.ty a)).substAvoid σ avoid).freshModeIndex,
      fun p hp => ?_⟩
    obtain ⟨body', hberase, hbt⟩ := hB p ((Nat.le_max_left _ _).trans hp)
    exact ⟨.defn rhs' body', congrArg₂ Term.defn hrerase hberase,
      .defn hrt hsolve.2.1 (hbt.weakening (.keep (.refl _ _)
        (Scheme.generalize_subsumesUnder_substAvoid_refined residual (τ.ty a) σ avoid Δ
          ((Nat.le_max_right _ _).trans hp))))⟩
  case lam Γ t a b m cs ht hf hht ih =>
    obtain ⟨needed, hΔ, hbody⟩ := ih ⟨hf, hΓ⟩ hs hσ
    refine ⟨needed ++ [.defined (σ.mode (.flex m))],
      fun _ hc => List.mem_append_left _ (hΔ hc), fun avoid havoid => ?_⟩
    obtain ⟨nB, hbody⟩ := hbody avoid (fun _ hc => havoid (List.mem_append_left _ hc))
    obtain ⟨nF, hF⟩ := AlgorithmicContext.substAvoid_refinementFresh_eventually
      (.binding (some (.mono (.var (.flex a)))) :: .lock (.var (.flex m)) :: Γ)
      σ Δ avoid (fun _ hc => havoid (List.mem_append_left _ (hΔ hc)))
    refine ⟨max nB nF, fun p hp => ?_⟩
    obtain ⟨t', herase, htyping⟩ := hbody p ((Nat.le_max_left _ _).trans hp)
    have hfresh := hF p ((Nat.le_max_right _ _).trans hp)
    simp only [AlgorithmicContext.substAvoid, AlgorithmicContext.transform, List.map_cons,
      Option.map_some, Scheme.mono_substAvoid] at hfresh htyping
    refine ⟨_, ?_,
      GuardedTyping.lam_refined hfresh.tail.tail
        (AlgorithmicContext.substAvoid_freshForMode Γ σ avoid
          (havoid (by simp [ModExpr.subst])))
        (hfresh.tail.2 _ List.mem_cons_self) (hfresh.1 _ List.mem_cons_self).1
        (((σ.type (.flex a)).definedUnder_iff_entails_wellFormed Δ).mp (hσ.types _))
        (hσ.modes _) htyping⟩
    exact congrArg (Term.lam ()) herase
  case var Γ i s θ hl hi =>
    let locks : Bounds := Γ.filterMap fun
      | .binding _ => none
      | .lock m => some (.defined (m.subst σ.mode))
    refine ⟨Δ ++ locks, fun _ hc => List.mem_append_left _ hc, fun avoid havoid => ?_⟩
    obtain ⟨n, hn⟩ := hl.substAvoid_refined_guarded_typing hi hΓ avoid
      (fun m hm => havoid (List.mem_append_right _ (List.mem_filterMap.mpr ⟨.lock m, hm, rfl⟩)))
      (fun _ hc => havoid (List.mem_append_left _ hc)) (Solution.append.mp hs).1
      (hσ.type_of_guards _ (Solution.append.mp hs).2)
    exact ⟨n, fun p hp => ⟨.var i, rfl, hn p hp⟩⟩
  case unit Γ =>
    exact ⟨Δ, fun _ h => h, fun _ _ => ⟨0, fun _ _ =>
      ⟨.unit, rfl, .unit (fun _ _ => rfl)⟩⟩⟩
  case pair Γ Γ₁ Γ₂ x y a b c d m cs ds hj hx hy hhx hhy ihx ihy
     | stackPair Γ Γ₁ Γ₂ x y a b c d m cs ds hj hx hy hhx hhy ihx ihy =>
    simp only [Solution.append] at hs
    obtain ⟨needX, hΔ, hX⟩ := ihx (hj.locksScoped hΓ).1 hs.1.1 hσ
    obtain ⟨needY, _, hY⟩ := ihy (hj.locksScoped hΓ).2 hs.1.2 hσ
    refine ⟨needX ++ needY, fun _ hc => List.mem_append_left _ (hΔ hc), fun avoid havoid => ?_⟩
    obtain ⟨nX, hX⟩ := hX avoid (fun _ hc => havoid (List.mem_append_left _ hc))
    obtain ⟨nY, hY⟩ := hY avoid (fun _ hc => havoid (List.mem_append_right _ hc))
    obtain ⟨nF, hF⟩ := Γ.substAvoid_refinementFresh_eventually σ Δ avoid
      (fun _ hc => havoid (List.mem_append_left _ (hΔ hc)))
    refine ⟨max (max nX nY) nF, fun p hp => ?_⟩
    have hxy := (Nat.le_max_left _ _).trans hp
    obtain ⟨x', hex, hxt⟩ := hX p ((Nat.le_max_left _ _).trans hxy)
    obtain ⟨y', hey, hyt⟩ := hY p ((Nat.le_max_right _ _).trans hxy)
    obtain ⟨joined, hc, hjoin⟩ := (hj.substAvoid σ avoid).declarative_refined_guarded
      (hF p ((Nat.le_max_right _ _).trans hp)) [] (by simp)
    have hleft := hs.2 _ (List.mem_map_of_mem (by simp : Constraint.sub a (.modal c m) ∈ _))
    have hright := hs.2 _ (List.mem_map_of_mem (by simp : Constraint.sub b (.modal d m) ∈ _))
    first
    | exact ⟨.pair x' y', congrArg₂ Term.pair hex hey,
        (GuardedSourceTyping.pair hjoin (hxt.subs (.refl _ _) hleft.1)
          (hyt.subs (.refl _ _) hright.1)).weakening hc⟩
    | exact ⟨.stackPair x' y', congrArg₂ Term.stackPair hex hey,
        (GuardedSourceTyping.stackPair hjoin (hxt.subs (.refl _ _) hleft.1)
          (hyt.subs (.refl _ _) hright.1)
          (.refl (TypeExpr.definedUnder_modal.mp hleft.2.2).2)
          (hs.2 _ (List.mem_map_of_mem (by simp : Constraint.mode (.const Mode.localLower) m ∈ _)))).weakening hc⟩
  case app Γ Γ₁ Γ₂ f x a b c m cs ds hj hf hx hhf hhx ihf ihx =>
    simp only [Solution.append] at hs
    obtain ⟨needF, hΔ, hF⟩ := ihf (hj.locksScoped hΓ).1 hs.1.1 hσ
    obtain ⟨needX, _, hX⟩ := ihx (hj.locksScoped hΓ).2 hs.1.2 hσ
    refine ⟨needF ++ needX, fun _ hc => List.mem_append_left _ (hΔ hc), fun avoid havoid => ?_⟩
    obtain ⟨nF, hF⟩ := hF avoid (fun _ hc => havoid (List.mem_append_left _ hc))
    obtain ⟨nX, hX⟩ := hX avoid (fun _ hc => havoid (List.mem_append_right _ hc))
    obtain ⟨nC, hC⟩ := Γ.substAvoid_refinementFresh_eventually σ Δ avoid
      (fun _ hc => havoid (List.mem_append_left _ (hΔ hc)))
    refine ⟨max (max nF nX) nC, fun p hp => ?_⟩
    have hfx := (Nat.le_max_left _ _).trans hp
    obtain ⟨f', hef, hft⟩ := hF p ((Nat.le_max_left _ _).trans hfx)
    obtain ⟨x', hex, hxt⟩ := hX p ((Nat.le_max_right _ _).trans hfx)
    obtain ⟨joined, hc, hjoin⟩ := (hj.substAvoid σ avoid).declarative_refined_guarded
      (hC p ((Nat.le_max_right _ _).trans hp)) [] (by simp)
    have hfn := hs.2 _ (List.mem_map_of_mem (by simp : Constraint.sub a (.modal (.fn b c) m) ∈ _))
    exact ⟨.app f' x', congrArg₂ Term.app hef hex,
      (GuardedSourceTyping.app hjoin (hft.subs (.refl _ _)
        (hfn.1.trans (.fn_modal_forget (TypeExpr.definedUnder_modal.mp hfn.2.2).2))) hxt).weakening hc⟩
  case inl Γ x a b c m cs hx hhx ih
     | inr Γ x a b c m cs hx hhx ih =>
    simp only [Solution.append] at hs
    obtain ⟨needed, hΔ, hX⟩ := ih hΓ hs.1 hσ
    refine ⟨needed, hΔ, fun avoid havoid => ?_⟩
    obtain ⟨n, hX⟩ := hX avoid havoid
    refine ⟨n, fun p hp => ?_⟩
    obtain ⟨x', hex, hxt⟩ := hX p hp
    have hsub := hs.2 _ (List.mem_map_of_mem List.mem_cons_self)
    first
    | exact ⟨.inl x', congrArg Term.inl hex,
        .inl (((σ.type (.flex c)).definedUnder_iff_entails_wellFormed Δ).mp (hσ.types _))
          (hxt.subs (.refl _ _) hsub.1)⟩
    | exact ⟨.inr x', congrArg Term.inr hex,
        .inr (((σ.type (.flex b)).definedUnder_iff_entails_wellFormed Δ).mp (hσ.types _))
          (hxt.subs (.refl _ _) hsub.1)⟩
  case region Γ t a b cs ht hht ih =>
    simp only [Solution.append] at hs
    obtain ⟨needed, hΔ, hT⟩ := ih hΓ hs.1 hσ
    refine ⟨needed, hΔ, fun avoid havoid => ?_⟩
    obtain ⟨n, hT⟩ := hT avoid havoid
    refine ⟨n, fun p hp => ?_⟩
    obtain ⟨t', het, htt⟩ := hT p hp
    have hsub := hs.2 _ (List.mem_map_of_mem List.mem_cons_self)
    exact ⟨.region t', congrArg Term.region het, .region (htt.subs (.refl _ _) hsub.1)⟩
  case split Γ Γ₁ Γ₂ x body a b c d m cs ds hj hx hb hhx hhb ihx ihb =>
    simp only [Solution.append] at hs
    obtain ⟨needX, hΔ, hX⟩ := ihx (hj.locksScoped hΓ).1 hs.1.1 hσ
    obtain ⟨needB, _, hB⟩ := ihb (hj.locksScoped hΓ).2 hs.1.2 hσ
    refine ⟨needX ++ needB, fun _ hc => List.mem_append_left _ (hΔ hc), fun avoid havoid => ?_⟩
    obtain ⟨nX, hX⟩ := hX avoid (fun _ hc => havoid (List.mem_append_left _ hc))
    obtain ⟨nB, hB⟩ := hB avoid (fun _ hc => havoid (List.mem_append_right _ hc))
    obtain ⟨nF, hF⟩ := Γ.substAvoid_refinementFresh_eventually σ Δ avoid
      (fun _ hc => havoid (List.mem_append_left _ (hΔ hc)))
    refine ⟨nX + nB + nF + (Scheme.mono (σ.ty (.modal .credit m))).freshModeIndex +
      (Scheme.mono (σ.ty (.modal b m))).freshModeIndex +
      (Scheme.mono (σ.ty (.modal c m))).freshModeIndex, fun p hp => ?_⟩
    obtain ⟨x', hex, hxt⟩ := hX p (by omega)
    obtain ⟨body', heb, hbt⟩ := hB p (by omega)
    obtain ⟨joined, hc, hjoin⟩ := (hj.substAvoid σ avoid).declarative_refined_guarded
      (hF p (by omega)) [] (by simp)
    simp only [AlgorithmicContext.substAvoid, AlgorithmicContext.transform, List.map_cons,
      Option.map_some, Scheme.mono_substAvoid] at hbt
    simp only [Substitution.ty, TypeExpr.subst] at hp
    exact ⟨.split x' body', congrArg₂ Term.split hex heb,
      (GuardedSourceTyping.split hjoin
        (hxt.subs (.refl _ _) (hs.2 _ (List.mem_map_of_mem List.mem_cons_self)).1)
        (hbt.weakening (.keep (.keep (.keep (.refl _ _)
          (Scheme.subsumesUnder_refineMode_withAssumptions (by omega) Δ))
          (Scheme.subsumesUnder_refineMode_withAssumptions (by omega) Δ))
          (Scheme.subsumesUnder_refineMode_withAssumptions (by omega) Δ)))).weakening hc⟩
  case «case» Γ Γ₁ Γ₂ x l r a b c d e f m cs ds es hj hx hl hr hhx hhl hhr ihx ihl ihr =>
    simp only [Solution.append] at hs
    obtain ⟨needX, hΔ, hX⟩ := ihx (hj.locksScoped hΓ).1 hs.1.1.1 hσ
    obtain ⟨needL, _, hL⟩ := ihl (hj.locksScoped hΓ).2 hs.1.1.2 hσ
    obtain ⟨needR, _, hR⟩ := ihr (hj.locksScoped hΓ).2 hs.1.2 hσ
    refine ⟨needX ++ needL ++ needR,
      fun _ hc => List.mem_append_left _ (List.mem_append_left _ (hΔ hc)), fun avoid havoid => ?_⟩
    obtain ⟨nX, hX⟩ := hX avoid (fun _ hc => havoid (List.mem_append_left _ (List.mem_append_left _ hc)))
    obtain ⟨nL, hL⟩ := hL avoid (fun _ hc => havoid (List.mem_append_left _ (List.mem_append_right _ hc)))
    obtain ⟨nR, hR⟩ := hR avoid (fun _ hc => havoid (List.mem_append_right _ hc))
    obtain ⟨nF, hF⟩ := Γ.substAvoid_refinementFresh_eventually σ Δ avoid
      (fun _ hc => havoid (List.mem_append_left _ (List.mem_append_left _ (hΔ hc))))
    refine ⟨nX + nL + nR + nF + (Scheme.mono (σ.ty (.modal b m))).freshModeIndex +
      (Scheme.mono (σ.ty (.modal c m))).freshModeIndex, fun p hp => ?_⟩
    obtain ⟨x', hex, hxt⟩ := hX p (by omega)
    obtain ⟨l', hel, hlt⟩ := hL p (by omega)
    obtain ⟨r', her, hrt⟩ := hR p (by omega)
    obtain ⟨joined, hc, hjoin⟩ := (hj.substAvoid σ avoid).declarative_refined_guarded
      (hF p (by omega)) [] (by simp)
    simp only [AlgorithmicContext.substAvoid, AlgorithmicContext.transform, List.map_cons,
      Option.map_some, Scheme.mono_substAvoid] at hlt hrt
    simp only [Substitution.ty, TypeExpr.subst] at hp
    refine ⟨.case x' l' r', ?_,
      (GuardedSourceTyping.case hjoin
        (hxt.subs (.refl _ _) (hs.2 _ (List.mem_map_of_mem List.mem_cons_self)).1)
        (hlt.subs (.keep (.refl _ _) (Scheme.subsumesUnder_refineMode_withAssumptions (by omega) Δ))
          (hs.2 _ (List.mem_map_of_mem (by simp : Constraint.sub d f ∈ _))).1)
        (hrt.subs (.keep (.refl _ _) (Scheme.subsumesUnder_refineMode_withAssumptions (by omega) Δ))
          (hs.2 _ (List.mem_map_of_mem (by simp : Constraint.sub e f ∈ _))).1)).weakening hc⟩
    exact congrArg₂ (fun x lr => Term.case x lr.1 lr.2) hex (congrArg₂ Prod.mk hel her)
  case reuse Γ Γ₁ Γ₂ Γ₃ Γ₂₃ k x y a b c d e m n cs ds es h1 h2 hk hx hy hhk hhx hhy ihk ihx ihy =>
    simp only [Solution.append] at hs
    obtain ⟨needK, hΔ, hK⟩ := ihk (h1.locksScoped hΓ).1 hs.1.1.1 hσ
    obtain ⟨needX, _, hX⟩ := ihx (h2.locksScoped (h1.locksScoped hΓ).2).1 hs.1.1.2 hσ
    obtain ⟨needY, _, hY⟩ := ihy (h2.locksScoped (h1.locksScoped hΓ).2).2 hs.1.2 hσ
    refine ⟨needK ++ needX ++ needY,
      fun _ hc => List.mem_append_left _ (List.mem_append_left _ (hΔ hc)), fun avoid havoid => ?_⟩
    obtain ⟨nK, hK⟩ := hK avoid (fun _ hc => havoid (List.mem_append_left _ (List.mem_append_left _ hc)))
    obtain ⟨nX, hX⟩ := hX avoid (fun _ hc => havoid (List.mem_append_left _ (List.mem_append_right _ hc)))
    obtain ⟨nY, hY⟩ := hY avoid (fun _ hc => havoid (List.mem_append_right _ hc))
    obtain ⟨nF, hF⟩ := Γ.substAvoid_refinementFresh_eventually σ Δ avoid
      (fun _ hc => havoid (List.mem_append_left _ (List.mem_append_left _ (hΔ hc))))
    refine ⟨nK + nX + nY + nF, fun p hp => ?_⟩
    obtain ⟨k', hek, hkt⟩ := hK p (by omega)
    obtain ⟨x', hex, hxt⟩ := hX p (by omega)
    obtain ⟨y', hey, hyt⟩ := hY p (by omega)
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      (h1.substAvoid σ avoid).declarative_refined_guarded_reuse (h2.substAvoid σ avoid)
        (hF p (by omega)) [] (by simp)
    refine ⟨.reuse k' x' y', ?_,
      (GuardedSourceTyping.reuse hj2 hj1
        (hkt.subs hl (hs.2 _ (List.mem_map_of_mem List.mem_cons_self)).1)
        (hxt.subs hm' (hs.2 _ (List.mem_map_of_mem (by simp : Constraint.sub b (.modal d m) ∈ _))).1)
        (hyt.subs hr (hs.2 _ (List.mem_map_of_mem (by simp : Constraint.sub c (.modal e m) ∈ _))).1)
        (hs.2 _ (List.mem_map_of_mem (by simp : Constraint.mode n (.const Mode.uniqueOnly) ∈ _)))
        (hs.2 _ (List.mem_map_of_mem (by simp : Constraint.mode (.compose n (.const Mode.many)) m ∈ _)))).weakening hc⟩
    exact congrArg₂ (fun k xy => Term.reuse k xy.1 xy.2) hek (congrArg₂ Prod.mk hex hey)

theorem Generates.guarded_raw_sound {Γ : Context} {t a cs Δ σ}
    (h : Generates (Γ.map ContextEntry.binding) t a cs) (hh : h.Hygienic)
    (hs : Solution cs Δ σ) (hσ : σ.WellFormedUnder Δ) :
    GuardedRawTyping Δ (Γ.subst σ) t (σ.ty a) := by
  have hΓ : AlgorithmicContext.LocksScoped (Γ.map ContextEntry.binding) := by
    clear hh h
    induction Γ <;> simp_all [AlgorithmicContext.LocksScoped]
  obtain ⟨needed, hΔ, hT⟩ := hh.guarded_typing_refined hΓ hs hσ
  obtain ⟨n, hT⟩ := hT needed (fun _ h => h)
  obtain ⟨nF, hF⟩ := AlgorithmicContext.substAvoid_refinementFresh_eventually
    (Γ.map ContextEntry.binding) σ Δ needed hΔ
  exact (hT (max n nF) (Nat.le_max_left _ _)).weakening
    (Γ.substAvoid_refined_guarded σ needed Δ (fun s hs =>
      ((hF _ (Nat.le_max_right _ _)).1 _
        (List.mem_map_of_mem (List.mem_map_of_mem hs))).1))

end ModalityInference
