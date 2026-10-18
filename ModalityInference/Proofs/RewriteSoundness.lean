import ModalityInference.Proofs.ShapeExpansion
import ModalityInference.Proofs.RewriteScope

namespace ModalityInference.Deferred

private theorem ground_typeGuards {ρ c} (h : GroundSatisfies ρ c) :
    GroundModels ρ c.typeGuards := by
  intro d hd
  apply Constraint.assumptions_ground h d
  cases c <;> simp_all [Constraint.typeGuards, Constraint.assumptions]

theorem Rewrites.configModels {s t scope} (h : Rewrites s t)
    (ht : scope.types ⊆ s.typeVars) (hm : scope.modes ⊆ s.modVars) (ρ) :
    ConfigModels scope s ρ ↔ ConfigModels scope t ρ := by
  cases h
  case substitute n t s hn hk => exact ConfigModels.substitute hn hk
  case expandLeft v t shape m n s hs hf =>
    apply ConfigModels.expand hf (by simp [Constraint.typeVars, TypeExpr.typeVars])
      (by simpa only [RewriteConfig.typeVars_pending_cons] using ht)
      (by simpa only [RewriteConfig.modVars_pending_cons] using hm)
    intro η hmodel
    obtain ⟨a, b, ha, hb, hab⟩ := hmodel
    simp only [TypeExpr.realize, bind, pure, Option.bind_some, Option.bind_eq_some_iff,
      Option.some.injEq] at ha hb
    obtain ⟨m', _, rfl⟩ := ha
    obtain ⟨ground, hg, n', _, rfl⟩ := hb
    exact hs.realize_fresh hg (by simpa using (GroundOrder.of_subtype hab).head)
  case expandRight v t shape m n s hs hf =>
    apply ConfigModels.expand hf (by simp [Constraint.typeVars, TypeExpr.typeVars])
      (by simpa only [RewriteConfig.typeVars_pending_cons] using ht)
      (by simpa only [RewriteConfig.modVars_pending_cons] using hm)
    intro η hmodel
    obtain ⟨a, b, ha, hb, hab⟩ := hmodel
    simp only [TypeExpr.realize, bind, pure, Option.bind_some, Option.bind_eq_some_iff,
      Option.some.injEq] at ha hb
    obtain ⟨ground, hg, m', _, rfl⟩ := ha
    obtain ⟨n', _, rfl⟩ := hb
    exact hs.realize_fresh hg (by simpa using (GroundOrder.of_subtype hab).head.symm)
  case equivalence cs ds s he =>
    apply ConfigModels.congr
    · rfl
    intro η
    simpa only [RewriteConfig.constraints, GroundModels, List.mem_append, or_imp, forall_and] using
      and_congr (and_congr (GroundModels.entailment_equivalence he η)
        (Iff.rfl (a := GroundModels η s.pending))) (Iff.rfl (a := GroundModels η s.bounds))
  case reduce cs ds s hr =>
    apply ConfigModels.congr
    · rfl
    intro η
    simpa only [RewriteConfig.constraints, GroundModels, List.mem_append, or_imp, forall_and] using
      and_congr (and_congr (hr.groundModels (ρ := η))
        (Iff.rfl (a := GroundModels η s.pending))) (Iff.rfl (a := GroundModels η s.bounds))
  case record c s hr hc =>
    apply ConfigModels.congr
    · rfl
    intro η
    change GroundModels η (c :: s.constraints) ↔
      GroundModels η ((c.typeGuards ++ s.pending) ++ c :: s.bounds)
    simp only [GroundModels, RewriteConfig.constraints, List.mem_cons, List.mem_append,
      or_imp, forall_and, forall_eq]
    exact ⟨fun h => ⟨⟨ground_typeGuards h.1, h.2.1⟩, h.1, h.2.2⟩,
      fun h => ⟨h.2.1, h.1.2, h.2.2⟩⟩
  case discharge c hc =>
    exact ConfigModels.redundant fun η hη => hc.groundSatisfies
      (fun d hd => hη d (List.mem_append_right _ hd))
  case hyp c s hr hc =>
    apply ConfigModels.congr
    · rfl
    intro η
    simp only [GroundModels, RewriteConfig.constraints, List.mem_cons, List.mem_append,
      or_imp, forall_and, forall_eq]
    exact ⟨fun h => ⟨⟨ground_typeGuards h.1.1, h.1.2⟩, h.2⟩,
      fun h => ⟨⟨h.2 c hc, h.1.2⟩, h.2⟩⟩
  case propagate a b c hab hbc hf =>
    apply Iff.symm
    apply ConfigModels.redundant
    intro η hη
    obtain ⟨x, y, hx, hy, hxy⟩ := hη (.mode a b) (List.mem_append_right _ hab)
    obtain ⟨y', z, hy', hz, hyz⟩ := hη (.mode b c) (List.mem_append_right _ hbc)
    have he := Option.some.inj (hy.symm.trans hy')
    subst y'
    exact ⟨x, z, hx, hz, Mode.le_trans hxy hyz⟩
  case permute cs ds s hp =>
    apply ConfigModels.congr
    · rfl
    intro η
    have hh : GroundModels η cs ↔ GroundModels η ds :=
      ⟨fun h c hc => h c (hp.mem_iff.mpr hc), fun h c hc => h c (hp.mem_iff.mp hc)⟩
    simpa only [RewriteConfig.constraints, GroundModels, List.mem_append, or_imp, forall_and] using
      and_congr hh (Iff.rfl (a := GroundModels η s.bounds))

end ModalityInference.Deferred
