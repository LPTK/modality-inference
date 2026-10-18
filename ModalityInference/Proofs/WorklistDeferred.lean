import ModalityInference.Proofs.SolverSoundness
import ModalityInference.Proofs.SolverCounters

namespace ModalityInference.WorklistCorrespondence

def config (s : SolverState) (deferred : Bounds) : RewriteConfig :=
  ⟨s.pending ++ deferred, s.bounds, s.substitution⟩

structure Deferred (s : SolverState) (cs : Bounds) : Prop where
  bounded : cs.Bounded s.nextType s.nextMode
  entails : ∀ Δ, EntailsAll Δ (s.pending ++ s.bounds) → EntailsAll Δ cs

theorem Deferred.empty (s : SolverState) : Deferred s [] :=
  ⟨Bounds.bounded_nil _ _, by simp [EntailsAll]⟩

theorem Deferred.same {s t : SolverState} {cs : Bounds} (hd : Deferred s cs)
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound)
    (hσ : s.substitution.Acyclic) (h : solverStep s = .success t)
    (he : t.substitution = s.substitution) : Deferred t cs :=
  ⟨hd.bounded.mono (solverStep_counters h).1 (solverStep_counters h).2,
   fun Δ hΔ => hd.entails Δ (solverStep_entails_of_same_substitution hs hm hu hσ h he hΔ)⟩

theorem Deferred.eliminate {s t : SolverState} {cs : Bounds} (hd : Deferred s cs)
    (hu : s.Unbound) (hf : s.Fresh) {c rest n a}
    (hp : s.pending = c :: rest)
    (he : (s.substitution.constraint c).normalize = .equal (.flex n) a)
    (hn : TypeVar.flex n ∉ a.typeVars)
    (ht : t.pending = ({types := [(n, a)]} : Substitution).bounds
      (rest ++ s.bounds ++ a.wellFormedBounds)) (hb : t.bounds = [])
    (hct : s.nextType ≤ t.nextType) (hcm : s.nextMode ≤ t.nextMode) :
    Deferred t (({types := [(n, a)]} : Substitution).bounds cs) := by
  let one : Substitution := {types := [(n, a)]}
  have haBound : n < s.nextType ∧ a.Bounded s.nextType s.nextMode := by
    simpa only [he, Constraint.Bounded, TypeVar.index] using hf.normalized_head hp
  refine ⟨((Substitution.bounded_singleType haBound.1 haBound.2).bounds hd.bounded).mono hct hcm, ?_⟩
  intro Δ hΔ
  have hnew : EntailsAll Δ (one.bounds (rest ++ s.bounds)) ∧
      EntailsAll Δ (one.bounds a.wellFormedBounds) := by
    simpa only [ht, hb, List.append_nil, Substitution.bounds, List.map_append,
      EntailsAll, List.mem_append, or_imp, forall_and] using hΔ
  have ha : a.DefinedUnder Δ := (a.definedUnder_iff_entails_wellFormed Δ).mpr (by
    simpa only [one.wellFormedBounds_fixed rfl] using hnew.2)
  have hec : c.normalize = .equal (.flex n) a := by
    simpa only [(hu.pending c (by simp [hp])).fixed hu.modes] using he
  have hinput : EntailsAll Δ (one.bounds (s.pending ++ s.bounds)) := by
    rw [hp]
    change EntailsAll Δ (one.constraint c :: one.bounds (rest ++ s.bounds))
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · apply (c.normalize_substitute_entails Δ (σ := one) rfl).mp
      rw [hec]
      exact Substitution.singleType_equal_entails hn ha
    · exact hnew.1 d hd
  rintro d hmem
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmem
  exact Entails.consequence_substitute_types (fun Γ hΓ => hd.entails Γ hΓ e he) rfl hinput
    (fun v _ => Substitution.singleType_images_defined ha v)

end ModalityInference.WorklistCorrespondence

namespace ModalityInference.WorklistCorrespondence

theorem single {s t : RewriteConfig} (h : Rewrites s t) : RewriteStar s t :=
  .step h .refl

theorem trans {s t u : RewriteConfig} (h : RewriteStar s t) (ht : RewriteStar t u) :
    RewriteStar s u := by
  induction h with
  | refl => exact ht
  | step h _ ih => exact .step h (ih ht)

theorem equivalent {cs ds : Bounds} (h : ∀ Δ, EntailsAll Δ cs ↔ EntailsAll Δ ds)
    (s : RewriteConfig) :
    RewriteStar {s with pending := cs ++ s.pending} {s with pending := ds ++ s.pending} :=
  single (.equivalence h)

theorem normalize (c : Constraint) (s : RewriteConfig) :
    RewriteStar {s with pending := c :: s.pending}
      {s with pending := c.normalize :: s.pending} := by
  apply equivalent (cs := [c]) (ds := [c.normalize])
  intro Δ
  simpa only [EntailsAll, List.mem_singleton, forall_eq] using (c.normalize_entails Δ).symm

theorem permute {cs ds : Bounds} (h : cs.Perm ds) (s : RewriteConfig) :
    RewriteStar {s with pending := cs} {s with pending := ds} := single (.permute h)

theorem substitute_deferred {s : SolverState} {c : Constraint} {rest cs : Bounds}
    {n : Nat} {a : Ty} (hu : s.Unbound) (hσ : s.substitution.Acyclic)
    (hp : s.pending = c :: rest)
    (he : (s.substitution.constraint c).normalize = .equal (.flex n) a)
    (hn : TypeVar.flex n ∉ a.typeVars) :
    RewriteStar (config s cs)
      ⟨({types := [(n, a)]} : Substitution).bounds
          (rest ++ s.bounds ++ a.wellFormedBounds) ++
        ({types := [(n, a)]} : Substitution).bounds cs,
        [], s.substitution.extendType n a⟩ := by
  have hec : c.normalize = .equal (.flex n) a := by
    simpa only [(hu.pending c (by simp [hp])).fixed hu.modes] using he
  have hk := (s.substitution.normalized_equal_fresh hσ he).1
  have hnorm := normalize c (⟨rest ++ cs, s.bounds, s.substitution⟩ : RewriteConfig)
  have hstep := Rewrites.substitute (s := ⟨rest ++ cs, s.bounds, s.substitution⟩) hn hk
  refine trans (by simpa only [config, hp, List.cons_append, hec] using hnorm)
    (trans (single hstep) ?_)
  apply permute (s := ⟨[], [], s.substitution.extendType n a⟩)
  simp only [RewriteConfig.constraints, Substitution.bounds, List.map_append]
  simpa only [Substitution.bounds, List.map_append, List.append_assoc] using
    (List.Perm.append_left
      (({types := [(n, a)]} : Substitution).bounds rest)
      (List.perm_append_comm
        (l₁ := ({types := [(n, a)]} : Substitution).bounds cs)
        (l₂ := ({types := [(n, a)]} : Substitution).bounds (s.bounds ++ a.wellFormedBounds))))

end ModalityInference.WorklistCorrespondence
