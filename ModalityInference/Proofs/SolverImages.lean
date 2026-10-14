import ModalityInference.Proofs.SolverStepEntailment
import ModalityInference.Proofs.TypeElimination

/-! Definedness of accumulated type images, conditional on the remaining work. -/
namespace ModalityInference

structure SolverState.ImagesInvariant (s : SolverState) : Prop where
  images : ∀ Δ, EntailsAll Δ (s.pending ++ s.bounds) →
    ∀ v, (s.substitution.type v).DefinedUnder Δ

theorem SolverState.ImagesInvariant.backward {s t : SolverState} (hs : s.ImagesInvariant)
    (hσ : t.substitution = s.substitution)
    (hc : ∀ Δ, EntailsAll Δ (t.pending ++ t.bounds) → EntailsAll Δ (s.pending ++ s.bounds)) :
    t.ImagesInvariant := ⟨fun Δ hΔ v => hσ ▸ hs.images Δ (hc Δ hΔ) v⟩

theorem Substitution.singleType_images_defined {n Δ} {a : Ty} (ha : a.DefinedUnder Δ) :
    ∀ v, (({types := [(n, a)]} : Substitution).type v).DefinedUnder Δ := by
  intro v
  cases v with
  | rigid k => simp [Substitution.type, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]
  | flex k =>
    by_cases hk : k = n
    · subst k; simpa [Substitution.type] using ha
    · have hkn : (k == n) = false := by simpa using hk
      simp [Substitution.type, List.lookup_cons, hkn, TypeExpr.DefinedUnder,
        TypeExpr.wellFormedBounds, ModeModels]

theorem SolverState.ImagesInvariant.eliminate {s t : SolverState} (hs : s.ImagesInvariant)
    (hu : s.Unbound) {c rest n a} (hp : s.pending = c :: rest)
    (he : (s.substitution.constraint c).normalize = .equal (.flex n) a)
    (hn : TypeVar.flex n ∉ a.typeVars) (hk : n ∉ s.substitution.types.map Prod.fst)
    (hσ : t.substitution = s.substitution.extendType n a)
    (ht : t.pending = ({types := [(n, a)]} : Substitution).bounds
      (rest ++ s.bounds ++ a.wellFormedBounds)) (hb : t.bounds = []) : t.ImagesInvariant := by
  refine ⟨fun Δ hΔ v => ?_⟩
  let one : Substitution := {types := [(n, a)]}
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
  have himage : Entails Δ (one.constraint (.sub (s.substitution.type v) (s.substitution.type v))) :=
    Entails.consequence_substitute_types
      (fun Γ hΓ => ⟨.refl, hs.images Γ hΓ v, hs.images Γ hΓ v⟩) rfl hinput
      (fun w _ => Substitution.singleType_images_defined ha w)
  rw [hσ, Substitution.extendType_type hk]
  exact himage.2.1

theorem solverStep_imagesInvariant {s t : SolverState} (hi : s.ImagesInvariant)
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound)
    (hσ : s.substitution.Acyclic) (h : solverStep s = .success t) : t.ImagesInvariant := by
  rcases solverStep_substitution_cases h with heq | ⟨c, rest, n, a, hp, he, hn, hsub, ht, hb⟩
  · exact hi.backward heq fun _ hΔ => solverStep_entails_of_same_substitution hs hm hu hσ h heq hΔ
  · exact hi.eliminate hu hp he hn (s.substitution.normalized_equal_fresh hσ he).1 hsub ht hb

theorem SolverState.ImagesInvariant.empty {s : SolverState} (hσ : s.substitution = {}) :
    s.ImagesInvariant := by
  refine ⟨fun Δ _ v => ?_⟩
  rw [hσ]
  cases v <;> simp [Substitution.type, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

theorem runWorklist_imagesInvariant {fuel s t} (hi : s.ImagesInvariant)
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (hσ : s.substitution.Acyclic) (h : runWorklist fuel s = .success t) : t.ImagesInvariant := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · exact RunResult.success.inj h ▸ hi
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_imagesInvariant hi hs hm hu hσ ht)
        (solverStep_typeReady hs hm hu hf hσ ht) (solverStep_modeInvariant hm ht)
        (solverStep_unbound hu hf hσ ht) (solverStep_fresh hf ht) (solverStep_acyclic hσ ht) h

theorem runSolver_imagesInvariant {fuel s t} (hi : s.ImagesInvariant)
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound) (hf : s.Fresh)
    (h : runSolver fuel s = .success t) : t.ImagesInvariant :=
  runWorklist_imagesInvariant hi hs hm hu hf (runSolver_input_acyclic h) (runSolver_worklist h)

theorem SolverState.DefinedInvariant.bounds_entails {s : SolverState} (hs : s.DefinedInvariant)
    (hp : s.pending = []) (hr : Residual s.bounds) : EntailsAll s.bounds s.bounds := by
  intro c hc
  have hrc := (List.forall_iff_forall_mem.mp hr) c hc
  cases c with
  | sub a b =>
    exact ⟨.bound hc,
      fun η hη => (hs.bounds η hη (by simp [hp, DefinedConstraints]) a b hc).1,
      fun η hη => (hs.bounds η hη (by simp [hp, DefinedConstraints]) a b hc).2⟩
  | mode a b => exact .valid fun _ hη => hη (.mode a b) hc
  | defined a => exact fun _ hη => hη (.defined a) hc
  | equal v a => exact False.elim hrc
  | equiv a b => exact False.elim hrc

theorem solveFrom_images_defined {fuel nt nm cs result} (hc : cs.Bounded nt nm)
    (h : solveFrom fuel nt nm cs = .success result) :
    ∀ v, (result.substitution.type v).DefinedUnder result.bounds := by
  unfold solveFrom at h
  cases hr : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hr, bind, RunResult.bind] at h
  split at h <;> cases h
  have hi := runSolver_imagesInvariant (s := {pending := cs, nextType := nt, nextMode := nm})
    (SolverState.ImagesInvariant.empty rfl) (Or.inl (SolverState.TypeInvariant.empty rfl))
    ⟨rfl, by simp⟩ ⟨rfl, fun c _ => c.unbound_empty, by simp, by simp⟩
    ⟨hc, Bounds.bounded_nil _ _, Bounds.bounded_nil _ _, Substitution.bounded_empty _ _⟩ hr
  obtain ⟨hd, hp⟩ := runSolver_definedInvariant ⟨rfl, by simp [DefinedConstraints], by simp⟩ hr
  have hres := runSolver_residual (s := {pending := cs, nextType := nt, nextMode := nm}) (by trivial) hr
  exact hi.images _ (by
    simpa only [hp, List.nil_append] using hd.bounds_entails hp hres)

theorem solve_images_defined {fuel cs result} (h : solve fuel cs = .success result) :
    ∀ v, (result.substitution.type v).DefinedUnder result.bounds :=
  solveFrom_images_defined cs.bounded_freshIndices h

/-- The solver returns a substitution satisfying inference's well-formed-image
convention. Its modality variables remain symbolic. -/
theorem solveFrom_substitution_wellFormed {fuel nt nm cs result} (hc : cs.Bounded nt nm)
    (h : solveFrom fuel nt nm cs = .success result) :
    result.substitution.WellFormedUnder result.bounds :=
  ⟨solveFrom_images_defined hc h, fun v η _ => by
    simp [Substitution.mode_eq_var (solveFrom_unbound hc h).1, ModExpr.WellFormed, ModExpr.eval]⟩

theorem solve_substitution_wellFormed {fuel cs result} (h : solve fuel cs = .success result) :
    result.substitution.WellFormedUnder result.bounds :=
  solveFrom_substitution_wellFormed cs.bounded_freshIndices h

end ModalityInference
