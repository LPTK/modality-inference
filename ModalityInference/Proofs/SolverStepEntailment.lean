import ModalityInference.Proofs.SolverTransport

/-! Backward entailment of complete solver transitions that preserve the saved
substitution. Equality elimination is handled separately by substitution transport. -/
namespace ModalityInference

theorem SolverState.entails_head {s t : SolverState} {c rest Δ}
    (hp : s.pending = c :: rest) (hfix : s.substitution.constraint c = c)
    (hb : s.bounds ⊆ t.bounds) (hr : rest ⊆ t.pending)
    (hΔ : EntailsAll Δ (t.pending ++ t.bounds))
    (hc : Entails Δ (s.substitution.constraint c).normalize) :
    EntailsAll Δ (s.pending ++ s.bounds) := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_cons.mp (hp ▸ hd) with rfl | hd
    · exact (d.normalize_entails Δ).mp (by simpa only [hfix] using hc)
    · exact hΔ d (List.mem_append_left _ (hr hd))
  · exact hΔ d (List.mem_append_right _ (hb hd))

theorem stepType_head_entails {s t : SolverState} (hu : s.Unbound) {c rest a b Δ}
    (hp : s.pending = c :: rest) (he : (s.substitution.constraint c).normalize = .sub a b)
    (h : stepType {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen}
      a b = .success t) (hΔ : EntailsAll Δ (t.pending ++ t.bounds)) :
    EntailsAll Δ (s.pending ++ s.bounds) := by
  obtain ⟨hr, hb, _⟩ := stepType_frame h
  exact SolverState.entails_head hp ((hu.pending c (by simp [hp])).fixed hu.modes)
    hb hr hΔ (he ▸ stepType_entails h hΔ)

theorem stepMode_head_entails {s t : SolverState} (hu : s.Unbound) {c rest a b Δ}
    (hp : s.pending = c :: rest) (he : (s.substitution.constraint c).normalize = .mode a b)
    (h : stepMode {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen}
      a b = .success t) (hΔ : EntailsAll Δ (t.pending ++ t.bounds)) :
    EntailsAll Δ (s.pending ++ s.bounds) := by
  obtain ⟨hr, hb, _⟩ := stepMode_frame h
  exact SolverState.entails_head hp ((hu.pending c (by simp [hp])).fixed hu.modes)
    hb hr hΔ (he ▸ stepMode_entails h hΔ)

theorem solverStep_entails_of_same_substitution {s t : SolverState}
    (hs : s.TypeReady) (hm : s.ModeInvariant) (hu : s.Unbound)
    (hσ : s.substitution.Acyclic) (h : solverStep s = .success t)
    (heq : t.substitution = s.substitution) {Δ}
    (hΔ : EntailsAll Δ (t.pending ++ t.bounds)) : EntailsAll Δ (s.pending ++ s.bounds) := by
  simp only [solverStep, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals first
    | exact stepType_head_entails hu ‹s.pending = _ :: _› (by assumption) h hΔ
    | exact stepMode_head_entails hu ‹s.pending = _ :: _› (by assumption) h hΔ
    | skip
  all_goals cases h
  all_goals try exact hΔ
  case h_2.isFalse.isFalse.refl =>
    rename_i pending c rest hp hseen normalized a v n he hrefl hoccurs
    obtain ⟨hn, _⟩ := s.substitution.normalized_equal_fresh hσ he
    have hlen := congrArg (fun σ : Substitution => (σ.types.map Prod.fst).length) heq
    simp only [Substitution.extendType_keys _ hn, List.length_cons, Nat.succ_ne_self] at hlen
  all_goals refine (SolverState.entails_head ‹s.pending = _ :: _›
    ((hu.pending _ (by simp [‹s.pending = _ :: _›])).fixed hu.modes)
    (by first | exact List.Subset.refl _ | (simp only [SolverState.retain]; split <;> simp))
    (by simp [SolverState.emit, SolverState.retain]) hΔ ?_)
  all_goals try solve
    | rename_i pending c rest hp hseen
      have hfix := (hu.pending c (by simp [hp])).fixed hu.modes
      rw [hfix]
      exact (c.normalize_entails Δ).mpr
        (hs.duplicate_entails hm hp hfix (by simpa using hseen) hΔ)
  case h_1.refl =>
    rename_i pending c rest hp hseen normalized a b he
    rw [he]
    have hab := hΔ (.sub a b) (by simp [SolverState.emit])
    have hba := hΔ (.sub b a) (by simp [SolverState.emit])
    exact ⟨hab.1, hba.1, hab.2⟩
  case h_4.isTrue.isTrue.refl =>
    rename_i pending c rest hp hseen normalized a he hfree heval
    rw [he]
    obtain ⟨m, heval⟩ := Option.isSome_iff_exists.mp heval
    exact fun _ _ => Option.isSome_iff_exists.mpr ⟨m, a.eval_refinement (by simp) heval⟩
  case h_4.isFalse.refl =>
    rename_i pending c rest hp hseen normalized a he hfree
    exact hΔ _ (List.mem_append_right _ (s.mem_retain .defined (s.substitution.constraint c).normalize))
  case h_1.isTrue.refl | h_2.isTrue.refl =>
    rename_i pending c rest hp hseen normalized a v n he hrefl
    rw [he, beq_iff_eq.mp hrefl]
    exact ⟨.refl, .refl, by simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]⟩
  case h_2.isFalse.isTrue.refl =>
    rename_i pending c rest hp hseen normalized a v n he hrefl hoccurs
    rw [he]
    have hleft := hΔ (.sub (.var (.flex n)) a) (by simp [SolverState.emit])
    have hright := hΔ (.sub a (.var (.flex n))) (by simp [SolverState.emit])
    exact ⟨hleft.1, hright.1, hleft.2.2⟩

/-- The only successful transition changing the saved substitution eliminates
an occurs-free flexible equality and moves its guards into the pending list. -/
theorem solverStep_substitution_cases {s t : SolverState} (h : solverStep s = .success t) :
    t.substitution = s.substitution ∨ ∃ c rest n a,
      s.pending = c :: rest ∧ (s.substitution.constraint c).normalize = .equal (.flex n) a ∧
      TypeVar.flex n ∉ a.typeVars ∧ t.substitution = s.substitution.extendType n a ∧
      t.pending = ({types := [(n, a)]} : Substitution).bounds
        (rest ++ s.bounds ++ a.wellFormedBounds) ∧ t.bounds = [] := by
  simp only [solverStep, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals first
    | (have hsub := stepType_substitution h; exact Or.inl hsub)
    | (have hsub := stepMode_substitution h; exact Or.inl hsub)
    | skip
  all_goals cases h
  all_goals try exact Or.inl rfl
  rename_i pending c rest hp hseen normalized a v n he hrefl hoccurs
  exact Or.inr ⟨c, rest, n, a, hp, he, by simpa using hoccurs, rfl, rfl, rfl⟩

end ModalityInference
