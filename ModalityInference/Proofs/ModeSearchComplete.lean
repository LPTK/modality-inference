import ModalityInference.Proofs.ModeSearch
import ModalityInference.Proofs.CNFNormalization

/-! Termination and completeness of Boolean and modality consistency search. -/
namespace ModalityInference

/-- Base three pays for both children while leaving a step for the parent. -/
def CNF.searchWeight (cs : CNF) : Nat := 3 ^ cs.atoms.toFinset.card

def CNF.frontierWeight (todo : List (CNF × List (Nat × Bool))) : Nat :=
  (todo.map fun node => node.1.searchWeight).sum

theorem assignCNF_card_lt {cs v b} (hv : v ∈ cs.atoms) :
    (assignCNF cs v b).atoms.toFinset.card < cs.atoms.toFinset.card := by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨fun _ hw => List.mem_toFinset.mpr (assignCNF_atoms (List.mem_toFinset.mp hw)).1,
      fun he => (assignCNF_atoms (List.mem_toFinset.mp
        (he.symm ▸ List.mem_toFinset.mpr hv))).2 rfl⟩)

theorem assignCNF_weight {cs v b} (hv : v ∈ cs.atoms) :
    3 * (assignCNF cs v b).searchWeight ≤ cs.searchWeight := by
  simpa [CNF.searchWeight, Nat.pow_succ, Nat.mul_comm] using
    Nat.pow_le_pow_right (by decide : 0 < 3) (assignCNF_card_lt (b := b) hv)

theorem searchCNF_terminates {fuel todo} (h : CNF.frontierWeight todo < fuel) :
    searchCNF fuel todo ≠ .exhausted := by
  induction fuel generalizing todo with
  | zero => omega
  | succ fuel ih =>
    cases todo with
    | nil => simp [searchCNF]
    | cons node todo =>
      obtain ⟨cs, σ⟩ := node
      simp only [searchCNF]
      split
      · apply ih
        have hp := Nat.pow_pos (a := 3) (n := cs.atoms.toFinset.card) (by decide)
        simp only [CNF.frontierWeight, CNF.searchWeight, List.map_cons, List.sum_cons] at h ⊢
        omega
      · next hfalse =>
        split
        · simp
        · next hnonempty =>
          split
          · next v b he =>
            have hv : v ∈ cs.atoms :=
              CNF.mem_atoms.mpr ⟨[(v,b)], CNF.find_unit_mem he, b, by simp⟩
            apply ih
            have hw := And.intro (assignCNF_weight (b := b) hv)
              (Nat.pow_pos (a := 3) (n := cs.atoms.toFinset.card) (by decide))
            simp only [CNF.frontierWeight, CNF.searchWeight, List.map_cons, List.sum_cons] at h hw ⊢
            omega
          · have hv : cs.atoms.foldl min (cs.atoms.headD 0) ∈ cs.atoms :=
              CNF.minimum_mem (CNF.atoms_ne_nil (by simpa using hnonempty)
                (fun hc => hfalse (List.any_eq_true.mpr ⟨[], hc, rfl⟩)))
            apply ih
            have hw := And.intro (assignCNF_weight (b := false) hv)
              (And.intro (assignCNF_weight (b := true) hv)
                (Nat.pow_pos (a := 3) (n := cs.atoms.toFinset.card) (by decide)))
            simp only [CNF.frontierWeight, CNF.searchWeight, CNF.atoms,
              List.map_cons, List.sum_cons] at h hw ⊢
            omega

theorem searchCNF_rejected {fuel todo message}
    (h : searchCNF fuel todo = .rejected message) :
    ∀ cs σ, (cs, σ) ∈ todo → ∀ η, ¬CNFHolds η cs := by
  induction fuel generalizing todo with
  | zero => cases h
  | succ fuel ih =>
    cases todo with
    | nil => simp
    | cons node todo =>
      obtain ⟨cs, σ⟩ := node
      simp only [searchCNF] at h
      split at h
      · next he =>
        have hn : [] ∈ cs := by simpa [List.any_eq_true] using he
        simp only [List.mem_cons, Prod.mk.injEq]
        rintro ds τ (⟨rfl, rfl⟩ | hm) η hη
        · simpa [ClauseHolds] using hη [] hn
        · exact ih h ds τ hm η hη
      · split at h
        · cases h
        · split at h
          · next v b he =>
            simp only [List.mem_cons, Prod.mk.injEq]
            rintro ds τ (⟨rfl, rfl⟩ | hm) η hη
            · have hv : η v = b := by
                simpa [ClauseHolds] using hη [(v,b)] (CNF.find_unit_mem he)
              exact ih h _ ((v,b) :: τ) (by simp) η ((assignCNF_correct hv ds).mpr hη)
            · exact ih h ds τ (by simp [hm]) η hη
          · simp only [List.mem_cons, Prod.mk.injEq]
            rintro ds τ (⟨rfl, rfl⟩ | hm) η hη
            · let v := ds.atoms.foldl min (ds.atoms.headD 0)
              refine ih h (assignCNF ds v (η v)) ((v, η v) :: τ) ?_ η
                ((assignCNF_correct rfl ds).mpr hη)
              cases η v <;> simp [v, CNF.atoms]
            · exact ih h ds τ (by simp [hm]) η hη

theorem searchCNF_complete {fuel todo}
    (hf : CNF.frontierWeight todo < fuel)
    (hs : ∃ cs σ η, (cs, σ) ∈ todo ∧ CNFHolds η cs) :
    ∃ result, searchCNF fuel todo = .success result := by
  obtain ⟨cs, σ, η, hm, hη⟩ := hs
  cases h : searchCNF fuel todo with
  | success result => exact ⟨result, rfl⟩
  | rejected message => exact False.elim (searchCNF_rejected h cs σ hm η hη)
  | exhausted => exact False.elim (searchCNF_terminates hf h)

theorem satisfiableModes_complete {cs η} (hη : ModeModels cs η) :
    ∃ n, ∀ fuel ≥ n, ∃ result, satisfiableModes fuel cs = .success result := by
  obtain ⟨n, clauses, hc⟩ := toCNF_complete (boundsModeFormula cs) true
  have hm : CNFHolds (encodeModes η) clauses := by
    simpa only [toCNF_correct (hc n le_rfl), boundsModeFormula_correct,
      projectedModes_encodeModes] using hη
  refine ⟨n + clauses.searchWeight + 1, fun fuel hf => ?_⟩
  have hw : CNF.frontierWeight [(clauses, [])] < fuel := by
    simpa [CNF.frontierWeight] using (show clauses.searchWeight < fuel by omega)
  obtain ⟨σ, hs⟩ := searchCNF_complete hw ⟨clauses, [], encodeModes η, by simp, hm⟩
  simp [satisfiableModes, hc fuel (by omega), hs, bind, pure, RunResult.bind]

theorem satisfiableModes_terminates (cs : Bounds) :
    ∃ n, ∀ fuel ≥ n, satisfiableModes fuel cs ≠ .exhausted := by
  obtain ⟨n, clauses, hc⟩ := toCNF_complete (boundsModeFormula cs) true
  refine ⟨n + clauses.searchWeight + 1, fun fuel hf => ?_⟩
  have hw : CNF.frontierWeight [(clauses, [])] < fuel := by
    simpa [CNF.frontierWeight] using (show clauses.searchWeight < fuel by omega)
  have ht := searchCNF_terminates hw
  cases hs : searchCNF fuel [(clauses, [])] <;>
    simp_all [satisfiableModes, hc fuel (by omega), bind, pure, RunResult.bind]

theorem satisfiableModes_success_iff (cs : Bounds) :
    (∃ fuel result, satisfiableModes fuel cs = .success result) ↔ ∃ η, ModeModels cs η := by
  constructor
  · rintro ⟨fuel, result, h⟩
    exact ⟨result.total, satisfiableModes_sound h⟩
  · rintro ⟨η, hη⟩
    obtain ⟨n, hn⟩ := satisfiableModes_complete hη
    exact ⟨n, hn n le_rfl⟩

end ModalityInference
