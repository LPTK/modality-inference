import ModalityInference.CNFPropagation
import ModalityInference.Proofs.Backend

/-! Model preservation, reconstruction, and termination of general bound elimination. -/

namespace ModalityInference.CNFPropagation

@[simp] theorem mem_atoms {cs : CNF} {v} :
    v ∈ atoms cs ↔ ∃ c ∈ cs, ∃ b, (v, b) ∈ c := by
  simp [atoms, List.mem_flatMap, List.mem_map, Prod.exists]

@[simp] theorem mem_pivots {cs : CNF} {v} : v ∈ pivots cs ↔ v ∈ atoms cs := by
  simp [pivots]

theorem cleanCNF_atoms {cs : CNF} {v} (hv : v ∈ atoms (cleanCNF cs)) : v ∈ atoms cs := by
  obtain ⟨c, hc, b, hb⟩ := mem_atoms.mp hv
  simp only [cleanCNF, List.mem_dedup, List.mem_filter, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc.1
  exact mem_atoms.mpr ⟨d, hd, b, List.mem_dedup.mp hb⟩

theorem eliminate_atoms {cs : CNF} {v w} (hw : w ∈ atoms (eliminate cs v)) :
    w ∈ atoms cs ∧ w ≠ v := by
  have hh := cleanCNF_atoms hw
  simp [atoms, unaffected, lower, upper, without, List.mem_flatMap, List.mem_map,
    Prod.exists] at hh
  simp only [mem_atoms]
  aesop

theorem eliminate_card_lt {cs : CNF} {v} (hv : v ∈ atoms cs) :
    (atoms (eliminate cs v)).toFinset.card < (atoms cs).toFinset.card := by
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨fun _ hw => List.mem_toFinset.mpr (eliminate_atoms (List.mem_toFinset.mp hw)).1,
      fun he => (eliminate_atoms (List.mem_toFinset.mp
        (he.symm ▸ List.mem_toFinset.mpr hv))).2 rfl⟩)

theorem holds_congr {σ τ : Nat → Bool} {cs : CNF}
    (h : ∀ v ∈ atoms cs, σ v = τ v) : CNFHolds σ cs ↔ CNFHolds τ cs := by
  constructor
  all_goals intro hh c hc
  all_goals obtain ⟨v, b, hv, he⟩ := hh c hc
  all_goals exact ⟨v, b, hv, by simpa [h v (mem_atoms.mpr ⟨c, hc, b, hv⟩)] using he⟩

@[simp] theorem clauseValue_correct (σ : Nat → Bool) (c : Clause) :
    clauseValue σ c = true ↔ ClauseHolds σ c := by
  simp [clauseValue, ClauseHolds, List.any_eq_true, Prod.exists]

theorem clause_update_of_without {σ : Nat → Bool} {v b c}
    (h : ClauseHolds σ (without v c)) : ClauseHolds (Function.update σ v b) c := by
  obtain ⟨w, p, hw, he⟩ := h
  simp only [without, List.mem_filter, bne_iff_ne] at hw
  exact ⟨w, p, hw.1, by simpa [Function.update_of_ne hw.2] using he⟩

theorem clause_without_of_missing {σ : Nat → Bool} {v c}
    (h : ClauseHolds σ c) (hm : (v, σ v) ∉ c) : ClauseHolds σ (without v c) := by
  obtain ⟨w, p, hw, he⟩ := h
  have hwv : w ≠ v := by rintro rfl; exact hm (he ▸ hw)
  exact ⟨w, p, List.mem_filter.mpr ⟨hw, by simpa using hwv⟩, he⟩

theorem eliminate_preserves {σ : Nat → Bool} {cs : CNF} (v : Nat)
    (h : CNFHolds σ cs) : CNFHolds σ (eliminate cs v) := by
  rw [eliminate, cleanCNF_correct, cnfHolds_append]
  refine ⟨fun c hc => h c (List.mem_filter.mp hc).1, ?_⟩
  rintro c hc
  obtain ⟨l, hl, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc
  simp [lower, upper] at hl hu
  obtain ⟨a, ⟨ha, _, han⟩, rfl⟩ := hl
  obtain ⟨b, ⟨hb, _, hbp⟩, rfl⟩ := hu
  exact (clauseHolds_append _ _ _).mpr (by
    cases hv : σ v with
    | false => exact .inl (clause_without_of_missing (h a ha) (by simpa [hv] using han))
    | true => exact .inr (clause_without_of_missing (h b hb) (by simpa [hv] using hbp)))

theorem eliminate_reconstruct (cs : CNF) (v : Nat) (σ : Nat → Bool)
    (h : CNFHolds σ (eliminate cs v)) :
    CNFHolds (Function.update σ v (lowerJoin cs v σ)) cs := by
  rw [eliminate, cleanCNF_correct, cnfHolds_append] at h
  intro c hc
  by_cases hp : (v, true) ∈ c <;> by_cases hn : (v, false) ∈ c
  · exact ⟨v, lowerJoin cs v σ, by cases lowerJoin cs v σ <;> assumption, by simp⟩
  · by_cases hb : lowerJoin cs v σ = true
    · exact ⟨v, true, hp, by simp [hb]⟩
    · have hl : ∀ l ∈ lower cs v, ClauseHolds σ l := by
        simpa [lowerJoin, Bool.not_eq_true, Bool.eq_false_iff] using hb
      exact clause_update_of_without (hl _
        (List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simp [hp, hn]⟩, rfl⟩))
  · have hu : without v c ∈ upper cs v :=
      List.mem_map.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simp [hp, hn]⟩, rfl⟩
    by_cases hb : lowerJoin cs v σ = true
    · have hl : ∃ l ∈ lower cs v, ¬ClauseHolds σ l := by
        simpa [lowerJoin, Bool.not_eq_true, Bool.eq_false_iff] using hb
      obtain ⟨l, hl, hnoth⟩ := hl
      have huH : ClauseHolds σ (without v c) :=
        ((clauseHolds_append σ l (without v c)).mp (h.2 _
          (List.mem_flatMap.mpr ⟨l, hl, List.mem_map.mpr ⟨_, hu, rfl⟩⟩))).resolve_left hnoth
      exact clause_update_of_without huH
    · exact ⟨v, false, hn, by simp [Bool.eq_false_iff.mpr hb]⟩
  · obtain ⟨w, p, hw, he⟩ := h.1 c (List.mem_filter.mpr ⟨hc, by simp [hp, hn]⟩)
    have hwv : w ≠ v := by rintro rfl; cases p <;> contradiction
    exact ⟨w, p, hw, by simpa [Function.update_of_ne hwv] using he⟩

theorem eliminate_update (cs : CNF) (v : Nat) (σ : Nat → Bool) (b : Bool) :
    CNFHolds (Function.update σ v b) (eliminate cs v) ↔ CNFHolds σ (eliminate cs v) := by
  exact holds_congr (fun w hw => by simp [Function.update_of_ne (eliminate_atoms hw).2])

/-- Exact elimination of the pivot, together with the constructive extension above. -/
theorem eliminate_iff (cs : CNF) (v : Nat) (σ : Nat → Bool) :
    CNFHolds σ (eliminate cs v) ↔ ∃ b, CNFHolds (Function.update σ v b) cs := by
  exact ⟨fun h => ⟨lowerJoin cs v σ, eliminate_reconstruct cs v σ h⟩,
    fun ⟨b, h⟩ => (eliminate_update cs v σ b).mp (eliminate_preserves v h)⟩

@[simp] theorem valuation_cons (v : Nat) (b : Bool) (σ : Assignment) :
    valuation ((v, b) :: σ) = Function.update (valuation σ) v b := by
  funext w
  by_cases hw : w = v
  · simp [valuation, Function.update_apply, hw]
  · have he : (w == v) = false := by simpa using hw
    simp [valuation, List.lookup_cons, Function.update_of_ne hw, he]

theorem run_sound {fuel vs cs result}
    (hdom : ∀ v ∈ atoms cs, v ∈ vs)
    (h : run fuel vs cs = .success result) : CNFHolds (valuation result) cs := by
  induction fuel generalizing vs cs result with
  | zero => cases h
  | succ fuel ih =>
    simp only [run] at h
    split at h
    · contradiction
    · rename_i hempty
      cases vs with
      | nil =>
        intro c hc
        cases c with
        | nil => exact False.elim (hempty (List.any_eq_true.mpr ⟨[], hc, rfl⟩))
        | cons lit c => exact False.elim (List.not_mem_nil
            (hdom lit.1 (mem_atoms.mpr ⟨lit :: c, hc, lit.2, by simp⟩)))
      | cons v vs =>
        dsimp only at h
        split at h
        · contradiction
        · cases hr : run fuel vs (eliminate cs v) <;> simp [hr, bind, pure, RunResult.bind] at h
          subst result
          simpa only [valuation_cons] using eliminate_reconstruct cs v _
            (ih (fun w hw => (List.mem_cons.mp (hdom w (eliminate_atoms hw).1)).resolve_left
              (eliminate_atoms hw).2) hr)

theorem solve_sound {fuel cs result} (h : solve fuel cs = .success result) :
    CNFHolds (valuation result) cs :=
  run_sound (fun _ hv => mem_pivots.mpr hv) h

theorem models_no_empty {σ : Nat → Bool} {cs : CNF} (h : CNFHolds σ cs) :
    cs.any List.isEmpty = false := by
  simp only [Bool.eq_false_iff]
  intro hh
  obtain ⟨c, hc, he⟩ := List.any_eq_true.mp hh
  cases c with
  | nil => simpa [ClauseHolds] using h _ hc
  | cons => cases he

theorem run_not_rejected {cs : CNF} {σ : Nat → Bool} (hmodel : CNFHolds σ cs)
    (fuel : Nat) (vs : List Nat) (message : String) : run fuel vs cs ≠ .rejected message := by
  induction fuel generalizing cs vs with
  | zero => simp [run]
  | succ fuel ih =>
    cases vs with
    | nil => simp [run, models_no_empty hmodel]
    | cons v vs =>
      simp only [run, models_no_empty hmodel, Bool.false_eq_true, ↓reduceIte]
      split
      · simp
      · cases hr : run fuel vs (eliminate cs v) <;> simp [bind, pure, RunResult.bind]
        simpa [hr] using ih (eliminate_preserves v hmodel) vs

theorem run_terminates (vs : List Nat) (cs : CNF) :
    ∃ n, ∀ fuel ≥ n, run fuel vs cs ≠ .exhausted := by
  induction vs generalizing cs with
  | nil =>
    refine ⟨1, ?_⟩
    rintro (_ | fuel) hf
    · omega
    · simp only [run]
      split <;> simp
  | cons v vs ih =>
    obtain ⟨n, hn⟩ := ih (eliminate cs v)
    refine ⟨max (crossSize cs v) (n + 1), ?_⟩
    rintro (_ | fuel) hf
    · omega
    · have hh := hn fuel (by omega)
      cases hr : run fuel vs (eliminate cs v) <;>
        simp_all [run, show ¬crossSize cs v > fuel + 1 by omega, bind, pure, RunResult.bind]
      all_goals split <;> simp

theorem solve_terminates (cs : CNF) : ∃ n, ∀ fuel ≥ n, solve fuel cs ≠ .exhausted :=
  run_terminates (pivots cs) cs

theorem solve_not_rejected {cs : CNF} {σ : Nat → Bool} (hmodel : CNFHolds σ cs)
    (fuel : Nat) (message : String) : solve fuel cs ≠ .rejected message :=
  run_not_rejected hmodel fuel (pivots cs) message

theorem solve_complete {cs : CNF} {σ : Nat → Bool} (hmodel : CNFHolds σ cs) :
    ∃ n, ∀ fuel ≥ n, ∃ result, solve fuel cs = .success result := by
  obtain ⟨n, hn⟩ := solve_terminates cs
  refine ⟨n, fun fuel hf => ?_⟩
  cases hr : solve fuel cs with
  | success result => exact ⟨result, rfl⟩
  | rejected message => exact False.elim (solve_not_rejected hmodel fuel message hr)
  | exhausted => exact False.elim (hn fuel hf hr)

theorem run_stable {n vs cs r} (hne : r ≠ .exhausted) (hr : run n vs cs = r) :
    ∀ fuel ≥ n, run fuel vs cs = r := by
  induction n generalizing vs cs r with
  | zero => exact False.elim (hne hr.symm)
  | succ n ih =>
    rintro (_ | fuel) hf
    · omega
    · simp only [run] at hr ⊢
      by_cases he : cs.any List.isEmpty = true
      · simpa only [he, ↓reduceIte] using hr
      · simp only [he, Bool.false_eq_true, ↓reduceIte] at hr ⊢
        cases vs with
        | nil => exact hr
        | cons v vs =>
          dsimp only at hr ⊢
          split at hr
          · exact False.elim (hne hr.symm)
          · rename_i hsize
            simp only [show ¬crossSize cs v > fuel + 1 by omega, ↓reduceIte]
            have hsne : run n vs (eliminate cs v) ≠ .exhausted := fun hs =>
              hne (by simpa [hs, bind, RunResult.bind] using hr.symm)
            simpa only [ih hsne rfl fuel (by omega)] using hr

theorem solve_stable {n cs r} (hne : r ≠ .exhausted) (hr : solve n cs = r) :
    ∀ fuel ≥ n, solve fuel cs = r := run_stable hne hr

theorem solve_monotone {n cs result} (h : solve n cs = .success result) :
    ∀ fuel ≥ n, solve fuel cs = .success result := solve_stable (by simp) h

end ModalityInference.CNFPropagation
