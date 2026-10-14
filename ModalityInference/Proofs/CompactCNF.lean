import ModalityInference.CompactCNF
import ModalityInference.Proofs.Backend

namespace ModalityInference.CompactCNF

@[simp] theorem mem_canonical (literal : Literal) (clause : Clause) :
    literal ∈ canonical clause ↔ literal ∈ clause := by
  simp [canonical]

theorem canonical_correct (σ : Nat → Bool) (clause : Clause) :
    ClauseHolds σ (canonical clause) ↔ ClauseHolds σ clause := by
  simp [ClauseHolds]

theorem subsumes_iff (a b : Clause) :
    subsumes a b = true ↔ ∀ literal ∈ a, literal ∈ b := by
  simp [subsumes, List.all_eq_true]

theorem subsumes_holds {a b : Clause} (h : subsumes a b = true)
    {σ : Nat → Bool} (ha : ClauseHolds σ a) : ClauseHolds σ b := by
  obtain ⟨v, p, hm, hv⟩ := ha
  exact ⟨v, p, (subsumes_iff a b).mp h _ hm, hv⟩

theorem insert_correct (σ : Nat → Bool) (clause : Clause) (clauses : CNF) :
    CNFHolds σ (insert clause clauses) ↔ ClauseHolds σ clause ∧ CNFHolds σ clauses := by
  unfold insert
  split
  case isTrue h => simp [clauseTautology_correct h σ]
  case isFalse ht =>
    split
    case isTrue h =>
      obtain ⟨old, hm, hs⟩ := List.any_eq_true.mp h
      exact ⟨fun hh => ⟨subsumes_holds hs (hh old hm), hh⟩, And.right⟩
    case isFalse h =>
      simp only [CNFHolds, List.mem_cons, List.mem_filter,
        forall_eq_or_imp, and_imp]
      refine ⟨?_, fun hh => ⟨hh.1, fun c hc _ => hh.2 c hc⟩⟩
      rintro ⟨hc, hcs⟩
      refine ⟨hc, fun old hm => ?_⟩
      exact if hs : subsumes clause old = true then subsumes_holds hs hc
        else hcs old hm (by simpa using hs)


theorem clean_correct (σ : Nat → Bool) (clauses : CNF) :
    CNFHolds σ (clean clauses) ↔ CNFHolds σ clauses := by
  induction clauses with
  | nil => rfl
  | cons c cs ih =>
    rw [clean, insert_correct, canonical_correct, ih]
    simp [CNFHolds]

theorem mem_insert {clause candidate : Clause} {clauses : CNF}
    (h : candidate ∈ insert clause clauses) : candidate = clause ∨ candidate ∈ clauses := by
  unfold insert at h
  repeat' split at h <;> simp_all
  exact h.imp id And.left


theorem clean_literal {literal : Literal} {clause : Clause} {clauses : CNF}
    (hc : clause ∈ clean clauses) (hl : literal ∈ clause) :
    ∃ original ∈ clauses, literal ∈ original := by
  induction clauses with
  | nil => cases hc
  | cons c cs ih =>
    rcases mem_insert hc with rfl | hm
    · exact ⟨c, .head _, (mem_canonical literal c).mp hl⟩
    · obtain ⟨original, ho, hl⟩ := ih hm
      exact ⟨original, .tail _ ho, hl⟩


/-- Clause minimization never introduces an atom. -/
theorem clean_atoms {v : Nat} {clauses : CNF}
    (h : v ∈ (clean clauses).flatMap (List.map Prod.fst)) :
    v ∈ clauses.flatMap (List.map Prod.fst) := by
  simp only [List.mem_flatMap, List.mem_map, Prod.exists] at h ⊢
  obtain ⟨c, hc, w, p, hl, rfl⟩ := h
  obtain ⟨original, ho, hl⟩ := clean_literal hc hl
  exact ⟨original, ho, w, p, hl, rfl⟩

theorem cnfOr_correct {limit a b cs} (h : cnfOr limit a b = .success cs)
    (σ : Nat → Bool) : CNFHolds σ cs ↔ CNFHolds σ a ∨ CNFHolds σ b := by
  unfold cnfOr at h
  split at h <;> simp at h
  rw [← h, clean_correct]
  simp [CNFHolds]
  constructor
  · intro hc
    by_cases ha : CNFHolds σ a
    · exact .inl ha
    · obtain ⟨x, hx, hbad⟩ : ∃ x ∈ a, ¬ClauseHolds σ x := by
        simpa only [CNFHolds, not_forall, exists_prop] using ha
      exact .inr fun y hy => (clauseHolds_append σ x y).mp (hc _ x hx y hy rfl) |>.resolve_left hbad
  · rintro (ha | hb) c x hx y hy rfl
    · exact (clauseHolds_append σ x y).mpr (.inl (ha x hx))
    · exact (clauseHolds_append σ x y).mpr (.inr (hb y hy))


theorem toCNF_correct {fuel positive e cs} (h : toCNF fuel positive e = .success cs)
    (σ : Nat → Bool) : CNFHolds σ cs ↔ e.eval σ = positive := by
  induction fuel generalizing positive e cs with
  | zero => simp [toCNF] at h
  | succ fuel ih =>
    cases e with
    | const b =>
      cases b <;> cases positive <;> simp [toCNF] at h <;> cases h <;>
        simp [CNFHolds, ClauseHolds, BoolExpr.eval]
    | atom n =>
      simp [toCNF] at h
      cases h
      simp [CNFHolds, ClauseHolds, BoolExpr.eval]
    | and a b =>
      cases hx : toCNF fuel positive a <;>
        simp [toCNF, hx, bind, pure, RunResult.bind] at h
      cases hy : toCNF fuel positive b <;> simp [hy] at h
      cases positive <;> simp at h
      · simp only [cnfOr_correct h, ih hx, ih hy, BoolExpr.eval, Bool.and_eq_false_iff]
      · rw [← h, clean_correct, cnfHolds_append, ih hx, ih hy]
        simp [BoolExpr.eval]
    | or a b =>
      cases hx : toCNF fuel positive a <;>
        simp [toCNF, hx, bind, pure, RunResult.bind] at h
      cases hy : toCNF fuel positive b <;> simp [hy] at h
      cases positive <;> simp at h
      · simp only [← h, clean_correct, cnfHolds_append, ih hx, ih hy,
          BoolExpr.eval, Bool.or_eq_false_iff]
      · simp [cnfOr_correct h, ih hx, ih hy, BoolExpr.eval]
    | imp a b =>
      cases hx : toCNF fuel (!positive) a <;>
        simp [toCNF, hx, bind, pure, RunResult.bind] at h
      cases hy : toCNF fuel positive b <;> simp [hy] at h
      cases positive <;> simp at h hx
      · simp [← h, clean_correct, cnfHolds_append, ih hx, ih hy, BoolExpr.eval]
      · simp [cnfOr_correct h, ih hx, ih hy, BoolExpr.eval]


theorem cnfOr_monotone {n a b cs} (h : cnfOr n a b = .success cs) :
    ∀ fuel ≥ n, cnfOr fuel a b = .success cs := by
  intro fuel hf
  simp only [cnfOr] at h ⊢
  split at h
  · contradiction
  · split
    · omega
    · exact h


theorem toCNF_monotone {n positive e cs} (h : toCNF n positive e = .success cs) :
    ∀ fuel ≥ n, toCNF fuel positive e = .success cs := by
  induction n generalizing positive e cs
  case zero => cases h
  case succ n ih =>
    rintro (_ | fuel) hFuel
    · omega
    have step (p e cs) (hs : toCNF n p e = .success cs) :
        toCNF fuel p e = .success cs := ih hs fuel (Nat.le_of_succ_le_succ hFuel)
    cases e
    all_goals simp only [toCNF, bind, pure, RunResult.bind] at h ⊢
    all_goals repeat' (split at h <;> try contradiction)
    all_goals simp_all
    all_goals exact cnfOr_monotone h _ (by omega)


/-- Normalization eventually returns the same clauses for every larger budget,
including the intermediate Cartesian-product size check. -/
theorem toCNF_complete (e : BoolExpr) (positive : Bool) :
    ∃ n cs, ∀ fuel ≥ n, toCNF fuel positive e = .success cs := by
  induction e generalizing positive with
  | const b => exact ⟨1, if b == positive then [] else [[]],
      fun fuel hf => by cases fuel <;> simp_all [toCNF]⟩
  | atom v => exact ⟨1, [[(v,positive)]],
      fun fuel hf => by cases fuel <;> simp_all [toCNF]⟩
  | and a b ia ib =>
    obtain ⟨na, ca, ha⟩ := ia positive
    obtain ⟨nb, cb, hb⟩ := ib positive
    refine ⟨na + nb + ca.length * cb.length + 1,
      if positive then clean (ca ++ cb)
        else clean (ca.flatMap fun x => cb.map (x ++ ·)), ?_⟩
    rintro (_ | fuel) hf
    · omega
    · cases positive <;> simp [toCNF, ha fuel (by omega), hb fuel (by omega),
        bind, pure, RunResult.bind, cnfOr, show ¬ca.length * cb.length > fuel + 1 by omega]
  | or a b ia ib =>
    obtain ⟨na, ca, ha⟩ := ia positive
    obtain ⟨nb, cb, hb⟩ := ib positive
    refine ⟨na + nb + ca.length * cb.length + 1,
      if positive then clean (ca.flatMap fun x => cb.map (x ++ ·))
        else clean (ca ++ cb), ?_⟩
    rintro (_ | fuel) hf
    · omega
    · cases positive <;> simp [toCNF, ha fuel (by omega), hb fuel (by omega),
        bind, pure, RunResult.bind, cnfOr, show ¬ca.length * cb.length > fuel + 1 by omega]
  | imp a b ia ib =>
    obtain ⟨na, ca, ha⟩ := ia (!positive)
    obtain ⟨nb, cb, hb⟩ := ib positive
    refine ⟨na + nb + ca.length * cb.length + 1,
      if positive then clean (ca.flatMap fun x => cb.map (x ++ ·))
        else clean (ca ++ cb), ?_⟩
    rintro (_ | fuel) hf
    · omega
    · cases positive <;> simp only [Bool.not_true, Bool.not_false] at ha <;>
        simp [toCNF, ha fuel (by omega), hb fuel (by omega),
        bind, pure, RunResult.bind, cnfOr, show ¬ca.length * cb.length > fuel + 1 by omega]


theorem cnfOr_literal {limit : Nat} {a b cs : CNF} {clause : Clause} {literal : Literal}
    (h : cnfOr limit a b = .success cs) (hc : clause ∈ cs) (hl : literal ∈ clause) :
    (∃ original ∈ a, literal ∈ original) ∨ (∃ original ∈ b, literal ∈ original) := by
  unfold cnfOr at h
  split at h <;> simp at h
  subst cs
  obtain ⟨original, ho, hl⟩ := clean_literal hc hl
  simp only [List.mem_flatMap, List.mem_map] at ho
  obtain ⟨left, ha, right, hb, rfl⟩ := ho
  exact (List.mem_append.mp hl).imp (fun hm => ⟨left, ha, hm⟩) (fun hm => ⟨right, hb, hm⟩)


/-- Normalization preserves the syntactic atom domain, at either polarity. -/
theorem toCNF_literal {fuel positive e cs} (h : toCNF fuel positive e = .success cs)
    {clause : Clause} {literal : Literal} (hc : clause ∈ cs) (hl : literal ∈ clause) :
    literal.1 ∈ e.atoms := by
  induction fuel generalizing positive e cs clause literal with
  | zero => cases h
  | succ fuel ih =>
    cases e with
    | const b =>
      clear ih
      cases b <;> cases positive <;> simp [toCNF] at h <;> cases h <;> simp_all
    | atom n =>
      clear ih
      simp only [toCNF, RunResult.success.injEq] at h
      subst cs
      simp_all [BoolExpr.atoms]
    | and a b =>
      cases hx : toCNF fuel positive a <;>
        simp [toCNF, hx, bind, pure, RunResult.bind] at h
      cases hy : toCNF fuel positive b <;> simp [hy] at h
      cases positive <;> simp at h hx
      all_goals simp only [BoolExpr.atoms, List.mem_dedup, List.mem_append]
      · rcases cnfOr_literal h hc hl with hleft | hright
        · obtain ⟨original, hm, hl⟩ := hleft
          exact .inl (ih hx hm hl)
        · obtain ⟨original, hm, hl⟩ := hright
          exact .inr (ih hy hm hl)
      · subst cs
        obtain ⟨original, hm, hl⟩ := clean_literal hc hl
        rcases List.mem_append.mp hm with hm | hm
        · exact .inl (ih hx hm hl)
        · exact .inr (ih hy hm hl)
    | or a b =>
      cases hx : toCNF fuel positive a <;>
        simp [toCNF, hx, bind, pure, RunResult.bind] at h
      cases hy : toCNF fuel positive b <;> simp [hy] at h
      cases positive <;> simp at h hx
      all_goals simp only [BoolExpr.atoms, List.mem_dedup, List.mem_append]
      · subst cs
        obtain ⟨original, hm, hl⟩ := clean_literal hc hl
        rcases List.mem_append.mp hm with hm | hm
        · exact .inl (ih hx hm hl)
        · exact .inr (ih hy hm hl)
      · rcases cnfOr_literal h hc hl with hleft | hright
        · obtain ⟨original, hm, hl⟩ := hleft
          exact .inl (ih hx hm hl)
        · obtain ⟨original, hm, hl⟩ := hright
          exact .inr (ih hy hm hl)
    | imp a b =>
      cases hx : toCNF fuel (!positive) a <;>
        simp [toCNF, hx, bind, pure, RunResult.bind] at h
      cases hy : toCNF fuel positive b <;> simp [hy] at h
      cases positive <;> simp at h hx
      all_goals simp only [BoolExpr.atoms, List.mem_dedup, List.mem_append]
      · subst cs
        obtain ⟨original, hm, hl⟩ := clean_literal hc hl
        rcases List.mem_append.mp hm with hm | hm
        · exact .inl (ih hx hm hl)
        · exact .inr (ih hy hm hl)
      · rcases cnfOr_literal h hc hl with hleft | hright
        · obtain ⟨original, hm, hl⟩ := hleft
          exact .inl (ih hx hm hl)
        · obtain ⟨original, hm, hl⟩ := hright
          exact .inr (ih hy hm hl)


theorem toCNF_atoms {fuel positive e cs v} (h : toCNF fuel positive e = .success cs)
    (hv : v ∈ cs.flatMap (List.map Prod.fst)) : v ∈ e.atoms := by
  simp only [List.mem_flatMap, List.mem_map] at hv
  obtain ⟨clause, hc, literal, hl, rfl⟩ := hv
  exact toCNF_literal h hc hl

end ModalityInference.CompactCNF
