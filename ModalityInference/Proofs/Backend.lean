import ModalityInference.ModeBackend

/-! Boolean normalization and the reduction to the independently verified generic solver. -/
namespace ModalityInference

def ClauseHolds (σ : Nat → Bool) (c : Clause) : Prop :=
  ∃ v p, (v, p) ∈ c ∧ σ v = p

def CNFHolds (σ : Nat → Bool) (cs : CNF) : Prop :=
  ∀ c ∈ cs, ClauseHolds σ c

@[simp] theorem clauseHolds_cons (σ : Nat → Bool) (v : Nat) (p : Bool) (c : Clause) :
    ClauseHolds σ ((v, p) :: c) ↔ σ v = p ∨ ClauseHolds σ c := by
  simp [ClauseHolds, exists_or]

@[simp] theorem clauseHolds_append (σ : Nat → Bool) (a b : Clause) :
    ClauseHolds σ (a ++ b) ↔ ClauseHolds σ a ∨ ClauseHolds σ b := by
  simp [ClauseHolds, exists_or]

@[simp] theorem clauseHolds_dedup (σ : Nat → Bool) (c : Clause) :
    ClauseHolds σ c.dedup ↔ ClauseHolds σ c := by simp [ClauseHolds]

theorem clauseTautology_correct {c} (h : clauseTautology c = true) (σ : Nat → Bool) :
    ClauseHolds σ c := by
  simp [clauseTautology, List.any_eq_true] at h
  rcases h with ⟨v, (⟨hf, ht⟩ | ⟨ht, hf⟩)⟩
  all_goals exact ⟨v, σ v, by cases (σ v) <;> assumption, rfl⟩

theorem cleanCNF_correct (σ : Nat → Bool) (cs : CNF) :
    CNFHolds σ (cleanCNF cs) ↔ CNFHolds σ cs := by
  simp [cleanCNF, CNFHolds]
  exact ⟨fun h c hc => if ht : clauseTautology c.dedup = true then
      (clauseHolds_dedup σ c).mp (clauseTautology_correct ht σ)
    else h c hc (Bool.eq_false_iff.mpr ht), fun h c hc _ => h c hc⟩

theorem cnfOr_correct {limit a b cs} (h : cnfOr limit a b = .success cs)
    (σ : Nat → Bool) : CNFHolds σ cs ↔ CNFHolds σ a ∨ CNFHolds σ b := by
  unfold cnfOr at h
  split at h <;> simp at h
  rw [← h, cleanCNF_correct]
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

@[simp] theorem cnfHolds_append (σ : Nat → Bool) (a b : CNF) :
    CNFHolds σ (a ++ b) ↔ CNFHolds σ a ∧ CNFHolds σ b := by
  simp [CNFHolds, or_imp, forall_and]

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
      · rw [← h, cleanCNF_correct, cnfHolds_append, ih hx, ih hy]
        simp [BoolExpr.eval]
    | or a b =>
      cases hx : toCNF fuel positive a <;>
        simp [toCNF, hx, bind, pure, RunResult.bind] at h
      cases hy : toCNF fuel positive b <;> simp [hy] at h
      cases positive <;> simp at h
      · simp only [← h, cleanCNF_correct, cnfHolds_append, ih hx, ih hy,
          BoolExpr.eval, Bool.or_eq_false_iff]
      · simp [cnfOr_correct h, ih hx, ih hy, BoolExpr.eval]
    | imp a b =>
      cases hx : toCNF fuel (!positive) a <;>
        simp [toCNF, hx, bind, pure, RunResult.bind] at h
      cases hy : toCNF fuel positive b <;> simp [hy] at h
      cases positive <;> simp at h hx
      · simp [← h, cleanCNF_correct, cnfHolds_append, ih hx, ih hy, BoolExpr.eval]
      · simp [cnfOr_correct h, ih hx, ih hy, BoolExpr.eval]

namespace ConcreteBackend

theorem atomFin_lookup {atoms v i} (h : atomFin atoms v = some i) : atoms[i] = v := by
  unfold atomFin at h
  dsimp only at h
  split at h <;> simp at h
  cases h
  exact List.getElem_idxOf _

theorem equationFrom_correct {atoms c hypothesis goal q}
    (h : equationFrom atoms c hypothesis goal = some q)
    (σ : Nat → Bool) (env : Vector Bool atoms.length)
    (hσ : ∀ v i, atomFin atoms v = some i → env.get i = σ v) :
    Equation.satisfied env q ↔
      RightExpr.eval env hypothesis ≤ LeftExpr.eval env goal ∨ ClauseHolds σ c := by
  induction c generalizing hypothesis goal q with
  | nil => simp [equationFrom] at h; cases h; simp [Equation.satisfied, ClauseHolds]
  | cons lit c ih =>
    rcases lit with ⟨v, p⟩
    cases hi : atomFin atoms v <;> simp [equationFrom, hi] at h
    cases p <;> simp at h
    all_goals rw [ih h, clauseHolds_cons]
    all_goals simp only [RightExpr.eval, LeftExpr.eval, hσ _ _ hi]
    all_goals cases (RightExpr.eval env hypothesis) <;> cases (LeftExpr.eval env goal) <;>
      cases (σ v) <;> simp [Bool.le_iff_imp]

theorem equation_correct {atoms c q} (h : equation atoms c = some q) :
    Equation.valid q ↔ ∀ σ, ClauseHolds σ c := by
  constructor
  · intro hv σ
    have hx := equationFrom_correct h σ (Vector.ofFn fun i => σ atoms[i])
    have hm : ∀ v i, atomFin atoms v = some i →
        (Vector.ofFn fun i => σ atoms[i]).get i = σ v := by
      intro v i hi
      simpa [Vector.get] using congrArg σ (atomFin_lookup hi)
    simpa [RightExpr.eval, LeftExpr.eval, Bool.le_iff_imp] using (hx hm).mp (hv _)
  · intro hv env
    let σ : Nat → Bool := fun v => (atomFin atoms v).map env.get |>.getD false
    have hx := equationFrom_correct h σ env
    exact (hx (fun v i hi => by simp [σ, hi])).mpr (.inr (hv σ))

theorem decideClauses_correct {atoms cs initial result}
    (h : decideClauses atoms cs initial = .success result) :
    result = true ↔ initial = true ∧ ∀ σ, CNFHolds σ cs := by
  induction cs generalizing initial with
  | nil => simpa [decideClauses, CNFHolds] using h.symm
  | cons c cs ih =>
    cases he : equation atoms c <;> simp [decideClauses, he] at h
    simpa [Bool.and_eq_true, Equation.decide_correct, equation_correct he,
      CNFHolds, forall_and, and_assoc] using ih h

theorem decideFormula_correct {fuel e report}
    (h : decideFormula fuel e = .success report) :
    report.valid = true ↔ ∀ σ, e.eval σ = true := by
  unfold decideFormula at h
  cases hc : toCNF fuel true e with
  | rejected _ | exhausted => simp [hc, bind, RunResult.bind] at h
  | success cs =>
    cases hd : decideClauses (e.atoms.mergeSort (· ≤ ·)) cs true <;>
      simp [hc, hd, bind, pure, RunResult.bind] at h
    cases h
    simpa only [true_and, toCNF_correct hc] using decideClauses_correct hd

end ConcreteBackend
end ModalityInference
