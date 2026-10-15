import ModalityInference.Proofs.CNFNormalization
import ModalityInference.Proofs.HornPropagation
import ModalityInference.ComparisonBody

/-! Normalization preserves its atom domain, so the concrete validity backend
and annotation classification always finish without internal rejection. -/
namespace ModalityInference

theorem cleanCNF_literal {literal : Literal} {clause : Clause} {clauses : CNF}
    (hc : clause ∈ cleanCNF clauses) (hl : literal ∈ clause) :
    ∃ original ∈ clauses, literal ∈ original := by
  simp only [cleanCNF, List.mem_dedup, List.mem_filter, List.mem_map] at hc
  obtain ⟨⟨original, ho, rfl⟩, _⟩ := hc
  exact ⟨original, ho, List.mem_dedup.mp hl⟩

theorem cnfOr_literal {limit : Nat} {a b cs : CNF} {clause : Clause} {literal : Literal}
    (h : cnfOr limit a b = .success cs) (hc : clause ∈ cs) (hl : literal ∈ clause) :
    (∃ original ∈ a, literal ∈ original) ∨ (∃ original ∈ b, literal ∈ original) := by
  unfold cnfOr at h
  split at h <;> simp at h
  subst cs
  obtain ⟨original, ho, hl⟩ := cleanCNF_literal hc hl
  simp only [List.mem_flatMap, List.mem_map] at ho
  obtain ⟨left, ha, right, hb, rfl⟩ := ho
  exact (List.mem_append.mp hl).imp (fun hm => ⟨left, ha, hm⟩) (fun hm => ⟨right, hb, hm⟩)

/-- Every normalized literal belongs to the expression's original atom domain. -/
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
        obtain ⟨original, hm, hl⟩ := cleanCNF_literal hc hl
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
        obtain ⟨original, hm, hl⟩ := cleanCNF_literal hc hl
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
        obtain ⟨original, hm, hl⟩ := cleanCNF_literal hc hl
        rcases List.mem_append.mp hm with hm | hm
        · exact .inl (ih hx hm hl)
        · exact .inr (ih hy hm hl)
      · rcases cnfOr_literal h hc hl with hleft | hright
        · obtain ⟨original, hm, hl⟩ := hleft
          exact .inl (ih hx hm hl)
        · obtain ⟨original, hm, hl⟩ := hright
          exact .inr (ih hy hm hl)

namespace ConcreteBackend

theorem equationFrom_complete {atoms : List Nat} {clause : Clause}
    (h : ∀ literal ∈ clause, literal.1 ∈ atoms)
    (hypothesis : RightExpr Bool atoms.length) (goal : LeftExpr Bool atoms.length) :
    ∃ q, equationFrom atoms clause hypothesis goal = some q := by
  induction clause generalizing hypothesis goal with
  | nil => exact ⟨_, rfl⟩
  | cons literal clause ih =>
    obtain ⟨v, positive⟩ := literal
    obtain ⟨i, hi⟩ := HornPropagation.atomFin_exists (h (v, positive) (by simp))
    have ht : ∀ literal ∈ clause, literal.1 ∈ atoms := fun literal hl => h literal (by simp [hl])
    cases positive
    · simpa [equationFrom, hi] using ih ht (.meet hypothesis (.var i)) goal
    · simpa [equationFrom, hi] using ih ht hypothesis (.join goal (.var i))

theorem decideClauses_complete {atoms : List Nat} {clauses : CNF}
    (h : ∀ clause ∈ clauses, ∀ literal ∈ clause, literal.1 ∈ atoms) (initial : Bool) :
    ∃ result, decideClauses atoms clauses initial = .success result := by
  induction clauses generalizing initial with
  | nil => exact ⟨initial, rfl⟩
  | cons clause clauses ih =>
    obtain ⟨q, hq⟩ := equationFrom_complete (h clause (by simp)) (.const true) (.const false)
    have ht : ∀ clause ∈ clauses, ∀ literal ∈ clause, literal.1 ∈ atoms :=
      fun clause hc => h clause (by simp [hc])
    simpa [decideClauses, equation, hq] using ih ht (initial && Equation.decide q)

/-- The validity result stabilizes at success; false validity is a successful
decision, and atom-domain diagnostics cannot occur on normalized expressions. -/
theorem decideFormula_complete (e : BoolExpr) :
    ∃ n report, ∀ fuel ≥ n, decideFormula fuel e = .success report := by
  obtain ⟨n, clauses, hn⟩ := toCNF_complete e true
  have hc : ∀ clause ∈ clauses, ∀ literal ∈ clause,
      literal.1 ∈ e.atoms.mergeSort (· ≤ ·) := by
    intro clause hcl literal hl
    simpa using toCNF_literal (hn n le_rfl) hcl hl
  obtain ⟨valid, hv⟩ := decideClauses_complete hc true
  exact ⟨n, ⟨e.atoms.mergeSort (· ≤ ·), clauses, valid⟩, fun fuel hf => by
    simp [decideFormula, hn fuel hf, hv, bind, pure, RunResult.bind]⟩

end ConcreteBackend

namespace ComparisonBody

theorem checkTotal_eventual_success (assumptions : Bounds) (expressions : List ModExpr) :
    ∃ n known, ∀ fuel ≥ n, checkTotal fuel assumptions expressions = .success known := by
  induction expressions with
  | nil => exact ⟨0, [], fun _ _ => rfl⟩
  | cons m ms ih =>
    obtain ⟨n, report, hn⟩ := ConcreteBackend.decideFormula_complete
      (.imp (boundsModeFormula assumptions) (boundsModeFormula [.defined m]))
    obtain ⟨k, rest, hk⟩ := ih
    refine ⟨max n k, if report.valid then m :: rest else rest, ?_⟩
    intro fuel hf
    simp [checkTotal, ConcreteBackend.entails, hn fuel ((Nat.le_max_left _ _).trans hf),
      hk fuel ((Nat.le_max_right _ _).trans hf), bind, pure, RunResult.bind]

/-- Classification returns a fixed list once its finite backend queries have
enough fuel, including when some residuals are not entailed by the bounds. -/
theorem knownTotal_eventual_success (assumptions : Bounds) (expressions : List ModExpr) :
    ∃ n known, ∀ fuel ≥ n, knownTotal fuel assumptions expressions = .success known :=
  checkTotal_eventual_success assumptions (expressions.flatMap residuals).eraseDups

end ComparisonBody
end ModalityInference
