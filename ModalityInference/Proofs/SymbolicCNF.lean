import ModalityInference.SymbolicCNF
import ModalityInference.Proofs.SymbolicModes
import ModalityInference.Proofs.CNFPropagation

/-! Exact symbolic reconstruction and parameter support for ordered elimination. -/
namespace ModalityInference.SymbolicCNF

def interpret (s : Assignment) (σ : Nat → Bool) (v : Nat) : Bool :=
  (lookup s v).eval σ

@[simp] theorem lookup_nil (v : Nat) : lookup [] v = .atom v := rfl

@[simp] theorem interpret_nil (σ : Nat → Bool) : interpret [] σ = σ := rfl

theorem lookup_cons (v : Nat) (e : BoolExpr) (s : Assignment) :
    lookup ((v, e) :: s) = Function.update (lookup s) v e := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [lookup]
  · have he : (w == v) = false := by simpa using hw
    simp [lookup, List.lookup_cons, Function.update_of_ne hw, he]

@[simp] theorem interpret_cons (v : Nat) (e : BoolExpr) (s : Assignment)
    (σ : Nat → Bool) :
    interpret ((v, e) :: s) σ = Function.update (interpret s σ) v (e.eval σ) := by
  funext w
  simp only [interpret, lookup_cons]
  by_cases hw : w = v
  · subst w
    simp
  · rw [Function.update_of_ne hw, Function.update_of_ne hw]
    rfl

@[simp] theorem substitute_eval (s : Nat → BoolExpr) (e : BoolExpr) (σ : Nat → Bool) :
    (substitute s e).eval σ = e.eval (fun v => (s v).eval σ) := by
  induction e <;> simp [substitute, BoolExpr.eval, *]

@[simp] theorem literal_eval (s : Assignment) (l : Literal) (σ : Nat → Bool) :
    (literal s l).eval σ = (interpret s σ l.1 == l.2) := by
  rcases l with ⟨v, b⟩
  cases b <;> simp [literal, interpret, BoolExpr.eval]

@[simp] theorem clause_eval (s : Assignment) (c : Clause) (σ : Nat → Bool) :
    (clause s c).eval σ = CNFPropagation.clauseValue (interpret s σ) c := by
  induction c with
  | nil => rfl
  | cons l c ih =>
    simpa only [clause, List.foldr_cons, SymbolicModes.smartOr_eval, literal_eval,
      CNFPropagation.clauseValue, List.any_cons] using congrArg
      (fun b => (interpret s σ l.1 == l.2) || b) ih

@[simp] theorem lower_eval (s : Assignment) (cs : CNF) (v : Nat) (σ : Nat → Bool) :
    (lower s cs v).eval σ = CNFPropagation.lowerJoin cs v (interpret s σ) := by
  unfold lower CNFPropagation.lowerJoin
  induction CNFPropagation.lower cs v <;> simp [BoolExpr.eval, *]

/-- Every residual model is extended by the actual symbolic images, and evaluating
those images can never turn a false residual obligation into a model. -/
theorem solve_correct (vs : List Nat) (cs : CNF) (σ : Nat → Bool) :
    CNFHolds σ (solve vs cs).residual ↔
      CNFHolds (interpret (solve vs cs).values σ) cs := by
  induction vs generalizing cs with
  | nil => rfl
  | cons v vs ih =>
    simp only [solve, interpret_cons, lower_eval]
    rw [ih]
    constructor
    · exact CNFPropagation.eliminate_reconstruct cs v _
    · intro h
      exact (CNFPropagation.eliminate_update cs v _ _).mp
        (CNFPropagation.eliminate_preserves v h)

theorem substitute_atoms {s : Nat → BoolExpr} {e : BoolExpr} {w : Nat}
    (h : w ∈ (substitute s e).atoms) : ∃ v ∈ e.atoms, w ∈ (s v).atoms := by
  induction e with
  | const b => simp [substitute, BoolExpr.atoms] at h
  | atom v => exact ⟨v, by simp [BoolExpr.atoms], h⟩
  | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    first
    | have hh := SymbolicModes.smartAnd_atoms _ _ h
    | have hh := SymbolicModes.smartOr_atoms _ _ h
    | have hh := SymbolicModes.smartImp_atoms _ _ h
    rcases List.mem_append.mp hh with ha | hb
    · obtain ⟨v, hv, hw⟩ := iha ha
      exact ⟨v, by simp [BoolExpr.atoms, hv], hw⟩
    · obtain ⟨v, hv, hw⟩ := ihb hb
      exact ⟨v, by simp [BoolExpr.atoms, hv], hw⟩

theorem literal_atoms {s : Assignment} {l : Literal} {w : Nat}
    (h : w ∈ (literal s l).atoms) : w ∈ (lookup s l.1).atoms := by
  rcases l with ⟨v, b⟩
  cases b with
  | true => exact h
  | false =>
    simpa [BoolExpr.atoms] using SymbolicModes.smartImp_atoms _ _ h

theorem clause_atoms {s : Assignment} {c : Clause} {w : Nat}
    (h : w ∈ (clause s c).atoms) :
    ∃ v b, (v, b) ∈ c ∧ w ∈ (lookup s v).atoms := by
  induction c with
  | nil => simp [clause, BoolExpr.atoms] at h
  | cons l c ih =>
    rcases List.mem_append.mp (SymbolicModes.smartOr_atoms _ _ h) with hl | hc
    · exact ⟨l.1, l.2, by simp, literal_atoms hl⟩
    · obtain ⟨v, b, hv, hw⟩ := ih hc
      exact ⟨v, b, List.mem_cons_of_mem _ hv, hw⟩

theorem lower_atoms {s : Assignment} {cs : CNF} {v w : Nat}
    (h : w ∈ (lower s cs v).atoms) :
    ∃ u, u ∈ CNFPropagation.atoms cs ∧ u ≠ v ∧ w ∈ (lookup s u).atoms := by
  have hh : ∃ c ∈ CNFPropagation.lower cs v, w ∈ (clause s c).atoms := by
    unfold lower at h
    generalize CNFPropagation.lower cs v = ds at h ⊢
    induction ds with
    | nil => simp [BoolExpr.atoms] at h
    | cons c cs ih =>
      rcases List.mem_append.mp (SymbolicModes.smartOr_atoms _ _ h) with hc | ht
      · exact ⟨c, by simp, by simpa [BoolExpr.atoms] using
          SymbolicModes.smartImp_atoms _ _ hc⟩
      · obtain ⟨d, hd, hw⟩ := ih ht
        exact ⟨d, List.mem_cons_of_mem _ hd, hw⟩
  obtain ⟨c, hc, hcl⟩ := hh
  obtain ⟨u, b, hu, hlkup⟩ := clause_atoms hcl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hu := List.mem_filter.mp hu
  exact ⟨u, CNFPropagation.mem_atoms.mpr ⟨d, (List.mem_filter.mp hd).1, b, hu.1⟩,
    by simpa using hu.2, hlkup⟩

theorem solve_residual_atoms {vs : List Nat} {cs : CNF} {w : Nat}
    (h : w ∈ CNFPropagation.atoms (solve vs cs).residual) :
    w ∈ CNFPropagation.atoms cs ∧ w ∉ vs := by
  induction vs generalizing cs with
  | nil => exact ⟨h, by simp⟩
  | cons v vs ih =>
    obtain ⟨hw, hn⟩ := ih h
    obtain ⟨hw, hv⟩ := CNFPropagation.eliminate_atoms hw
    exact ⟨hw, by simp [hv, hn]⟩

@[simp] theorem solve_domain (vs : List Nat) (cs : CNF) :
    (solve vs cs).values.map Prod.fst = vs := by
  induction vs generalizing cs <;> simp [solve, *]

theorem solve_fixed {vs : List Nat} {cs : CNF} {v : Nat} (h : v ∉ vs) :
    lookup (solve vs cs).values v = .atom v := by
  induction vs generalizing cs with
  | nil => rfl
  | cons w vs ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [solve, lookup_cons, Function.update_of_ne h.1]
    exact ih h.2

theorem solve_atoms {vs : List Nat} {cs : CNF} {v w : Nat} (hv : v ∈ vs)
    (h : w ∈ (lookup (solve vs cs).values v).atoms) :
    w ∈ CNFPropagation.atoms cs ∧ w ∉ vs := by
  induction vs generalizing cs v with
  | nil => simp at hv
  | cons u us ih =>
    by_cases he : v = u
    · subst v
      simp only [solve, lookup_cons, Function.update_self] at h
      obtain ⟨x, hx, hxu, hw⟩ := lower_atoms h
      by_cases hxs : x ∈ us
      · obtain ⟨hw, hws⟩ := ih hxs hw
        obtain ⟨hw, hwu⟩ := CNFPropagation.eliminate_atoms hw
        exact ⟨hw, by simp [hwu, hws]⟩
      · rw [solve_fixed hxs] at hw
        have hwx : w = x := by simpa [BoolExpr.atoms] using hw
        subst w
        exact ⟨hx, by simp [hxu, hxs]⟩
    · simp only [solve, lookup_cons, Function.update_of_ne he] at h
      obtain ⟨hw, hws⟩ := ih ((List.mem_cons.mp hv).resolve_left he) h
      obtain ⟨hw, hwu⟩ := CNFPropagation.eliminate_atoms hw
      exact ⟨hw, by simp [hwu, hws]⟩

theorem solve_preserves (vs : List Nat) {cs : CNF} {σ : Nat → Bool}
    (h : CNFHolds σ cs) : CNFHolds σ (solve vs cs).residual := by
  induction vs generalizing cs with
  | nil => exact h
  | cons v vs ih => exact ih (CNFPropagation.eliminate_preserves v h)

/-- A parameter valuation satisfies the residual exactly when it has an extension
to the eliminated variables satisfying the original clauses. -/
theorem solve_complete (vs : List Nat) (cs : CNF) (σ : Nat → Bool) :
    CNFHolds σ (solve vs cs).residual ↔
      ∃ τ, (∀ v ∉ vs, τ v = σ v) ∧ CNFHolds τ cs := by
  constructor
  · intro h
    refine ⟨interpret (solve vs cs).values σ, ?_, (solve_correct vs cs σ).mp h⟩
    intro v hv
    simp [interpret, solve_fixed hv, BoolExpr.eval]
  · rintro ⟨τ, hτ, h⟩
    exact (CNFPropagation.holds_congr
      (fun v hv => hτ v (solve_residual_atoms hv).2)).mp (solve_preserves vs h)

theorem abstract_atoms {keep : Nat → Bool} {cs : CNF} {v : Nat}
    (h : v ∈ CNFPropagation.atoms (abstract keep cs)) :
    v ∈ CNFPropagation.atoms cs ∧ keep v = true := by
  obtain ⟨c, hc, b, hb⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hb, hk⟩ := List.mem_filter.mp hb
  exact ⟨CNFPropagation.cleanCNF_atoms (CNFPropagation.mem_atoms.mpr ⟨d, hd, b, hb⟩), hk⟩

/-- Universal abstraction is clause deletion of quantified literals, after
tautologies have been removed. It does not expand Boolean assignments. -/
theorem abstract_correct (keep : Nat → Bool) (cs : CNF) (σ : Nat → Bool) :
    CNFHolds σ (abstract keep cs) ↔
      ∀ τ, (∀ v, keep v = true → τ v = σ v) → CNFHolds τ cs := by
  constructor
  · intro h τ hτ
    apply (cleanCNF_correct τ cs).mp
    intro c hc
    obtain ⟨v, b, hv, he⟩ := h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    obtain ⟨hv, hk⟩ := List.mem_filter.mp hv
    exact ⟨v, b, hv, (hτ v hk).trans he⟩
  · intro h c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have hnt : clauseTautology d = false := by
      simpa using (List.mem_filter.mp (List.mem_dedup.mp hd)).2
    let τ : Nat → Bool := fun v => if keep v then σ v else !d.contains (v, true)
    have hτ : ∀ v, keep v = true → τ v = σ v := by
      intro v hv
      simp [τ, hv]
    obtain ⟨v, b, hv, he⟩ := (cleanCNF_correct τ cs).mpr (h τ hτ) d hd
    by_cases hk : keep v = true
    · exact ⟨v, b, List.mem_filter.mpr ⟨hv, hk⟩, (hτ v hk).symm.trans he⟩
    · have hkf : keep v = false := Bool.eq_false_iff.mpr hk
      cases b with
      | true => simp [τ, hkf, hv] at he
      | false =>
        have hp : (v, true) ∈ d := by simpa [τ, hkf] using he
        have ht : clauseTautology d = true := by
          exact List.any_eq_true.mpr ⟨(v, false), hv, by simpa using hp⟩
        simp [hnt] at ht

end ModalityInference.SymbolicCNF
