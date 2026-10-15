import ModalityInference.Proofs.ComparisonPropagation

/-! Pointwise validation of compiled comparison bounds. Lower and edge closure
is global; the residual checks and upper bounds need only hold at the valuation
selected by uniform modality synthesis. -/
namespace ModalityInference.ComparisonPropagation

def Program.HoldsAt (program : Program count) (store : Store count) (σ : Nat → Bool) : Prop :=
  (∀ v : Fin count, CNFHolds σ program.lower[v] → CNFHolds σ store[v]) ∧
    (∀ e ∈ program.edges, CNFHolds (fun i => σ (i / 2)) e.relation →
      CNFHolds σ store[e.source] → CNFHolds σ store[e.target]) ∧
    CNFHolds σ program.checks ∧
    ∀ v : Fin count, CNFHolds σ store[v] → CNFHolds σ program.upper[v]

private theorem diagonal_same (size : Nat) (condition : CNF) (σ : Nat → Bool) :
    CNFHolds (fun i => σ (i / 2)) (diagonal size condition) ↔ CNFHolds σ condition := by
  rw [diagonal_correct]
  simp

theorem Program.Closed.holdsAt {program : Program count} {store : Store count}
    (h : program.Closed store) {σ : Nat → Bool}
    (hr : CNFHolds σ (residual program store)) : program.HoldsAt store σ := by
  obtain ⟨hc, hu⟩ := (residual_correct program store σ).mp hr
  refine ⟨fun v => h.1 v σ, ?_, hc, hu⟩
  intro e he hr hs
  have ht := h.2 e he (fun i => σ (i / 2)) hr (by simpa using hs)
  simpa using ht

theorem Program.add_holdsAt {size : Nat} {program : Program count} {store : Store count}
    {σ : Nat → Bool} (obligation : Obligation count)
    (h : (program.add size obligation).HoldsAt store σ) :
    program.HoldsAt store σ ∧ obligation.Holds σ (fun v => CNFHolds σ store[v]) := by
  cases obligation with
  | lower v condition =>
    obtain ⟨hl, he, hc, hu⟩ := h
    refine ⟨⟨?_, he, hc, hu⟩, ?_⟩
    · intro w hw
      apply hl w
      by_cases hv : w = v
      · simpa [Program.add, hv, join_correct] using Or.inr hw
      · simpa [Program.add, hv] using hw
    · intro hc
      apply hl v
      simp [Program.add, join_correct, hc]
  | upper v condition =>
    obtain ⟨hl, he, hc, hu⟩ := h
    refine ⟨⟨hl, he, hc, ?_⟩, ?_⟩
    · intro w hw
      have hh := hu w hw
      by_cases hv : w = v
      · subst w
        exact ((meet_correct _ _ _).mp (by simpa [Program.add] using hh)).2
      · simpa [Program.add, hv] using hh
    · intro hv
      have hh := hu v hv
      exact ((meet_correct _ _ _).mp (by simpa [Program.add] using hh)).1
  | edge source target condition =>
    obtain ⟨hl, he, hc, hu⟩ := h
    refine ⟨⟨hl, ?_, hc, hu⟩, ?_⟩
    · intro e hem
      exact he e (List.mem_cons_of_mem _ hem)
    · intro hcond hs
      exact he ⟨source, target, diagonal size condition⟩ (by simp [Program.add])
        ((diagonal_same size condition σ).mpr hcond) hs
  | check condition =>
    obtain ⟨hl, he, hc, hu⟩ := h
    have hh := (meet_correct condition program.checks σ).mp hc
    exact ⟨⟨hl, he, hh.2, hu⟩, hh.1⟩

private theorem fold_holdsAt {size : Nat} (obligations : List (Obligation count))
    {program : Program count} {store : Store count} {σ : Nat → Bool}
    (h : (obligations.foldl (Program.add size) program).HoldsAt store σ) :
    program.HoldsAt store σ ∧
      ∀ obligation ∈ obligations, obligation.Holds σ (fun v => CNFHolds σ store[v]) := by
  induction obligations generalizing program with
  | nil => exact ⟨h, by simp⟩
  | cons obligation obligations ih =>
    obtain ⟨hp, hrest⟩ := ih h
    obtain ⟨hp, hfirst⟩ := Program.add_holdsAt obligation hp
    refine ⟨hp, ?_⟩
    intro o ho
    rcases List.mem_cons.mp ho with rfl | ho
    · exact hfirst
    · exact hrest o ho

theorem compile_holdsAt {size : Nat} {action : ModExpr → Action} {theory : CNF}
    {bounds : List (Bound count)} {store : Store count} {σ : Nat → Bool}
    (h : (compile size action theory bounds).HoldsAt store σ) :
    ∀ bound ∈ bounds, CNFHolds σ theory →
      bound.left.Holds action σ (fun v => CNFHolds σ store[v]) →
      bound.right.Holds action σ (fun v => CNFHolds σ store[v]) := by
  have hobligations := (fold_holdsAt (bounds.flatMap (compileBound action theory)) h).2
  intro bound hb
  apply (compileBound_correct action theory bound σ _).mp
  exact fun obligation ho => hobligations obligation (List.mem_flatMap.mpr ⟨bound, hb, ho⟩)

/-- The synthesized valuation only needs to satisfy the residual obligation.
The globally saturated lower and edge clauses supply the remaining premises. -/
theorem reduce_compile_pointwise {basis : List CompareTy} {size : Nat}
    {action : ModExpr → Action} {theory : CNF} {bounds : List (Bound count)}
    {result : Reduction count}
    (h : reduce basis (compile size action theory bounds) = .success result)
    {σ : Nat → Bool} (ho : CNFHolds σ result.obligation) :
    ∀ bound ∈ bounds, CNFHolds σ theory →
      bound.left.Holds action σ (fun v => CNFHolds σ result.store[v]) →
      bound.right.Holds action σ (fun v => CNFHolds σ result.store[v]) := by
  apply compile_holdsAt
  apply (reduce_closed h).holdsAt
  exact (reduce_correct h).2.2 ▸ ho

end ModalityInference.ComparisonPropagation
