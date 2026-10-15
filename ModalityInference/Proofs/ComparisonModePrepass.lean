import ModalityInference.ComparisonModePrepass
import ModalityInference.Proofs.ComparisonElimination
import ModalityInference.Proofs.ComparisonContextSupport

/-! The scalar feasibility prepass performs existential leaf elimination followed
by universal fixed-coordinate abstraction. Successful retries carry only scoped,
bounded source-modality specializations; comparison still checks every original
obligation after applying them. -/
namespace ModalityInference.ComparisonModePrepass

open ComparisonPropagation ComparisonElimination

theorem leafFormula_correct (leaf : Leaf count) (σ : Nat → Bool) :
    CNFHolds σ (leafFormula leaf) ↔
      leaf.Holds (σ ∘ (count + ·)) (fun i => σ i.val = true) := by
  cases leaf with
  | fixed cs => exact rename_correct _ _ _
  | flex i => simp [leafFormula, Leaf.Holds, CNFHolds, ClauseHolds]

theorem endpointFormula_correct (action : ModExpr → Action) (a : Endpoint count)
    (σ : Nat → Bool) :
    CNFHolds σ (endpointFormula action a) ↔
      a.Holds action (σ ∘ (count + ·)) (fun i => σ i.val = true) := by
  simp only [endpointFormula, Action.apply, meet_correct, join_correct,
    leafFormula_correct, rename_correct, Endpoint.Holds, Action.Holds]

theorem inequalities_correct (action : ModExpr → Action) (theory : CNF)
    (bounds : List (Bound count)) (σ : Nat → Bool) :
    CNFHolds σ (inequalities action theory bounds) ↔
      ∀ b ∈ bounds, CNFHolds (σ ∘ (count + ·)) theory →
        b.left.Holds action (σ ∘ (count + ·)) (fun i => σ i.val = true) →
        b.right.Holds action (σ ∘ (count + ·)) (fun i => σ i.val = true) := by
  induction bounds with
  | nil => simp [inequalities, CNFHolds]
  | cons b bs ih =>
    simp only [inequalities, List.foldr_cons, meet_correct, implies_correct,
      rename_correct, endpointFormula_correct]
    simpa only [List.forall_mem_cons, inequalities] using and_congr Iff.rfl ih

/-- The quantifier order is exact: leaf values may depend on the fixed type
valuation, while retained scalar values are unchanged throughout projection. -/
theorem projectQuery_correct (leafCount basisSize : Nat) (cs : CNF) (η : Nat → Bool) :
    (projectQuery leafCount basisSize cs).eval η = true ↔
      ∀ σ : Nat → Bool, (∀ i, σ (leafCount + basisSize + 2 + i) = η i) →
        ∃ τ, (∀ i, leafCount ≤ i → τ i = σ i) ∧ CNFHolds τ cs := by
  simp only [projectQuery, formula_correct, rename_correct, SymbolicCNF.abstract_correct,
    project_complete, List.mem_range, not_lt]
  constructor
  · intro h σ hs
    apply h σ
    intro v hv
    have hv : leafCount + basisSize + 2 ≤ v := by simpa using hv
    simpa only [Function.comp_apply, Nat.add_sub_of_le hv] using hs (v - (leafCount + basisSize + 2))
  · intro h σ hs
    apply h σ
    intro i
    simpa only [Function.comp_apply, Nat.add_sub_cancel_left] using hs
      (leafCount + basisSize + 2 + i) (by simp)

/-- Every simultaneous leaf witness supplies the necessary scalar feasibility
query. This direction imposes no polynomial form on the witness values. -/
theorem projectQuery_necessary (leafCount basisSize : Nat) (cs : CNF) (η : Nat → Bool)
    (h : ∀ σ : Nat → Bool, (∀ i, σ (leafCount + basisSize + 2 + i) = η i) →
      ∃ τ, (∀ i, leafCount ≤ i → τ i = σ i) ∧ CNFHolds τ cs) :
    (projectQuery leafCount basisSize cs).eval η = true :=
  (projectQuery_correct leafCount basisSize cs η).mpr h

private def extend (values : Fin count → Bool) (σ : Nat → Bool) (i : Nat) : Bool :=
  if h : i < count then values ⟨i, h⟩ else σ (i - count)

private theorem extend_shift (values : Fin count → Bool) (σ : Nat → Bool) :
    extend values σ ∘ (count + ·) = σ := by
  funext i
  simp [extend]

private theorem extend_low (values : Fin count → Bool) (σ : Nat → Bool) (i : Fin count) :
    extend values σ i.val = values i := by
  simp [extend, i.isLt]

/-- Feasibility is exactly pointwise existential leaf assignment, with a single
retained modality environment shared by all inequalities and coordinates. -/
theorem boundsQuery_correct (basisSize : Nat) (action : ModExpr → Action)
    (theory : CNF) (bounds : List (Bound count)) (η : Nat → Bool) :
    (projectQuery count basisSize (inequalities action theory bounds)).eval η = true ↔
      ∀ σ : Nat → Bool, (∀ i, σ (basisSize + 2 + i) = η i) →
        ∃ values : Fin count → Bool, ∀ b ∈ bounds, CNFHolds σ theory →
          b.left.Holds action σ (fun i => values i = true) →
          b.right.Holds action σ (fun i => values i = true) := by
  rw [projectQuery_correct]
  constructor
  · intro h σ hs
    obtain ⟨τ, ht, hc⟩ := h (extend (count := count) (fun _ => false) σ) (by
      intro i
      simpa only [extend, dif_neg (by omega : ¬ count + basisSize + 2 + i < count),
        show count + basisSize + 2 + i - count = basisSize + 2 + i by omega] using hs i)
    have he : τ ∘ (count + ·) = σ := by
      funext i
      simpa only [extend, dif_neg (by omega : ¬ count + i < count),
        Nat.add_sub_cancel_left, Function.comp_apply] using ht (count + i) (by omega)
    refine ⟨fun i => τ i.val, ?_⟩
    simpa only [he] using (inequalities_correct action theory bounds τ).mp hc
  · intro h σ hs
    obtain ⟨values, hv⟩ := h (σ ∘ (count + ·)) (by
      intro i
      simpa [Function.comp_def, Nat.add_assoc] using hs i)
    refine ⟨extend values (σ ∘ (count + ·)), ?_, ?_⟩
    · intro i hi
      simp [extend, Nat.not_lt.mpr hi, Nat.add_sub_of_le hi]
    · apply (inequalities_correct action theory bounds _).mpr
      simpa only [extend_shift, extend_low] using hv

theorem selectionCheck_scoped {p : SchemePreparation.Prepared} {action : Substitution}
    (h : selectionCheck p action = true) : ComparisonContext.Scoped p action :=
by
  apply (ComparisonContext.scopeCheck_iff p action).mp
  simpa only [selectionCheck, Bool.and_eq_true] using (Bool.and_eq_true_iff.mp h).1

theorem selectionCheck_bounded {p : SchemePreparation.Prepared} {action : Substitution}
    (h : selectionCheck p action = true) : action.Bounded p.nextType p.nextMode := by
  have hs := selectionCheck_scoped h
  refine ⟨?_, ?_⟩
  · intro n a ha
    simp [hs.1] at ha
  · intro n m hm
    have hn := (hs.2 n m hm).1
    simp only [ComparisonInstance.modeAllowed, Bool.and_eq_true, decide_eq_true_eq] at hn
    refine ⟨hn.2, (ModExpr.bounded_iff m p.nextMode).mpr ?_⟩
    have hb := (Bool.and_eq_true_iff.mp h).2
    simp only [List.all_eq_true] at hb
    intro v hv
    exact of_decide_eq_true (hb (n, m) hm v (by simpa using hv))

theorem attempt_checked {fuel p shapes action}
    (h : attempt fuel p shapes = .success action) : selectionCheck p action = true := by
  unfold attempt at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first | contradiction | cases h | split at h
  assumption

theorem attempt_scoped {fuel p shapes action}
    (h : attempt fuel p shapes = .success action) : ComparisonContext.Scoped p action :=
  selectionCheck_scoped (attempt_checked h)

theorem attempt_bounded {fuel p shapes action}
    (h : attempt fuel p shapes = .success action) : action.Bounded p.nextType p.nextMode :=
  selectionCheck_bounded (attempt_checked h)

end ModalityInference.ComparisonModePrepass
