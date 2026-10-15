import ModalityInference.Proofs.ComparisonPartialPropagationTermination
import ModalityInference.Proofs.ComparisonBody
import ModalityInference.ComparisonReduction

/-! Every structural reduction step decreases the pending worklist in the
lexicographic order of constructor count and modality-expression size. Both
reduction passes therefore complete and preserve completed results as fuel grows. -/

namespace ModalityInference.ComparisonReduction

open ComparisonPartialModes

def structuralSize : Ty → Nat
  | .var _ | .unit | .credit => 1
  | .prod a b | .sum a b | .fn a b => structuralSize a + structuralSize b + 1
  | .modal a _ => structuralSize a

theorem structuralSize_pos (t : Ty) : 0 < structuralSize t := by
  induction t <;> simp_all [structuralSize]

theorem expressionSize_pos (m : ModExpr) : 0 < expressionSize m := by
  induction m <;> simp_all [expressionSize]

def OuterProgress (t u : Ty) : Prop :=
  structuralSize u = structuralSize t ∧ (u = t ∨ modalitySize u < modalitySize t)

theorem OuterProgress.refl (t : Ty) : OuterProgress t t := ⟨rfl, Or.inl rfl⟩

theorem OuterProgress.le {t u : Ty} (h : OuterProgress t u) : modalitySize u ≤ modalitySize t := by
  rcases h.2 with h | h
  · simp [h]
  · omega

theorem OuterProgress.trans {t u v : Ty} (h : OuterProgress t u) (g : OuterProgress u v) :
    OuterProgress t v := by
  refine ⟨g.1.trans h.1, ?_⟩
  rcases g.2 with rfl | hg
  · exact h.2
  · exact Or.inr (lt_of_lt_of_le hg h.le)

theorem modal_progress (a : Ty) (m : ModExpr) : OuterProgress (.modal a m) a :=
  ⟨rfl, Or.inr (Nat.lt_add_of_pos_right (expressionSize_pos m))⟩

theorem normalizeOuterFuel_progress (fuel : Nat) (t : Ty) :
    OuterProgress t (normalizeOuterFuel fuel t) := by
  induction fuel generalizing t with
  | zero => exact .refl _
  | succ fuel ih =>
    cases t with
    | var | unit | credit | prod | sum | fn => exact .refl _
    | modal a m =>
      cases m <;> simp only [normalizeOuterFuel]
      case compose m n =>
        have h : OuterProgress (.modal a (.compose m n)) (.modal (.modal a m) n) := by
          exact ⟨rfl, Or.inr (by simp [modalitySize, expressionSize]; omega)⟩
        exact h.trans (ih _)
      all_goals
        split
        · next hm =>
          exact (modal_progress a _).trans (ih a)
        · exact .refl _

theorem peelOne_progress (total : ModExpr → Bool) (t : Ty) :
    OuterProgress t (ComparisonBody.peelFuel total 1 t).base := by
  have hn := normalizeOuterFuel_progress (modalitySize t) t
  change OuterProgress t (normalizeOuter t) at hn
  cases he : normalizeOuter t <;> simp only [ComparisonBody.peelFuel, he]
  case modal a m =>
    split
    · simpa only [ComparisonBody.peelFuel] using hn.trans (he ▸ modal_progress a m)
    · simpa only [he] using hn
  all_goals simpa only [he] using hn

def workWeight (pending : List (Ty × Ty)) : Nat × Nat :=
  ((pending.map fun pair => structuralSize pair.1 + structuralSize pair.2).sum,
   (pending.map fun pair => modalitySize pair.1 + modalitySize pair.2).sum)

def WorkLt (pending previous : List (Ty × Ty)) : Prop :=
  Prod.Lex (· < ·) (· < ·) (workWeight pending) (workWeight previous)

theorem WorkLt.tail (left right : Ty) (rest : List (Ty × Ty)) :
    WorkLt rest ((left, right) :: rest) := by
  apply Prod.lex_def.mpr
  left
  have h := structuralSize_pos left
  simp only [workWeight, List.map_cons, List.sum_cons]
  omega

theorem WorkLt.strip {total : ModExpr → Bool} {left right : Ty}
    {result : ComparisonBody.TotalStep} (h : ComparisonBody.stripTotal total left right = some result)
    (rest : List (Ty × Ty)) : WorkLt (result.bases :: rest) ((left, right) :: rest) := by
  have hl := peelOne_progress total left
  have hr := peelOne_progress total right
  have hle := hl.le
  have hre := hr.le
  simp only [ComparisonBody.stripTotal] at h
  split at h
  · contradiction
  · next hn =>
    cases h
    apply Prod.lex_def.mpr
    right
    constructor
    · simp only [workWeight, List.map_cons, List.sum_cons, hl.1, hr.1]
    · simp only [workWeight, List.map_cons, List.sum_cons]
      simp only [Bool.and_eq_true, beq_iff_eq] at hn
      rcases hl.2 with hl | hl <;> rcases hr.2 with hr | hr
      · exact False.elim (hn ⟨hl, hr⟩)
      · omega
      · omega
      · omega

theorem structuralSize_outer (t : Ty) : structuralSize t.outer.1 = structuralSize t := by
  induction t <;> simp_all [TypeExpr.outer, structuralSize]

theorem step_decreases {s next : State} (h : step s = .success next)
    (hp : s.pending ≠ []) : WorkLt next.pending s.pending := by
  cases he : s.pending with
  | nil => exact False.elim (hp he)
  | cons pair rest =>
    rcases pair with ⟨left, right⟩
    have hl := structuralSize_outer left
    have hr := structuralSize_outer right
    simp only [step, he] at h
    repeat' first | contradiction | (split at h <;> try dsimp only at h)
    all_goals cases h
    all_goals first | exact WorkLt.tail _ _ _ | skip
    · rename_i result hs
      cases hb : s.shared <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hs
      · contradiction
      exact WorkLt.strip hs rest
    all_goals
      apply Prod.lex_def.mpr
      left
      simp_all only [workWeight, List.map_cons, List.sum_cons, structuralSize]
      omega

theorem step_not_exhausted (s : State) : step s ≠ .exhausted := by
  intro h
  unfold step at h
  repeat' first | contradiction | (split at h <;> try dsimp only at h)

theorem work_wellFounded : WellFounded (fun next s : State => WorkLt next.pending s.pending) :=
  InvImage.wf (fun s : State => workWeight s.pending)
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

open ComparisonPartialPropagation in
theorem run_fuel_terminates (s : State) : Fuel.Terminates (fun fuel => run fuel s) := by
  induction s using work_wellFounded.induction with
  | h s ih =>
    by_cases hp : s.pending = []
    · exact ⟨1, .success s, by simp, fun fuel hf => by
        cases fuel with
        | zero => omega
        | succ fuel => simp [run, hp]⟩
    · have he : s.pending.isEmpty = false := by
        cases hps : s.pending with
        | nil => exact False.elim (hp hps)
        | cons => rfl
      cases hs : step s with
      | exhausted => exact False.elim (step_not_exhausted s hs)
      | rejected reason =>
        exact ⟨1, .rejected reason, by simp, fun fuel hf => by
          cases fuel with
          | zero => omega
          | succ fuel => simp [run, he, hs, bind, RunResult.bind]⟩
      | success next =>
        obtain ⟨n, result, hr, hn⟩ := ih next (step_decreases hs hp)
        exact ⟨n + 1, result, hr, fun fuel hf => by
          cases fuel with
          | zero => omega
          | succ fuel => simpa [run, he, hs, bind, RunResult.bind] using hn fuel (by omega)⟩

open ComparisonPartialPropagation in
theorem run_fuel_stable (s : State) : Fuel.Stable (fun fuel => run fuel s) := by
  intro small large result hle h hr
  induction small generalizing large s result with
  | zero => exact False.elim (hr h.symm)
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      simp only [run] at h ⊢
      split at h
      · next he => simpa only [he, ↓reduceIte] using h
      · next he =>
        simp only [he]
        cases hs : step s with
        | success next =>
          simp only [hs, bind, RunResult.bind] at h ⊢
          exact ih next (by omega) h hr
        | rejected reason => simpa only [hs, bind, RunResult.bind] using h
        | exhausted =>
          simp only [hs, bind, RunResult.bind] at h
          exact False.elim (hr h.symm)

open ComparisonPartialPropagation in
theorem prepare_fuel_terminates (p : SchemePreparation.Prepared)
    (templates : ComparisonSkeleton.Templates) (bare : List Nat) (known : List ModExpr)
    (shared : Bool) : Fuel.Terminates (fun fuel => prepare fuel p templates bare known shared) := by
  unfold prepare
  apply Fuel.Terminates.bind (run_fuel_terminates _)
  intro reduced
  exact run_fuel_terminates _

open ComparisonPartialPropagation in
theorem prepare_fuel_stable (p : SchemePreparation.Prepared)
    (templates : ComparisonSkeleton.Templates) (bare : List Nat) (known : List ModExpr)
    (shared : Bool) : Fuel.Stable (fun fuel => prepare fuel p templates bare known shared) := by
  unfold prepare
  apply Fuel.Stable.bind (run_fuel_stable _)
  intro reduced
  exact run_fuel_stable _

end ModalityInference.ComparisonReduction
