import ModalityInference.ComparisonShapeSolver
import Mathlib.Data.Finset.Card
import ModalityInference.Proofs.SyntacticEquality
import ModalityInference.Proofs.SchemePreparedScope

namespace ModalityInference
deriving instance ReflBEq for ComparisonShape
deriving instance LawfulBEq for ComparisonShape
end ModalityInference

namespace ModalityInference.ComparisonShapeSolver

/-- Symbolic solutions of the finite shape equations. -/
def Models (ps : Pairs) (ρ : TypeVar → ComparisonShape) : Prop :=
  ∀ p ∈ ps, p.1.subst ρ = p.2.subst ρ

def Fixes (allowed : TypeVar → Bool) (ρ : TypeVar → ComparisonShape) : Prop :=
  ∀ v, allowed v = false → ρ v = .var v

@[simp] theorem subst_id (t : ComparisonShape) : t.subst .var = t := by
  induction t <;> simp_all [ComparisonShape.subst]

theorem subst_comp (t : ComparisonShape) (ρ η : TypeVar → ComparisonShape) :
    (t.subst ρ).subst η = t.subst (fun v => (ρ v).subst η) := by
  induction t <;> simp_all [ComparisonShape.subst]

theorem subst_congr (t : ComparisonShape) {ρ η : TypeVar → ComparisonShape}
    (h : ∀ v ∈ t.vars, ρ v = η v) : t.subst ρ = t.subst η := by
  induction t <;> simp_all [ComparisonShape.subst, ComparisonShape.vars]

@[simp] theorem action_nil (v : TypeVar) : action [] v = .var v := rfl

@[simp] theorem action_cons (v : TypeVar) (t : ComparisonShape) (s : Assignment) (w : TypeVar) :
    action ((v, t) :: s) w = if w == v then t else action s w := by
  cases h : w == v <;> simp [action, List.lookup_cons, h]


theorem replace_fresh (v : TypeVar) (t : ComparisonShape) (h : v ∉ t.vars) :
    t.subst (replace v t) = t := by
  refine (subst_congr t ?_).trans (subst_id t)
  intro w hw
  have hn : w ≠ v := fun he => h (he ▸ hw)
  simp [replace, hn]


theorem extend_action (v : TypeVar) (t : ComparisonShape) (s : Assignment) (w : TypeVar) :
    action ((v, t.subst (action s)) :: s) w = (replace v t w).subst (action s) := by
  simp only [action_cons, replace]
  split <;> rfl

theorem replace_eval (t : ComparisonShape) {ρ : TypeVar → ComparisonShape}
    {v : TypeVar} {u : ComparisonShape} (h : ρ v = u.subst ρ) :
    (t.subst (replace v u)).subst ρ = t.subst ρ := by
  rw [subst_comp]
  apply subst_congr
  intro w hw
  by_cases he : w = v <;> simp [replace, he, h, ComparisonShape.subst]


@[simp] theorem models_cons {ps a b ρ} : Models ((a, b) :: ps) ρ ↔
    a.subst ρ = b.subst ρ ∧ Models ps ρ := by
  simp [Models]

theorem models_replace {ps ρ v t} (h : Models ps ρ) (hv : ρ v = t.subst ρ) :
    Models (mapPairs (replace v t) ps) ρ := by
  intro p hp
  simp only [mapPairs, List.mem_map] at hp
  obtain ⟨⟨a, b⟩, hm, rfl⟩ := hp
  simpa only [replace_eval _ hv] using h (a, b) hm


theorem choose_spec {allowed a b v t} (h : choose allowed a b = some (v, t)) :
    allowed v = true ∧ ((a = .var v ∧ b = t) ∨ (b = .var v ∧ a = t)) := by
  cases a <;> cases b <;> simp only [choose] at h
  all_goals repeat' (split at h <;> simp_all)
  all_goals aesop


theorem subst_extend (a : ComparisonShape) (v : TypeVar) (t : ComparisonShape) (s : Assignment) :
    a.subst (action ((v, t.subst (action s)) :: s)) =
      (a.subst (replace v t)).subst (action s) := by
  rw [subst_comp]
  exact subst_congr a (fun w _ => extend_action v t s w)

theorem models_extend {v t ps s} (hv : v ∉ t.vars)
    (h : Models (mapPairs (replace v t) ps) (action s)) :
    Models ((.var v, t) :: ps) (action ((v, t.subst (action s)) :: s)) := by
  rw [models_cons]
  constructor
  · simp [subst_extend, ComparisonShape.subst, replace_fresh v t hv]
  · intro p hp
    simpa only [subst_extend] using h _ (List.mem_map.mpr ⟨p, hp, rfl⟩)


theorem unify_sound {fuel allowed ps s} (h : unify fuel allowed ps = .success s) :
    Models ps (action s) := by
  induction fuel generalizing ps s with
  | zero => cases h
  | succ fuel ih =>
    cases ps with
    | nil => simp [Models]
    | cons pair rest =>
      rcases pair with ⟨a, b⟩
      simp only [unify] at h
      split at h
      case isTrue he =>
        exact models_cons.mpr ⟨congrArg (ComparisonShape.subst (action s)) (eq_of_beq he), ih h⟩
      case isFalse he =>
        cases hp : choose allowed a b with
        | none =>
          simp only [hp] at h
          cases a <;> cases b <;> simp at h
          all_goals simpa [models_cons, ComparisonShape.subst, and_assoc] using ih h
        | some pair =>
          rcases pair with ⟨v, t⟩
          simp only [hp] at h
          split at h
          · cases h
          · rename_i hv
            cases hs : unify fuel allowed (mapPairs (replace v t) rest) <;>
              simp [hs, bind, pure, RunResult.bind] at h
            subst s
            have hh := models_extend (by simpa using hv) (ih hs)
            rcases (choose_spec hp).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact hh
            · simpa [models_cons, eq_comm] using hh


theorem factor_extend {ρ : TypeVar → ComparisonShape} {v : TypeVar} {t : ComparisonShape} {s : Assignment}
    (h : ∀ w, (action s w).subst ρ = ρ w) (hv : ρ v = t.subst ρ) :
    ∀ w, (action ((v, t.subst (action s)) :: s) w).subst ρ = ρ w := by
  intro w
  rw [action_cons]
  split
  · rename_i he
    have he : w = v := eq_of_beq he
    subst w
    rw [subst_comp]
    exact (subst_congr t (fun w _ => h w)).trans hv.symm
  · exact h w


/-- Every solution factors through the returned symbolic substitution. -/
theorem unify_factor {fuel allowed ps s} (h : unify fuel allowed ps = .success s)
    {ρ : TypeVar → ComparisonShape} (hm : Models ps ρ) :
    ∀ v, (action s v).subst ρ = ρ v := by
  induction fuel generalizing ps s with
  | zero => cases h
  | succ fuel ih =>
    cases ps with
    | nil =>
      simp only [unify, RunResult.success.injEq] at h
      subst s
      simp [action, ComparisonShape.subst]
    | cons pair rest =>
      rcases pair with ⟨a, b⟩
      simp only [unify] at h
      split at h
      case isTrue he => exact ih h (models_cons.mp hm).2
      case isFalse he =>
        cases hp : choose allowed a b with
        | none =>
          simp only [hp] at h
          cases a <;> cases b <;> simp at h
          all_goals apply ih h
          all_goals simpa [models_cons, ComparisonShape.subst, and_assoc] using hm
        | some pair =>
          rcases pair with ⟨v, t⟩
          simp only [hp] at h
          split at h
          · cases h
          · cases hs : unify fuel allowed (mapPairs (replace v t) rest) <;>
              simp [hs, bind, pure, RunResult.bind] at h
            subst s
            have hv : ρ v = t.subst ρ := by
              rcases (choose_spec hp).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact (models_cons.mp hm).1
              · exact (models_cons.mp hm).1.symm
            exact factor_extend (ih hs (models_replace (models_cons.mp hm).2 hv)) hv


/-- A successful declared-shape substitution decides exactly its rigid shape
consequences, without choosing concrete shapes for its remaining names. -/
theorem unify_equivalent {fuel allowed Δ s} (h : unify fuel allowed (ComparisonShape.pairs Δ) = .success s)
    (a b : ComparisonShape) :
    ComparisonShape.Equivalent Δ a b ↔ a.subst (action s) = b.subst (action s) := by
  constructor
  · intro he
    exact he (action s) (unify_sound h)
  · intro he ρ hm
    have eval_normalized (t : ComparisonShape) :
        (t.subst (action s)).subst ρ = t.subst ρ :=
      (subst_comp t (action s) ρ).trans
        (subst_congr t (fun v _ => unify_factor h hm v))
    exact (eval_normalized a).symm.trans
      ((congrArg (ComparisonShape.subst ρ) he).trans (eval_normalized b))

theorem unify_fixes {fuel allowed ps s} (h : unify fuel allowed ps = .success s) :
    Fixes allowed (action s) := by
  induction fuel generalizing ps s with
  | zero => cases h
  | succ fuel ih =>
    cases ps with
    | nil =>
      simp only [unify, RunResult.success.injEq] at h
      subst s
      simp [Fixes, action]
    | cons pair rest =>
      rcases pair with ⟨a, b⟩
      simp only [unify] at h
      split at h
      case isTrue he => exact ih h
      case isFalse he =>
        cases hp : choose allowed a b with
        | none =>
          simp only [hp] at h
          cases a <;> cases b <;> simp at h
          all_goals exact ih h
        | some pair =>
          rcases pair with ⟨v, t⟩
          simp only [hp] at h
          split at h
          · cases h
          · cases hs : unify fuel allowed (mapPairs (replace v t) rest) <;>
              simp [hs, bind, pure, RunResult.bind] at h
            subst s
            intro w hw
            have hn : w ≠ v := by
              intro he
              exact Bool.noConfusion (hw.symm.trans (he ▸ (choose_spec hp).1))
            simpa [hn] using ih hs w hw


def size : ComparisonShape → Nat
  | .var _ | .unit | .credit => 1
  | .prod a b | .sum a b | .fn a b => size a + size b + 1

theorem size_pos (t : ComparisonShape) : 0 < size t := by
  induction t <;> simp_all [size]

theorem occurs_le (t : ComparisonShape) (ρ : TypeVar → ComparisonShape) {v : TypeVar}
    (hv : v ∈ t.vars) : size (ρ v) ≤ size (t.subst ρ) := by
  induction t <;> simp_all [ComparisonShape.vars, ComparisonShape.subst, size]
  all_goals rcases hv with hv | hv <;> simp_all <;> omega


theorem occurs_lt (t : ComparisonShape) (ρ : TypeVar → ComparisonShape) {v : TypeVar}
    (hv : v ∈ t.vars) (hne : t ≠ .var v) : size (ρ v) < size (t.subst ρ) := by
  cases t <;> simp_all [ComparisonShape.vars, ComparisonShape.subst, size]
  all_goals rcases hv with hv | hv <;> have hle := occurs_le _ ρ hv <;> omega

theorem mem_vars_subst (t : ComparisonShape) (ρ : TypeVar → ComparisonShape) (w : TypeVar) :
    w ∈ (t.subst ρ).vars ↔ ∃ v ∈ t.vars, w ∈ (ρ v).vars := by
  induction t <;> simp_all [ComparisonShape.subst, ComparisonShape.vars, or_and_right, exists_or]


theorem unify_not_rejected {allowed ps ρ} (hm : Models ps ρ) (hf : Fixes allowed ρ)
    (fuel : Nat) : unify fuel allowed ps = .exhausted ∨
      ∃ s, unify fuel allowed ps = .success s := by
  induction fuel generalizing ps with
  | zero => exact .inl rfl
  | succ fuel ih =>
    cases ps with
    | nil => exact .inr ⟨[], rfl⟩
    | cons pair rest =>
      rcases pair with ⟨a, b⟩
      by_cases he : a = b
      · simpa [unify, he] using ih (models_cons.mp hm).2
      cases hp : choose allowed a b with
      | some pair =>
        rcases pair with ⟨v, t⟩
        have hv : ρ v = t.subst ρ := by
          rcases (choose_spec hp).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact (models_cons.mp hm).1
          · exact (models_cons.mp hm).1.symm
        have hn : t ≠ .var v := by
          rcases (choose_spec hp).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Ne.symm he
          · exact he
        have ho : v ∉ t.vars := by
          intro ho
          have hs := occurs_lt t ρ ho hn
          rw [hv] at hs
          exact (Nat.lt_irrefl _) hs
        rcases ih (models_replace (models_cons.mp hm).2 hv) with hh | ⟨s, hs⟩
        · exact .inl (by simp [unify, he, hp, ho, hh, bind, RunResult.bind])
        · exact .inr ⟨(v, t.subst (action s)) :: s,
            by simp [unify, he, hp, ho, hs, bind, pure, RunResult.bind]⟩
      | none =>
        have hab := (models_cons.mp hm).1
        have hr := (models_cons.mp hm).2
        cases a <;> cases b <;> simp_all [choose, ComparisonShape.subst, Fixes]
        all_goals try (repeat' split at hp <;> simp_all)
        all_goals
          have hh := ih (models_cons.mpr ⟨hm.1, models_cons.mpr ⟨hm.2, hr⟩⟩)
          have hne := not_and.mpr he
          simpa [unify, choose, hne] using hh

namespace Measure

def vars : Pairs → Finset TypeVar
  | [] => ∅
  | (a, b) :: rest => a.vars.toFinset ∪ b.vars.toFinset ∪ vars rest

def nodes : Pairs → Nat
  | [] => 0
  | (a, b) :: rest => size a + size b + nodes rest

def rank (ps : Pairs) : Nat × Nat := ((vars ps).card, nodes ps)

abbrev Lt (ps qs : Pairs) : Prop := Prod.Lex (· < ·) (· < ·) (rank ps) (rank qs)

theorem mem_vars (ps : Pairs) (v : TypeVar) :
    v ∈ vars ps ↔ ∃ a b, (a, b) ∈ ps ∧ (v ∈ a.vars ∨ v ∈ b.vars) := by
  induction ps with
  | nil => simp [vars]
  | cons pair rest ih =>
    rcases pair with ⟨a, b⟩
    simp only [vars, Finset.mem_union, List.mem_toFinset, ih, List.mem_cons, Prod.mk.injEq]
    aesop

theorem lt_tail (a b : ComparisonShape) (ps : Pairs) : Lt ps ((a, b) :: ps) := by
  have hcard : (vars ps).card ≤ (vars ((a, b) :: ps)).card :=
    Finset.card_le_card Finset.subset_union_right
  apply Prod.lex_def.mpr
  rcases lt_or_eq_of_le hcard with hc | hc
  · exact .inl hc
  · refine .inr ⟨hc, ?_⟩
    change nodes ps < size a + size b + nodes ps
    have ha := size_pos a
    omega

theorem subst_vars_subset (ps : Pairs) (ρ : TypeVar → ComparisonShape) (S : Finset TypeVar)
    (h : ∀ v ∈ vars ps, (ρ v).vars.toFinset ⊆ S) : vars (mapPairs ρ ps) ⊆ S := by
  intro v hv
  obtain ⟨a, b, hab, hv⟩ := (mem_vars _ _).mp hv
  obtain ⟨⟨x, y⟩, hxy, he⟩ := List.mem_map.mp hab
  cases he
  simp only [mem_vars_subst] at hv
  exact hv.elim
    (fun ⟨w, hw, hv⟩ => h w ((mem_vars _ _).mpr ⟨x, y, hxy, .inl hw⟩)
      (List.mem_toFinset.mpr hv))
    (fun ⟨w, hw, hv⟩ => h w ((mem_vars _ _).mpr ⟨x, y, hxy, .inr hw⟩)
      (List.mem_toFinset.mpr hv))

theorem lt_replace (v : TypeVar) (t : ComparisonShape) (ps : Pairs) (hv : v ∉ t.vars) :
    Lt (mapPairs (replace v t) ps) ((.var v, t) :: ps) := by
  let S := vars ((.var v, t) :: ps)
  have hsub : vars (mapPairs (replace v t) ps) ⊆ S.erase v := by
    apply subst_vars_subset
    intro w hw
    by_cases he : w = v
    · subst w
      simp only [replace, beq_self_eq_true, ↓reduceIte]
      exact fun z hz => Finset.mem_erase.mpr ⟨fun he => hv (he ▸ List.mem_toFinset.mp hz),
        Finset.mem_union_left _ (Finset.mem_union_right _ hz)⟩
    · simpa [replace, he, ComparisonShape.vars, S, vars] using And.intro he (Or.inr hw)
  exact Prod.lex_def.mpr (.inl ((Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem (by simp [S, vars, ComparisonShape.vars]))))

theorem rank_swap (a b : ComparisonShape) (ps : Pairs) :
    rank ((a, b) :: ps) = rank ((b, a) :: ps) := by
  simp [rank, vars, nodes, Finset.union_comm, Nat.add_comm]

theorem lt_replace_right (v : TypeVar) (t : ComparisonShape) (ps : Pairs) (hv : v ∉ t.vars) :
    Lt (mapPairs (replace v t) ps) ((t, .var v) :: ps) := by
  simpa only [Lt, ← rank_swap t (.var v) ps] using lt_replace v t ps hv

theorem lt_decompose {a b c d x y : ComparisonShape} (ps : Pairs)
    (hx : x.vars = a.vars ++ b.vars) (hy : y.vars = c.vars ++ d.vars)
    (hxs : size x = size a + size b + 1) (hys : size y = size c + size d + 1) :
    Lt ((a, c) :: (b, d) :: ps) ((x, y) :: ps) := by
  apply Prod.lex_def.mpr
  right
  constructor
  · change (a.vars.toFinset ∪ c.vars.toFinset ∪
        (b.vars.toFinset ∪ d.vars.toFinset ∪ vars ps)).card =
      (x.vars.toFinset ∪ y.vars.toFinset ∪ vars ps).card
    rw [hx, hy, List.toFinset_append, List.toFinset_append]
    congr 1
    ac_rfl
  · change size a + size c + (size b + size d + nodes ps) < size x + size y + nodes ps
    omega

theorem wellFounded : WellFounded Lt :=
  InvImage.wf rank (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

end Measure

theorem unify_eventually (allowed : TypeVar → Bool) (ps : Pairs) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, unify fuel allowed ps = result := by
  induction ps using Measure.wellFounded.induction with
  | h ps ih =>
    cases ps with
    | nil =>
      exact ⟨1, .success [], by simp,
        fun fuel hf => by cases fuel <;> simp_all [unify]⟩
    | cons pair ps =>
      rcases pair with ⟨a, b⟩
      have advance (qs : Pairs) (hlt : Measure.Lt qs ((a, b) :: ps))
          (he : ∀ fuel, unify (fuel + 1) allowed ((a, b) :: ps) = unify fuel allowed qs) :
          ∃ n result, result ≠ .exhausted ∧
            ∀ fuel ≥ n, unify fuel allowed ((a, b) :: ps) = result := by
        obtain ⟨n, result, hn, hresult⟩ := ih qs hlt
        refine ⟨n + 1, result, hn, fun fuel hf => ?_⟩
        cases fuel with
        | zero => omega
        | succ fuel => exact (he fuel).trans (hresult fuel (by omega))
      by_cases he : a = b
      · exact advance ps (Measure.lt_tail a b ps) (fun fuel => by simp [unify, he])
      have reject (reason : String)
          (hr : ∀ fuel, unify (fuel + 1) allowed ((a, b) :: ps) = .rejected reason) :
          ∃ n result, result ≠ .exhausted ∧
            ∀ fuel ≥ n, unify fuel allowed ((a, b) :: ps) = result := by
        refine ⟨1, .rejected reason, by simp, fun fuel hf => ?_⟩
        cases fuel with
        | zero => omega
        | succ fuel => exact hr fuel
      cases hp : choose allowed a b with
      | none =>
        cases a <;> cases b
        all_goals first
          | exact False.elim (he rfl)
          | solve |
              apply reject "incompatible or fixed type shapes"
              intro fuel
              simp [unify, he, hp]
          | refine advance _ (Measure.lt_decompose ps rfl rfl rfl rfl) ?_
        all_goals intro fuel; simp [unify, he, hp]
      | some pair =>
        rcases pair with ⟨v, t⟩
        by_cases ho : v ∈ t.vars
        · exact reject "cyclic finite shape equation" (fun fuel => by simp [unify, he, hp, ho])
        have hlt : Measure.Lt (mapPairs (replace v t) ps) ((a, b) :: ps) := by
          rcases (choose_spec hp).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Measure.lt_replace v _ ps ho
          · exact Measure.lt_replace_right v _ ps ho
        obtain ⟨n, result, hn, hresult⟩ := ih _ hlt
        cases result with
        | exhausted => exact False.elim (hn rfl)
        | rejected reason =>
          refine ⟨n + 1, .rejected reason, by simp, fun fuel hf => ?_⟩
          cases fuel with
          | zero => omega
          | succ fuel => simp [unify, he, hp, ho, hresult fuel (by omega), bind, RunResult.bind]
        | success s =>
          refine ⟨n + 1, .success ((v, t.subst (action s)) :: s), by simp, fun fuel hf => ?_⟩
          cases fuel with
          | zero => omega
          | succ fuel =>
            simp [unify, he, hp, ho, hresult fuel (by omega), bind, pure, RunResult.bind]

theorem unify_complete {allowed ps ρ} (hm : Models ps ρ) (hf : Fixes allowed ρ) :
    ∃ n s, ∀ fuel ≥ n, unify fuel allowed ps = .success s := by
  obtain ⟨n, result, hn, hresult⟩ := unify_eventually allowed ps
  rcases unify_not_rejected hm hf n with he | ⟨s, hs⟩
  · exact False.elim (hn ((hresult n le_rfl).symm.trans he))
  · exact ⟨n, s, fun fuel hf => (hresult fuel hf).trans ((hresult n le_rfl).symm.trans hs)⟩

theorem unify_rejected {fuel allowed ps reason} (h : unify fuel allowed ps = .rejected reason) :
    ¬ ∃ ρ, Models ps ρ ∧ Fixes allowed ρ := by
  rintro ⟨ρ, hm, hf⟩
  rcases unify_not_rejected hm hf fuel with he | ⟨s, hs⟩ <;> simp [h] at *

theorem unify_monotone {small large allowed ps s} (hle : small ≤ large)
    (h : unify small allowed ps = .success s) : unify large allowed ps = .success s := by
  induction small generalizing large ps s with
  | zero => cases h
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      have hle' : small ≤ large := by omega
      cases ps with
      | nil => simpa only [unify] using h
      | cons pair rest =>
        rcases pair with ⟨a, b⟩
        simp only [unify] at h ⊢
        split at h
        case isTrue he => simpa only [he, ↓reduceIte] using ih hle' h
        case isFalse he =>
          simp only [he]
          cases hp : choose allowed a b with
          | none =>
            simp only [hp] at h ⊢
            cases a <;> cases b <;> simp at h ⊢
            all_goals exact ih hle' h
          | some pair =>
            rcases pair with ⟨v, t⟩
            simp only [hp] at h ⊢
            split at h
            · cases h
            · rename_i ho
              simp only [ho]
              cases hs : unify small allowed (mapPairs (replace v t) rest) <;>
                simp [hs, bind, pure, RunResult.bind] at h
              subst s
              simp [ih hle' hs, bind, pure, RunResult.bind]

theorem subst_vars_subset (t : ComparisonShape) (ρ : TypeVar → ComparisonShape)
    (S : Finset TypeVar) (h : ∀ v ∈ t.vars, (ρ v).vars.toFinset ⊆ S) :
    (t.subst ρ).vars.toFinset ⊆ S := by
  intro w hw
  obtain ⟨v, hv, hw⟩ := (mem_vars_subst t ρ w).mp (List.mem_toFinset.mp hw)
  exact h v hv (List.mem_toFinset.mpr hw)

/-- A successful unifier changes only names present in the input and introduces
no new names. This applies even when the allowed set is larger than the input. -/
theorem unify_support {fuel allowed ps s} (h : unify fuel allowed ps = .success s)
    (S : Finset TypeVar) (hp : Measure.vars ps ⊆ S) :
    (∀ v ∉ S, action s v = .var v) ∧
      ∀ v ∈ S, (action s v).vars.toFinset ⊆ S := by
  induction fuel generalizing ps s with
  | zero => cases h
  | succ fuel ih =>
    cases ps with
    | nil =>
      simp only [unify, RunResult.success.injEq] at h
      subst s
      simp [action, ComparisonShape.vars]
    | cons pair rest =>
      rcases pair with ⟨a, b⟩
      have hr : Measure.vars rest ⊆ S := Finset.Subset.trans Finset.subset_union_right hp
      simp only [unify] at h
      split at h
      case isTrue he => exact ih h hr
      case isFalse he =>
        cases hc : choose allowed a b with
        | none =>
          simp only [hc] at h
          cases a <;> cases b <;> simp at h
          all_goals
            apply ih h
            intro v hv
            apply hp
            simp only [Measure.vars, ComparisonShape.vars, List.toFinset_append,
              Finset.mem_union] at hv ⊢
            tauto
        | some pair =>
          rcases pair with ⟨v, t⟩
          simp only [hc] at h
          split at h
          · cases h
          · cases hs : unify fuel allowed (mapPairs (replace v t) rest) <;>
              simp [hs, bind, pure, RunResult.bind] at h
            rename_i s'
            subst s
            have hv : v ∈ S := by
              apply hp
              rcases (choose_spec hc).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
                simp [Measure.vars, ComparisonShape.vars]
            have ht : t.vars.toFinset ⊆ S := by
              intro w hw
              apply hp
              rcases (choose_spec hc).2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
                simp_all [Measure.vars, ComparisonShape.vars]
            have hsub : Measure.vars (mapPairs (replace v t) rest) ⊆ S := by
              apply Measure.subst_vars_subset
              intro w hw
              by_cases hwv : w = v
              · simpa [replace, hwv] using ht
              · simpa [replace, hwv, ComparisonShape.vars] using hr hw
            obtain ⟨hfixed, hclosed⟩ := ih hs hsub
            have hts : (t.subst (action s')).vars.toFinset ⊆ S := by
              apply subst_vars_subset
              exact fun w hw => hclosed w (ht (List.mem_toFinset.mpr hw))
            constructor
            · intro w hw
              have hn : w ≠ v := fun he => hw (he ▸ hv)
              simpa [hn] using hfixed w hw
            · intro w hw
              by_cases hn : w = v
              · simpa [hn] using hts
              · simpa [hn] using hclosed w hw

theorem models_mapPairs (ps : Pairs) (σ ρ : TypeVar → ComparisonShape) :
    Models (mapPairs σ ps) ρ ↔ Models ps (fun v => (σ v).subst ρ) := by
  simp only [Models, mapPairs, List.forall_mem_map, subst_comp]

theorem models_postcompose {ps ρ} (h : Models ps ρ) (σ : TypeVar → ComparisonShape) :
    Models ps (fun v => (ρ v).subst σ) := by
  intro p hp
  simpa only [subst_comp] using congrArg (ComparisonShape.subst σ) (h p hp)

theorem prepare_solved_iff {fuel p s} : prepare fuel p = .success (.solved s) ↔
    unify fuel (fun _ => true) (ComparisonShape.pairs p.assumptions) = .success s.fixed ∧
    unify fuel (sourceAllowed p) (mapPairs s.fixedShapes (sourcePairs p)) = .success s.source := by
  cases hf : unify fuel (fun _ => true) (ComparisonShape.pairs p.assumptions) <;>
    simp [prepare, hf, bind, RunResult.bind]
  rename_i fixed
  cases hs : unify fuel (sourceAllowed p) (mapPairs (action fixed) (sourcePairs p)) <;>
    simp [pure]
  constructor
  · rintro rfl
    exact ⟨rfl, hs⟩
  · rintro ⟨rfl, hh⟩
    cases s
    simpa [Solved.fixedShapes, hs] using hh
  all_goals rintro rfl; simp [Solved.fixedShapes, hs]

theorem prepare_infeasible_iff {fuel p} : prepare fuel p = .success .infeasibleAssumptions ↔
    ∃ reason, unify fuel (fun _ => true) (ComparisonShape.pairs p.assumptions) = .rejected reason := by
  cases hf : unify fuel (fun _ => true) (ComparisonShape.pairs p.assumptions) <;>
    simp [prepare, hf, bind, RunResult.bind]
  rename_i fixed
  cases hs : unify fuel (sourceAllowed p) (mapPairs (action fixed) (sourcePairs p)) <;>
    simp [pure]

/-- An infeasible result concerns only declared assumptions. It is not a
rejection of the source subsumption query. -/
theorem prepare_infeasible {fuel p} (h : prepare fuel p = .success .infeasibleAssumptions) :
    ¬ ∃ ρ, ComparisonShape.Models p.assumptions ρ := by
  obtain ⟨reason, hr⟩ := prepare_infeasible_iff.mp h
  rintro ⟨ρ, hm⟩
  exact unify_rejected hr ⟨ρ, hm, by simp [Fixes]⟩

theorem prepare_fixed_equivalent {fuel p s} (h : prepare fuel p = .success (.solved s))
    (a b : ComparisonShape) :
    ComparisonShape.Equivalent p.assumptions a b ↔ a.subst s.fixedShapes = b.subst s.fixedShapes :=
  unify_equivalent (prepare_solved_iff.mp h).1 a b

theorem prepare_source_fixes {fuel p s} (h : prepare fuel p = .success (.solved s)) :
    Fixes (sourceAllowed p) (action s.source) :=
  unify_fixes (prepare_solved_iff.mp h).2

theorem prepare_sound {fuel p s} (h : prepare fuel p = .success (.solved s)) :
    ComparisonShape.Models p.assumptions s.resolveAll ∧ Models (sourcePairs p) s.resolveAll := by
  obtain ⟨hf, hs⟩ := prepare_solved_iff.mp h
  exact ⟨models_postcompose (unify_sound hf) (action s.source),
    (models_mapPairs _ _ _).mp (unify_sound hs)⟩

theorem prepare_solved_monotone {small large p s} (hle : small ≤ large)
    (h : prepare small p = .success (.solved s)) : prepare large p = .success (.solved s) :=
  prepare_solved_iff.mpr ⟨unify_monotone hle (prepare_solved_iff.mp h).1,
    unify_monotone hle (prepare_solved_iff.mp h).2⟩

theorem prepare_eventually (p : SchemePreparation.Prepared) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, prepare fuel p = result := by
  obtain ⟨n, fixedResult, hn, hfixed⟩ :=
    unify_eventually (fun _ => true) (ComparisonShape.pairs p.assumptions)
  cases fixedResult with
  | exhausted => exact False.elim (hn rfl)
  | rejected reason =>
    exact ⟨n, .success .infeasibleAssumptions, by simp,
      fun fuel hf => by simp [prepare, hfixed fuel hf]⟩
  | success fixed =>
    obtain ⟨m, sourceResult, hm, hsource⟩ :=
      unify_eventually (sourceAllowed p) (mapPairs (action fixed) (sourcePairs p))
    cases sourceResult with
    | exhausted => exact False.elim (hm rfl)
    | rejected reason =>
      exact ⟨max n m, .rejected reason, by simp, fun fuel hf => by
        simp [prepare, hfixed fuel ((Nat.le_max_left _ _).trans hf),
          hsource fuel ((Nat.le_max_right _ _).trans hf), bind, RunResult.bind]⟩
    | success source =>
      exact ⟨max n m, .success (.solved ⟨fixed, source⟩), by simp, fun fuel hf => by
        simp [prepare, hfixed fuel ((Nat.le_max_left _ _).trans hf),
          hsource fuel ((Nat.le_max_right _ _).trans hf), bind, pure, RunResult.bind]⟩

theorem prepare_residual_complete {initial p fixed ρ}
    (hf : unify initial (fun _ => true) (ComparisonShape.pairs p.assumptions) = .success fixed)
    (hm : Models (mapPairs (action fixed) (sourcePairs p)) ρ)
    (hρ : Fixes (sourceAllowed p) ρ) :
    ∃ n source, ∀ fuel ≥ n, prepare fuel p = .success (.solved ⟨fixed, source⟩) := by
  obtain ⟨n, source, hs⟩ := unify_complete hm hρ
  exact ⟨max initial n, source, fun fuel h => prepare_solved_iff.mpr
    ⟨unify_monotone ((Nat.le_max_left _ _).trans h) hf,
      hs fuel ((Nat.le_max_right _ _).trans h)⟩⟩

theorem sourceAllowed_iff (p : SchemePreparation.Prepared) (v : TypeVar) :
    sourceAllowed p v = true ↔ ∃ n, v = .flex n ∧ p.firstType ≤ n ∧ n < p.nextType := by
  cases v <;> simp [sourceAllowed]

/-- Declared shape classes stay frozen after source unification. The premise
holds automatically for the public scope-preserving preparation below. -/
theorem prepare_resolve_fixed {fuel p s v} (h : prepare fuel p = .success (.solved s))
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions), sourceAllowed p w = false)
    (hv : sourceAllowed p v = false) : s.resolveAll v = s.fixedShapes v := by
  obtain ⟨hfixed, himages⟩ := unify_support (prepare_solved_iff.mp h).1
    (Measure.vars (ComparisonShape.pairs p.assumptions)) Finset.Subset.rfl
  change (action s.fixed v).subst (action s.source) = action s.fixed v
  refine (subst_congr _ ?_).trans (subst_id _)
  intro w hw
  apply prepare_source_fixes h
  by_cases hmem : v ∈ Measure.vars (ComparisonShape.pairs p.assumptions)
  · exact hscope w (himages v hmem (List.mem_toFinset.mpr hw))
  · rw [hfixed v hmem] at hw
    have he : w = v := by simpa [ComparisonShape.vars] using hw
    exact he ▸ hv

theorem prepare_resolve_source {fuel p s v} (h : prepare fuel p = .success (.solved s))
    (hscope : ∀ w ∈ Measure.vars (ComparisonShape.pairs p.assumptions), sourceAllowed p w = false)
    (hv : sourceAllowed p v = true) : s.resolveAll v = action s.source v := by
  have hmem : v ∉ Measure.vars (ComparisonShape.pairs p.assumptions) := by
    intro hm
    exact Bool.noConfusion (hv.symm.trans (hscope v hm))
  have hfixed := (unify_support (prepare_solved_iff.mp h).1
    (Measure.vars (ComparisonShape.pairs p.assumptions)) Finset.Subset.rfl).1 v hmem
  simp [Solved.resolveAll, Solved.fixedShapes, hfixed, ComparisonShape.subst]

@[simp] theorem mem_vars_ofTy (a : Ty) (v : TypeVar) :
    v ∈ (ComparisonShape.ofTy a).vars ↔ v ∈ a.typeVars := by
  induction a <;> simp_all [ComparisonShape.ofTy, ComparisonShape.vars, TypeExpr.typeVars]

theorem vars_pairs (Δ : Bounds) : Measure.vars (ComparisonShape.pairs Δ) = Δ.typeVars := by
  induction Δ with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> ext v <;>
      simp_all [ComparisonShape.pairs, Measure.vars, ComparisonShape.vars,
        Constraint.typeVars]

private theorem constraint_subst_vars (c : Constraint) (σ : Substitution) (v : TypeVar) :
    v ∈ (σ.constraint c).typeVars ↔ ∃ w ∈ c.typeVars, v ∈ (σ.type w).typeVars := by
  cases c <;> simp [Substitution.constraint, Constraint.subst, Constraint.typeVars,
    Substitution.ty, TypeExpr.mem_typeVars_subst, or_and_right, exists_or]
  rename_i w a
  cases w with
  | rigid n => simp [Substitution.type, TypeExpr.typeVars, TypeExpr.mem_typeVars_subst]
  | flex n =>
    cases he : σ.types.lookup n <;>
      simp [he, Substitution.type, TypeExpr.typeVars, TypeExpr.mem_typeVars_subst]

private theorem bounds_typeVars_append (cs ds : Bounds) :
    (cs ++ ds).typeVars = cs.typeVars ∪ ds.typeVars := by
  ext v
  simp [Bounds.mem_typeVars_iff, or_and_right, exists_or]

private theorem wellFormedBounds_typeVars (a : Ty) : a.wellFormedBounds.typeVars = ∅ := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, Constraint.typeVars, bounds_typeVars_append,
    show Bounds.typeVars [] = ∅ from rfl]

private theorem assumptions_typeVars (cs : Bounds) : cs.assumptions.typeVars = cs.typeVars := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c <;> ext v <;>
      simp_all [Bounds.assumptions, Constraint.assumptions, Constraint.typeVars,
        TypeExpr.typeVars, wellFormedBounds_typeVars, bounds_typeVars_append]
    tauto

theorem prepared_original_fixed (ambient : Bounds) (source target : Scheme)
    (v : TypeVar) (hv : v ∈ SchemePreparation.originalTypeIds ambient source target) :
    sourceAllowed (SchemePreparation.prepare ambient source target) v = false := by
  have hi := SchemePreparation.original_type_lt_first hv
  cases v <;> simp_all [sourceAllowed, TypeVar.index, Nat.not_le_of_gt]

theorem prepared_assumptions_fixed (ambient : Bounds) (source target : Scheme) :
    ∀ v ∈ Measure.vars (ComparisonShape.pairs (SchemePreparation.prepare ambient source target).assumptions),
      sourceAllowed (SchemePreparation.prepare ambient source target) v = false := by
  let p := SchemePreparation.prepare ambient source target
  change ∀ v ∈ Measure.vars (ComparisonShape.pairs p.assumptions), sourceAllowed p v = false
  have original_fixed (v : TypeVar) (hv : v ∈ SchemePreparation.originalTypeIds ambient source target) :
      sourceAllowed p v = false := prepared_original_fixed ambient source target v hv
  have target_fixed (v : TypeVar) (hv : v ∈ target.bounds.typeVars) :
      ∀ w ∈ (p.targetRenaming.type v).typeVars, sourceAllowed p w = false := by
    have hvo : v ∈ SchemePreparation.originalTypeIds ambient source target := by
      simp only [SchemePreparation.originalTypeIds, List.mem_append]
      have hv' := (Bounds.mem_typeVariables target.bounds v).mpr hv
      tauto
    cases v with
    | rigid n => simp [p, SchemePreparation.prepare, Substitution.type, TypeExpr.typeVars, sourceAllowed]
    | flex n =>
      cases he : p.targetRenaming.types.lookup n with
      | none => simpa [Substitution.type, he, TypeExpr.typeVars] using original_fixed (.flex n) hvo
      | some a =>
        obtain ⟨i, hi, ha⟩ := lookup_fresh_some (xs := target.typeParams)
          (f := fun i => (.var (.rigid ((source.subsumptionIndices ambient target).1 + i)) : Ty)) he
        simp [Substitution.type, he, ha, TypeExpr.typeVars, sourceAllowed]
  intro v hv
  rw [vars_pairs] at hv
  change v ∈ (ambient ++ (p.targetRenaming.bounds target.bounds).assumptions).typeVars at hv
  rw [bounds_typeVars_append, assumptions_typeVars] at hv
  rcases Finset.mem_union.mp hv with hv | hv
  · apply original_fixed
    simp only [SchemePreparation.originalTypeIds, List.mem_append]
    exact .inr ((Bounds.mem_typeVariables ambient v).mpr hv)
  · obtain ⟨c, hc, hv⟩ := (Bounds.mem_typeVars_iff _ _).mp hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨w, hw, hv⟩ := (constraint_subst_vars d p.targetRenaming v).mp hv
    exact target_fixed w ((Bounds.mem_typeVars_iff _ _).mpr ⟨d, hd, hw⟩) v hv

theorem prepared_resolve_fixed {fuel ambient source target s v}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved s))
    (hv : sourceAllowed (SchemePreparation.prepare ambient source target) v = false) :
    s.resolveAll v = s.fixedShapes v :=
  prepare_resolve_fixed h (prepared_assumptions_fixed ambient source target) hv

theorem prepared_resolve_source {fuel ambient source target s v}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved s))
    (hv : sourceAllowed (SchemePreparation.prepare ambient source target) v = true) :
    s.resolveAll v = action s.source v :=
  prepare_resolve_source h (prepared_assumptions_fixed ambient source target) hv

theorem prepared_original_resolved {fuel ambient source target s v}
    (h : prepare fuel (SchemePreparation.prepare ambient source target) = .success (.solved s))
    (hv : v ∈ SchemePreparation.originalTypeIds ambient source target) :
    s.resolveAll v = s.fixedShapes v :=
  prepared_resolve_fixed h (prepared_original_fixed ambient source target v hv)

end ModalityInference.ComparisonShapeSolver
