import ModalityInference.Proofs.ComparisonAlgebra

/-! A limitation of reconstructing finite type witnesses from bounded finite
semantic carriers. The declared bounds have no finite shape model, every
finite ordered interpretation admits a fixed-point candidate, and no finite
comparison type has an algebraic fixed-point derivation. This distinguishes
finite-term realizability from satisfaction in a bounded semantic abstraction;
it is not an impossibility result for constraint propagation or proof grammars. -/

namespace ModalityInference.ComparisonFiniteGraphLimitation

def observe : CompareTy → Set (Bool × Nat)
  | .var v => if v = .rigid 1 then Set.univ else ∅
  | .unit | .credit => ∅
  | .prod a _ => fun p => match p.2 with | 0 => p.1 = true | n + 1 => observe a (p.1, n)
  | .sum _ _ | .fn _ _ => ∅
  | .modal a _ => observe a
  | .join a b => observe a ∪ observe b
  | .meet a b => observe a ∩ observe b

private theorem shaped_sound {Δ a b} (h : ShapedSubtype Δ a b)
    (hΔ : ∀ x y, Constraint.sub x y ∈ Δ → observe (.ofTy x) ⊆ observe (.ofTy y)) :
    observe a ⊆ observe b := by
  induction h with
  | refl => exact Set.Subset.rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | bound h => exact hΔ _ _ h
  | identity | identityRev | compose | composeRev => exact Set.Subset.rfl
  | congr _ _ ih => exact ih
  | prod _ _ ih₁ _ =>
      rintro ⟨s, n⟩ hn
      cases n with
      | zero => exact hn
      | succ n => exact ih₁ hn
  | sum | fn => exact Set.Subset.rfl
  | joinLeft => exact Set.subset_union_left
  | joinRight => exact Set.subset_union_right
  | joinLeast _ _ ih₁ ih₂ => exact Set.union_subset ih₁ ih₂
  | meetLeft => exact Set.inter_subset_left
  | meetRight => exact Set.inter_subset_right
  | meetGreatest _ _ ih₁ ih₂ => exact Set.subset_inter ih₁ ih₂

private theorem equation_sound {Δ a b} (h : ComparisonAlgebra.Equation Δ a b) :
    observe a = observe b := by
  cases h with
  | distrib p =>
      cases p <;> ext n <;>
        simp only [ComparisonAlgebra.typeOp, Bool.false_eq_true, Bool.not_false,
          Bool.not_true, if_false, if_true, observe, Set.mem_union, Set.mem_inter_iff]
      · tauto
      · tauto
  | modal p => cases p <;> rfl
  | scalar p =>
      cases p <;> simp [ComparisonAlgebra.typeOp, observe]
  | prod p =>
      cases p
      · ext ⟨s, n⟩
        cases n with
        | zero => change (s = true ∧ s = true ↔ s = true); tauto
        | succ n => rfl
      · ext ⟨s, n⟩
        cases n with
        | zero => change (s = true ∨ s = true ↔ s = true); tauto
        | succ n => rfl
  | sum p | fn p =>
      cases p <;> simp [ComparisonAlgebra.typeOp, observe]

private theorem algebra_sound {Δ a b} (h : AlgebraSubtype Δ a b)
    (hΔ : ∀ x y, Constraint.sub x y ∈ Δ → observe (.ofTy x) ⊆ observe (.ofTy y)) :
    observe a ⊆ observe b := by
  induction h with
  | shaped h => exact shaped_sound h hΔ
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | equation h => exact (equation_sound h).subset
  | equationRev h => exact (equation_sound h).symm.subset
  | congr _ _ ih => exact ih
  | prod _ _ ih₁ _ =>
      rintro ⟨s, n⟩ hn
      cases n with
      | zero => exact hn
      | succ n => exact ih₁ hn
  | sum | fn => exact Set.Subset.rfl
  | joinLeast _ _ ih₁ ih₂ => exact Set.union_subset ih₁ ih₂
  | meetGreatest _ _ ih₁ ih₂ => exact Set.subset_inter ih₁ ih₂
  | clamp _ _ _ _ _ _ ih₂ =>
      intro n hn
      exact ⟨Or.inl hn, ih₂ hn⟩
  | clampRev _ _ _ _ _ ih₁ _ =>
      intro n hn
      exact hn.1.elim id (fun hb => ih₁ hb)

def A : Ty := .var (.rigid 0)
def C : Ty := .var (.rigid 1)
def F (a : Ty) : Ty := .prod a .unit

def bounds : Bounds := [.sub A (F A), .sub (F C) C, .sub A C]

/-- The declared shape equations themselves have no finite shape model. -/
theorem no_finite_shape_model : ¬ ∃ ρ, ComparisonShape.Models bounds ρ := by
  rintro ⟨ρ, hρ⟩
  have h := hρ (.var (.rigid 0), .prod (.var (.rigid 0)) .unit)
    (by simp [bounds, A, C, F, ComparisonShape.pairs, ComparisonShape.ofTy])
  have hs := congrArg sizeOf h
  simp only [ComparisonShape.subst, ComparisonShape.prod.sizeOf_spec, ComparisonShape.unit.sizeOf_spec] at hs
  omega

/-- The obstruction has no partial annotations in its declared endpoints. -/
theorem bounds_defined {a b} (h : Constraint.sub a b ∈ bounds) :
    a.DefinedUnder bounds ∧ b.DefinedUnder bounds := by
  simp only [bounds, List.mem_cons, List.not_mem_nil, or_false, Constraint.sub.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [A, C, F, TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

theorem bounds_sound {a b} (h : Constraint.sub a b ∈ bounds) :
    observe (.ofTy a) ⊆ observe (.ofTy b) := by
  simp only [bounds, List.mem_cons, List.not_mem_nil, or_false, Constraint.sub.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Set.empty_subset _
  · exact Set.subset_univ _
  · exact Set.empty_subset _

/-- Finite terms cannot distinguish the two tails forever. -/
theorem equal_tails (a : CompareTy) :
    ∃ n, ∀ k, n ≤ k → (observe a (true, k) ↔ observe a (false, k)) := by
  induction a with
  | var v =>
    refine ⟨0, fun k _ => ?_⟩
    by_cases h : v = .rigid 1 <;> simp [observe, h] <;> rfl
  | unit | credit | sum | fn => exact ⟨0, fun _ _ => Iff.rfl⟩
  | prod a b iha _ =>
    obtain ⟨n, hn⟩ := iha
    refine ⟨n + 1, fun k hk => ?_⟩
    cases k with
    | zero => omega
    | succ k => exact hn k (by omega)
  | modal a m ih => exact ih
  | join a b iha ihb | meet a b iha ihb =>
    obtain ⟨n, hn⟩ := iha
    obtain ⟨m, hm⟩ := ihb
    refine ⟨max n m, fun k hk => ?_⟩
    have h₁ := hn k (le_trans (le_max_left _ _) hk)
    have h₂ := hm k (le_trans (le_max_right _ _) hk)
    first | exact or_congr h₁ h₂ | exact and_congr h₁ h₂

/-- No finite internal type solves the fixed-point demand. The model validates
all original algebra rules, including guarded distribution and clamp. -/
theorem no_finite_fixed_point (a : CompareTy) :
    ¬ (AlgebraSubtype bounds a (.prod a .unit) ∧ AlgebraSubtype bounds (.prod a .unit) a) := by
  rintro ⟨h₁, h₂⟩
  have hl := algebra_sound h₁ (fun _ _ => bounds_sound)
  have hr := algebra_sound h₂ (fun _ _ => bounds_sound)
  have htrue (k : Nat) : observe a (true, k) := by
    induction k with
    | zero => exact hr rfl
    | succ k ih => exact hr ih
  have hfalse (k : Nat) : ¬ observe a (false, k) := by
    induction k with
    | zero => exact fun h => Bool.noConfusion (hl h)
    | succ k ih => exact fun h => ih (hl h)
  obtain ⟨n, hn⟩ := equal_tails a
  exact hfalse n ((hn n le_rfl).mp (htrue n))


def iterate {α : Type*} (f : α → α) (a : α) : Nat → α
  | 0 => a
  | n + 1 => f (iterate f a n)

theorem iterate_mono {α : Type*} [Preorder α] {f : α → α} {a : α}
    (hf : Monotone f) (ha : a ≤ f a) : Monotone (iterate f a) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact ha
  | succ n ih => exact hf ih

theorem iterate_stays {α : Type*} {f : α → α} {a : α} {i : Nat}
    (hi : iterate f a i = iterate f a (i + 1)) :
    ∀ n, i ≤ n → iterate f a n = iterate f a i := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    change f (iterate f a n) = iterate f a i
    rw [ih]
    exact hi.symm

/-- Every monotone ascending iteration in a finite poset is stationary by its
cardinality. This is a finite-state fact, not a term-algebra fixed-point rule. -/
theorem finite_iteration {α : Type*} [Fintype α] [PartialOrder α] {f : α → α} {a : α}
    (hf : Monotone f) (ha : a ≤ f a) :
    iterate f a (Fintype.card α) = iterate f a (Fintype.card α + 1) := by
  classical
  have hm := iterate_mono hf ha
  have hcollision {i j : Nat} (hij : i < j) (he : iterate f a i = iterate f a j) :
      iterate f a i = iterate f a (i + 1) := by
    apply le_antisymm (hm (by omega))
    exact (hm (show i + 1 ≤ j by omega)).trans (le_of_eq he.symm)
  by_contra hneq
  have hinj : Function.Injective (fun i : Fin (Fintype.card α + 1) => iterate f a i.val) := by
    intro i j he
    apply Fin.ext
    by_contra hij
    rcases Nat.lt_or_gt_of_ne hij with hij | hji
    · have hs := iterate_stays (hcollision hij he)
      exact hneq ((hs _ (by omega)).trans (hs _ (by omega)).symm)
    · have hs := iterate_stays (hcollision hji he.symm)
      exact hneq ((hs _ (by omega)).trans (hs _ (by omega)).symm)
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at hc
  omega

/-- The same finite iterate solves the interval/fixed-point demands in every
model over a fixed finite carrier, while no finite type solves the original
algebraic demands. -/
theorem finite_interval_solution {α : Type*} [Fintype α] [PartialOrder α]
    {f : α → α} {a c : α} (hf : Monotone f) (ha : a ≤ f a) (hc : f c ≤ c) (hac : a ≤ c) :
    let w := iterate f a (Fintype.card α)
    a ≤ w ∧ w ≤ c ∧ f w = w := by
  dsimp only
  have hu (n : Nat) : iterate f a n ≤ c := by
    induction n with
    | zero => exact hac
    | succ n ih => exact (hf ih).trans hc
  exact ⟨iterate_mono hf ha (Nat.zero_le _), hu _, (finite_iteration hf ha).symm⟩

/-- A literal finite type, using only the lower input name and the input
constructor context. -/
def candidate : Nat → CompareTy := iterate (fun a => .prod a .unit) (.ofTy A)

theorem candidate_eval {α : Type*} (eval : CompareTy → α) (f : α → α)
    (hf : ∀ a, eval (.prod a .unit) = f (eval a)) (n : Nat) :
    eval (candidate n) = iterate f (eval (.ofTy A)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change eval (.prod (candidate n) .unit) = f (iterate f (eval (.ofTy A)) n)
    rw [hf, ih]

/-- For a fixed finite semantic carrier, one literal input-derived candidate
satisfies all four demands in every interpretation preserving that constructor
and the declared bounds. This does not provide an algebraic derivation. -/
theorem finite_candidate {α : Type*} [Fintype α] [PartialOrder α]
    (eval : CompareTy → α) (f : α → α)
    (he : ∀ a, eval (.prod a .unit) = f (eval a)) (hf : Monotone f)
    (ha : eval (.ofTy A) ≤ f (eval (.ofTy A)))
    (hc : f (eval (.ofTy C)) ≤ eval (.ofTy C))
    (hac : eval (.ofTy A) ≤ eval (.ofTy C)) :
    eval (.ofTy A) ≤ eval (candidate (Fintype.card α)) ∧
    eval (candidate (Fintype.card α)) ≤ eval (.ofTy C) ∧
    eval (.prod (candidate (Fintype.card α)) .unit) = eval (candidate (Fintype.card α)) := by
  rw [he, candidate_eval eval f he]
  exact finite_interval_solution hf ha hc hac

end ModalityInference.ComparisonFiniteGraphLimitation
