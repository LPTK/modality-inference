import ModalityInference.ComparisonSelectedPlan
import ModalityInference.Proofs.ComparisonSelectedMatches

/-! Compiled selector plans are exact for shared shape choices, input anchors,
and inhabited basis branches; admissible witnesses satisfy these clauses. -/

namespace ModalityInference.ComparisonSelectedBases

open ComparisonShapeSelectors ComparisonShapeRetraction ComparisonPreparation ComparisonWitnessRestriction

private theorem any_map_eval {α : Type} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any (xs.map f)).eval world = true ↔ ∃x∈xs, (f x).eval world = true := by
  induction xs <;> simp_all [BoolExpr.any, BoolExpr.eval]

private theorem all_map_eval {α : Type} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all (xs.map f)).eval world = true ↔ ∀x∈xs, (f x).eval world = true := by
  induction xs <;> simp_all [BoolExpr.all, BoolExpr.eval]

theorem branchCoverage_eval (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool) :
    (branchCoverage (branchEntries first p solved)).eval world=true ↔
      ∀v∈inputNames p, ∃branch∈prepared first p solved v, branch.guard.eval world=true := by
  simp only [branchCoverage, all_map_eval, branchEntries, List.forall_mem_map, any_map_eval]

theorem selectorFormula_eval (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (world : Nat → Bool) :
    (selectorFormula first p solved).eval world=true ↔
      (anchorTheory first p solved).eval world=true ∧
      ∀v∈inputNames p, ∃branch∈prepared first p solved v, branch.guard.eval world=true := by
  simp only [selectorFormula, BoolExpr.eval, Bool.and_eq_true, branchCoverage_eval]

theorem compilePlan_spec {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {plan : Plan}
    (h : compilePlan fuel first p solved=.success plan) :
    plan.selectors=layout first p solved ∧ plan.branches=branchEntries first p solved ∧
      CompactCNF.toCNF fuel true (selectorFormula first p solved)=.success plan.clauses := by
  cases hc : CompactCNF.toCNF fuel true (selectorFormula first p solved) <;>
    simp [compilePlan, hc, bind, pure, RunResult.bind] at h
  subst plan
  exact ⟨rfl, rfl, rfl⟩

theorem compilePlan_complete (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) :
    ∃threshold plan, ∀fuel≥threshold, compilePlan fuel first p solved=.success plan := by
  obtain ⟨n, clauses, hc⟩ := CompactCNF.toCNF_complete (selectorFormula first p solved) true
  exact ⟨n, ⟨layout first p solved, branchEntries first p solved, clauses⟩,
    fun fuel hf => by simp [compilePlan, hc fuel hf, bind, pure, RunResult.bind]⟩

theorem compilePlan_correct {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {plan : Plan}
    (h : compilePlan fuel first p solved=.success plan) (world : Nat → Bool) :
    CNFHolds world plan.clauses ↔ (anchorTheory first p solved).eval world=true ∧
      ∀v∈inputNames p, ∃branch∈prepared first p solved v, branch.guard.eval world=true :=
  (CompactCNF.toCNF_correct (compilePlan_spec h).2.2 world).trans
    (selectorFormula_eval first p solved world)


theorem compilePlan_branch_sound {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {plan : Plan}
    (h : compilePlan fuel first p solved=.success plan) {world : Nat → Bool}
    (hw : CNFHolds world plan.clauses) {v : TypeVar} {branches : List Branch}
    (hv : (v, branches)∈plan.branches) {branch : Branch} (hb : branch∈branches)
    (hg : branch.guard.eval world=true) :
    v∈inputNames p ∧
      branch.shape=((solved.resolveAll v).subst (plan.selectors.decode world)).subst solved.fixedShapes ∧
      ComparisonStructuralBasis.basis (inputNames p) (inputModes p) solved.fixedShapes branch.shape =
        some branch.basis := by
  obtain ⟨hlayout, hentries, _⟩ := compilePlan_spec h
  rw [hentries] at hv
  obtain ⟨w, hwname, he⟩ := List.mem_map.mp hv
  have hev : w=v := congrArg Prod.fst he
  subst w
  have heb : prepared first p solved v=branches := congrArg Prod.snd he
  subst branches
  have ht := ((layout first p solved).matchTheory_correct solved.fixedShapes
    (anchorEquations p solved) world (anchorEquations_scope first p solved)).mp
      ((compilePlan_correct h world).mp hw).1
  refine ⟨hwname, ?_⟩
  simpa only [hlayout] using prepared_sound ht.1 hwname hb hg

theorem compilePlan_branch_coverage {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {plan : Plan}
    (h : compilePlan fuel first p solved=.success plan) {world : Nat → Bool}
    (hw : CNFHolds world plan.clauses) {v : TypeVar} (hv : v∈inputNames p) :
    ∃branches, (v, branches)∈plan.branches ∧
      ∃branch∈branches, branch.guard.eval world=true := by
  rw [(compilePlan_spec h).2.1]
  exact ⟨_, List.mem_map.mpr ⟨v, hv, rfl⟩, ((compilePlan_correct h world).mp hw).2 v hv⟩

theorem BranchPolynomials.selectorFormula {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat → Bool} {action : CompareSubstitution}
    (hs : ComparisonShapeSolver.prepare fuel p=.success (.solved solved))
    (h : BranchPolynomials first p solved world action) (hw : PreparedWitnessUnder p action) :
    (selectorFormula first p solved).eval world=true := by
  refine (selectorFormula_eval first p solved world).mpr ⟨h.anchorTheory hs hw, ?_⟩
  intro v hv
  obtain ⟨branch, hb, _, _, hg, _⟩ := h.2 v hv
  exact ⟨branch, hb, hg⟩

/-- Finite declared shape models admit an actual compiled selector plan and
one admissible image family realizing its enabled basis polynomials. -/
theorem algebra_compilePlan {ambient : Bounds} {source target : Scheme}
    (first : Nat) (h : AlgebraSubsumesUnder ambient source target)
    (hdecl : ∃φ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source.requireDefinedInstances target).assumptions φ) :
    let p := SchemePreparation.prepare ambient source.requireDefinedInstances target
    ∃threshold solved τ ρ plan,
      (∀fuel≥threshold,
        ComparisonShapeSolver.prepare fuel p=.success (.solved solved) ∧
        compilePlan fuel first p solved=.success plan) ∧
      PreparedWitnessUnder p τ ∧ Supported p τ ∧
      (∀v, ρ v∈shapeChoices p solved) ∧
      CNFHolds ((layout first p solved).encode ρ) plan.clauses ∧
      BranchPolynomials first p solved ((layout first p solved).encode ρ) τ := by
  obtain ⟨n, solved, τ, ρ, hs, hw, hsp, hc, hp⟩ := algebra_branch_polynomials first h hdecl
  obtain ⟨m, plan, hplan⟩ := compilePlan_complete first _ solved
  refine ⟨max n m, solved, τ, ρ, plan, ?_, hw, hsp, hc, ?_, hp⟩
  · intro fuel hf
    exact ⟨hs fuel (Nat.le_trans (Nat.le_max_left ..) hf),
      hplan fuel (Nat.le_trans (Nat.le_max_right ..) hf)⟩
  · exact (CompactCNF.toCNF_correct (compilePlan_spec (hplan m le_rfl)).2.2 _).mpr
      (hp.selectorFormula (hs n le_rfl) hw)


private theorem all_atoms {P : Nat → Prop} {es : List BoolExpr}
    (h : ∀e∈es, ∀n∈e.atoms, P n) : ∀n∈(BoolExpr.all es).atoms, P n := by
  induction es with
  | nil => simp [BoolExpr.all, BoolExpr.atoms]
  | cons e es ih =>
    intro n hn
    simp only [BoolExpr.all, List.foldr_cons, BoolExpr.atoms, List.mem_dedup, List.mem_append] at hn
    exact hn.elim (h e (List.mem_cons_self) n)
      (ih (fun e he => h e (List.mem_cons_of_mem _ he)) n)

private theorem any_atoms {P : Nat → Prop} {es : List BoolExpr}
    (h : ∀e∈es, ∀n∈e.atoms, P n) : ∀n∈(BoolExpr.any es).atoms, P n := by
  induction es with
  | nil => simp [BoolExpr.any, BoolExpr.atoms]
  | cons e es ih =>
    intro n hn
    simp only [BoolExpr.any, List.foldr_cons, BoolExpr.atoms, List.mem_dedup, List.mem_append] at hn
    exact hn.elim (h e (List.mem_cons_self) n)
      (ih (fun e he => h e (List.mem_cons_of_mem _ he)) n)

theorem branchCoverage_atoms (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) :
    ∀n∈(branchCoverage (branchEntries first p solved)).atoms,
      first≤n ∧ n<(layout first p solved).next := by
  apply all_atoms
  intro e he
  obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp he
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hentry
  apply any_atoms
  intro g hg
  obtain ⟨branch, hb, rfl⟩ := List.mem_map.mp hg
  exact prepared_atoms hv hb

theorem selectorFormula_atoms (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) :
    ∀n∈(selectorFormula first p solved).atoms, first≤n ∧ n<(layout first p solved).next := by
  intro n hn
  simp only [selectorFormula, BoolExpr.atoms, List.mem_dedup, List.mem_append] at hn
  exact hn.elim (anchorTheory_atoms first p solved n) (branchCoverage_atoms first p solved n)

theorem compilePlan_atoms {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {plan : Plan}
    (h : compilePlan fuel first p solved=.success plan) {clause : Clause} {literal : Literal}
    (hc : clause∈plan.clauses) (hl : literal∈clause) :
    first≤literal.1 ∧ literal.1<plan.selectors.next := by
  rw [(compilePlan_spec h).1]
  exact selectorFormula_atoms first p solved literal.1
    (CompactCNF.toCNF_literal (compilePlan_spec h).2.2 hc hl)

end ModalityInference.ComparisonSelectedBases
