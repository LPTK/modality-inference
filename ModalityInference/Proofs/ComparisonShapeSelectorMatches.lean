import ModalityInference.ComparisonShapeSelectorMatches
import ModalityInference.Proofs.ComparisonShapeSelectors

/-! Guarded finite branches express exact simultaneous matches after the
declared shape substitution, using only the shared selector block. -/

namespace ModalityInference.ComparisonShapeSelectors

private theorem any_map_eval {α : Type} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any (xs.map f)).eval world = true ↔ ∃x∈xs, (f x).eval world = true := by
  induction xs <;> simp_all [BoolExpr.any, BoolExpr.eval]

private theorem all_map_eval {α : Type} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all (xs.map f)).eval world = true ↔ ∀x∈xs, (f x).eval world = true := by
  induction xs <;> simp_all [BoolExpr.all, BoolExpr.eval]

theorem Layout.matches_eval (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (template target : ComparisonShape) (world : Nat → Bool) :
    (layout.matches fixed template target).eval world=true ↔
      ∃branch∈layout.branches template,
        branch.guard.eval world=true ∧ branch.shape.subst fixed=target := by
  rw [Layout.matches, any_map_eval]
  constructor
  · rintro ⟨branch, hb, he⟩
    by_cases hshape : branch.shape.subst fixed=target
    · exact ⟨branch, hb, by simpa only [hshape, beq_self_eq_true, if_true] using he, hshape⟩
    · simp only [beq_iff_eq, hshape, Bool.false_eq_true, if_false, BoolExpr.eval] at he
  · rintro ⟨branch, hb, hg, hs⟩
    exact ⟨branch, hb, by simpa only [hs, beq_self_eq_true, if_true] using hg⟩

theorem Layout.matches_decoded {layout : Layout} {world : Nat → Bool}
    (h : layout.theory.eval world=true) (fixed : TypeVar → ComparisonShape)
    (template target : ComparisonShape) (hscope : ∀v∈template.vars, v∈layout.parameters) :
    (layout.matches fixed template target).eval world=true ↔
      (template.subst (layout.decode world)).subst fixed=target := by
  rw [layout.matches_eval]
  constructor
  · rintro ⟨branch, hb, hg, hs⟩
    simpa only [(Layout.branches_decoded h template hscope).1 branch hb hg] using hs
  · intro hs
    obtain ⟨branch, hb, hg, he⟩ := (Layout.branches_decoded h template hscope).2
    exact ⟨branch, hb, hg, by simpa only [he] using hs⟩

theorem Layout.matches_encoded {layout : Layout} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v∈layout.parameters, ρ v∈layout.choices) (fixed : TypeVar → ComparisonShape)
    (template target : ComparisonShape) (hscope : ∀v∈template.vars, v∈layout.parameters) :
    (layout.matches fixed template target).eval (layout.encode ρ)=true ↔
      (template.subst ρ).subst fixed=target := by
  rw [layout.matches_eval]
  constructor
  · rintro ⟨branch, hb, hg, hs⟩
    simpa only [(Layout.branches_encoded hρ template hscope).1 branch hb hg] using hs
  · intro hs
    obtain ⟨branch, hb, hg, he⟩ := (Layout.branches_encoded hρ template hscope).2
    exact ⟨branch, hb, hg, by simpa only [he] using hs⟩


theorem Layout.matchesAll_decoded {layout : Layout} {world : Nat → Bool}
    (h : layout.theory.eval world=true) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape))
    (hscope : ∀pair∈equations, ∀v∈pair.1.vars, v∈layout.parameters) :
    (layout.matchesAll fixed equations).eval world=true ↔
      ∀pair∈equations, (pair.1.subst (layout.decode world)).subst fixed=pair.2 := by
  simp only [Layout.matchesAll, all_map_eval]
  exact forall₂_congr fun pair hp => layout.matches_decoded h fixed pair.1 pair.2 (hscope pair hp)

theorem Layout.matchesAll_encoded {layout : Layout} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v∈layout.parameters, ρ v∈layout.choices) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape))
    (hscope : ∀pair∈equations, ∀v∈pair.1.vars, v∈layout.parameters) :
    (layout.matchesAll fixed equations).eval (layout.encode ρ)=true ↔
      ∀pair∈equations, (pair.1.subst ρ).subst fixed=pair.2 := by
  simp only [Layout.matchesAll, all_map_eval]
  exact forall₂_congr fun pair hp => layout.matches_encoded hρ fixed pair.1 pair.2 (hscope pair hp)

theorem Layout.matchTheory_correct (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape)) (world : Nat → Bool)
    (hscope : ∀pair∈equations, ∀v∈pair.1.vars, v∈layout.parameters) :
    (layout.matchTheory fixed equations).eval world=true ↔
      layout.theory.eval world=true ∧
        ∀pair∈equations, (pair.1.subst (layout.decode world)).subst fixed=pair.2 := by
  simp only [Layout.matchTheory, BoolExpr.eval, Bool.and_eq_true]
  exact and_congr_right fun h => layout.matchesAll_decoded h fixed equations hscope

theorem Layout.compileMatches_correct {layout : Layout} {fuel : Nat}
    {fixed : TypeVar → ComparisonShape} {equations : List (ComparisonShape × ComparisonShape)}
    {clauses : CNF} (h : layout.compileMatches fuel fixed equations=.success clauses)
    (world : Nat → Bool) (hscope : ∀pair∈equations, ∀v∈pair.1.vars, v∈layout.parameters) :
    CNFHolds world clauses ↔ layout.theory.eval world=true ∧
      ∀pair∈equations, (pair.1.subst (layout.decode world)).subst fixed=pair.2 :=
  (CompactCNF.toCNF_correct h world).trans (layout.matchTheory_correct fixed equations world hscope)

theorem Layout.compileMatches_complete (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape)) :
    ∃threshold clauses, ∀fuel≥threshold, layout.compileMatches fuel fixed equations=.success clauses :=
  CompactCNF.toCNF_complete (layout.matchTheory fixed equations) true


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

theorem Layout.matches_atoms (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (template target : ComparisonShape) (hscope : ∀v∈template.vars, v∈layout.parameters) :
    ∀n∈(layout.matches fixed template target).atoms, layout.first≤n ∧ n<layout.next := by
  apply any_atoms
  intro e he n hn
  obtain ⟨branch, hb, rfl⟩ := List.mem_map.mp he
  by_cases hs : branch.shape.subst fixed=target
  · simp only [hs, beq_self_eq_true, if_true] at hn
    exact layout.branches_atoms template hscope branch hb n hn
  · simp only [beq_iff_eq, hs, if_false, BoolExpr.atoms] at hn
    exact (List.not_mem_nil hn).elim

theorem Layout.matchesAll_atoms (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape))
    (hscope : ∀pair∈equations, ∀v∈pair.1.vars, v∈layout.parameters) :
    ∀n∈(layout.matchesAll fixed equations).atoms, layout.first≤n ∧ n<layout.next := by
  apply all_atoms
  intro e he
  obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp he
  exact layout.matches_atoms fixed pair.1 pair.2 (hscope pair hp)

theorem Layout.matchTheory_atoms (layout : Layout) (fixed : TypeVar → ComparisonShape)
    (equations : List (ComparisonShape × ComparisonShape))
    (hscope : ∀pair∈equations, ∀v∈pair.1.vars, v∈layout.parameters) :
    ∀n∈(layout.matchTheory fixed equations).atoms, layout.first≤n ∧ n<layout.next := by
  intro n hn
  simp only [Layout.matchTheory, BoolExpr.atoms, List.mem_dedup, List.mem_append] at hn
  exact hn.elim (layout.theory_atoms n) (layout.matchesAll_atoms fixed equations hscope n)

end ModalityInference.ComparisonShapeSelectors
