import ModalityInference.Proofs.ComparisonTupleReification
import ModalityInference.Proofs.ComparisonBoundaryPropagation

/-! Positive head clauses become executable tuple formulas while scalar
parameters retain their shared synthesized expressions. -/
namespace ModalityInference.ComparisonTupleCNF

open ComparisonControls ComparisonTupleReification SymbolicModes

/-- Only nominal heads must occur positively; scalar coefficients may have
arbitrary polarity. -/
def HeadPositive (heads : Nat) (clauses : CNF) : Prop :=
  ∀ clause ∈ clauses, ∀ literal ∈ clause, literal.1 < heads → literal.2 = true

def literal (b : Basis) (scalars : Nat → BoolExpr) (value : Literal) : Formula b BoolExpr :=
  if h : value.1 < b.heads.length then
    if value.2 then .head b.heads[value.1] (List.getElem_mem h)
    else .scalar (.const false)
  else .scalar (if value.2 then scalars value.1 else .imp (scalars value.1) (.const false))

def clause (b : Basis) (scalars : Nat → BoolExpr) (values : Clause) : Formula b BoolExpr :=
  values.foldr (fun value rest => .join (literal b scalars value) rest) (.scalar (.const false))

def cnf (b : Basis) (scalars : Nat → BoolExpr) (clauses : CNF) : Formula b BoolExpr :=
  clauses.foldr (fun values rest => .meet (clause b scalars values) rest) (.scalar (.const true))

/-- Complementary parameter coordinates refer to one shared scalar expression. -/
def signed (heads : Nat) (values : Nat → BoolExpr) (i : Nat) : BoolExpr :=
  if (i - heads) % 2 == 0 then values ((i - heads) / 2)
  else .imp (values ((i - heads) / 2)) (.const false)

def world (b : Basis) (heads : CompareTy → Bool) (scalars : Nat → BoolExpr)
    (values : Nat → Bool) (i : Nat) : Bool :=
  if h : i < b.heads.length then heads b.heads[i] else (scalars i).eval values

private theorem literal_correct {b : Basis} {scalars : Nat → BoolExpr}
    {value : Literal} (hp : value.1 < b.heads.length → value.2 = true)
    (heads : CompareTy → Bool) (values : Nat → Bool) :
    (literal b scalars value).eval (fun c => c.eval values) heads = true ↔
      world b heads scalars values value.1 = value.2 := by
  by_cases hi : value.1 < b.heads.length
  · simp [literal, world, hi, hp hi, Formula.eval]
  · cases h : value.2 <;> simp [literal, world, hi, h, Formula.eval, BoolExpr.eval]

private theorem clause_correct {b : Basis} {scalars : Nat → BoolExpr} {c : Clause}
    (hp : ∀value∈c, value.1 < b.heads.length → value.2 = true)
    (heads : CompareTy → Bool) (values : Nat → Bool) :
    (clause b scalars c).eval (fun e => e.eval values) heads = true ↔
      ClauseHolds (world b heads scalars values) c := by
  induction c with
  | nil => simp [clause, Formula.eval, BoolExpr.eval, ClauseHolds]
  | cons value rest ih =>
    change ((literal b scalars value).eval (fun e => e.eval values) heads ||
      (clause b scalars rest).eval (fun e => e.eval values) heads) = true ↔ _
    simp only [Bool.or_eq_true]
    rw [literal_correct (hp value List.mem_cons_self),
      ih (fun v hv => hp v (List.mem_cons_of_mem _ hv))]
    cases value
    simp [clauseHolds_cons]

/-- The translation preserves each clause under arbitrary head and scalar
valuations; no coordinate or valuation-specific choice enters the formula. -/
theorem cnf_correct {b : Basis} {scalars : Nat → BoolExpr} {cs : CNF}
    (hp : HeadPositive b.heads.length cs) (heads : CompareTy → Bool) (values : Nat → Bool) :
    (cnf b scalars cs).eval (fun e => e.eval values) heads = true ↔
      CNFHolds (world b heads scalars values) cs := by
  induction cs with
  | nil => simp [cnf, Formula.eval, BoolExpr.eval, CNFHolds]
  | cons c cs ih =>
    change ((clause b scalars c).eval (fun e => e.eval values) heads &&
      (cnf b scalars cs).eval (fun e => e.eval values) heads) = true ↔ _
    simp only [Bool.and_eq_true]
    rw [clause_correct (hp c List.mem_cons_self),
      ih (fun d hd => hp d (List.mem_cons_of_mem _ hd))]
    simp [CNFHolds]

private theorem supported_neg {b : Basis} {axis : Axis} {e : BoolExpr}
    (h : ComparisonTupleReification.Supported b axis e) :
    ComparisonTupleReification.Supported b axis (.imp e (.const false)) := by
  simpa [ComparisonTupleReification.Supported, BoolExpr.atoms] using h

private theorem supported_const (b : Basis) (axis : Axis) (v : Bool) :
    ComparisonTupleReification.Supported b axis (.const v) := by
  simp [ComparisonTupleReification.Supported, BoolExpr.atoms]

private theorem literal_supported {b : Basis} {axis : Axis} {scalars : Nat → BoolExpr}
    (value : Literal)
    (hs : b.heads.length ≤ value.1 → ComparisonTupleReification.Supported b axis (scalars value.1)) :
    (literal b scalars value).All (ComparisonTupleReification.Supported b axis) := by
  unfold literal
  split
  · cases value.2 <;> simp [Formula.All, supported_const]
  · cases value.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, Formula.All]
    · exact supported_neg (hs (by omega))
    · exact hs (by omega)

private theorem clause_supported {b : Basis} {axis : Axis} {scalars : Nat → BoolExpr} {c : Clause}
    (hs : ∀value∈c, b.heads.length ≤ value.1 →
      ComparisonTupleReification.Supported b axis (scalars value.1)) :
    (clause b scalars c).All (ComparisonTupleReification.Supported b axis) := by
  induction c with
  | nil => exact supported_const _ _ _
  | cons value rest ih =>
    exact ⟨literal_supported value (hs value List.mem_cons_self),
      ih (fun v hv => hs v (List.mem_cons_of_mem _ hv))⟩

/-- Legal dependence is inherited exactly from the scalar expressions attached
to the non-head atoms that occur in the reconstructed clauses. -/
theorem cnf_supported {b : Basis} {axis : Axis} {scalars : Nat → BoolExpr} {cs : CNF}
    (hs : ∀i∈CNFPropagation.atoms cs, b.heads.length ≤ i →
      ComparisonTupleReification.Supported b axis (scalars i)) :
    (cnf b scalars cs).All (ComparisonTupleReification.Supported b axis) := by
  have hs' : ∀c∈cs, ∀value∈c, b.heads.length ≤ value.1 →
      ComparisonTupleReification.Supported b axis (scalars value.1) := by
    intro c hc value hv hi
    apply hs value.1 ?_ hi
    simp only [CNFPropagation.atoms, List.mem_flatMap, List.mem_map]
    exact ⟨c, hc, value, hv, rfl⟩
  induction cs with
  | nil => exact supported_const _ _ _
  | cons c cs ih =>
    exact ⟨clause_supported (hs' c List.mem_cons_self),
      ih (fun i hi => hs i (by simp only [CNFPropagation.atoms, List.flatMap_cons,
        List.mem_append] at hi ⊢; exact Or.inr hi))
        (fun d hd => hs' d (List.mem_cons_of_mem _ hd))⟩

@[simp] theorem signed_eval (heads : Nat) (values : Nat → BoolExpr)
    (world : Nat → Bool) (i : Nat) :
    (signed heads values i).eval world =
      if (i - heads) % 2 == 0 then (values ((i - heads) / 2)).eval world
      else !(values ((i - heads) / 2)).eval world := by
  simp only [signed]
  split <;> simp [BoolExpr.eval]

theorem signed_supported {b : Basis} {axis : Axis} {values : Nat → BoolExpr} {i : Nat}
    (h : ComparisonTupleReification.Supported b axis (values ((i - b.heads.length) / 2))) :
    ComparisonTupleReification.Supported b axis (signed b.heads.length values i) := by
  unfold signed
  split
  · exact h
  · exact supported_neg h

theorem positive_headPositive {b : Basis} {cs : CNF}
    (h : ComparisonPropagation.Positive cs) : HeadPositive b.heads.length cs :=
  fun c hc value hv _ => h c hc value hv

def mapFormula (f : α → β) : Formula b α → Formula b β
  | .head a ha => .head a ha
  | .scalar a => .scalar (f a)
  | .join a c => .join (mapFormula f a) (mapFormula f c)
  | .meet a c => .meet (mapFormula f a) (mapFormula f c)

theorem mapFormula_eval (f : α → β) (e : Formula b α) (scalar : β → Bool)
    (heads : CompareTy → Bool) :
    (mapFormula f e).eval scalar heads = e.eval (scalar ∘ f) heads := by
  induction e <;> simp_all [mapFormula, Formula.eval]

def nominal (b : Basis) (clauses : CNF) : Formula b Bool :=
  mapFormula (BoolExpr.eval (fun _ => false)) (cnf b (fun _ => .const false) clauses)

theorem nominal_correct {b : Basis} {cs : CNF} (hp : HeadPositive b.heads.length cs)
    (heads : CompareTy → Bool) :
    (nominal b cs).eval id heads = true ↔
      CNFHolds (world b heads (fun _ => .const false) (fun _ => false)) cs := by
  rw [nominal, mapFormula_eval]
  exact cnf_correct hp heads (fun _ => false)

theorem nominal_normalized {b : Basis} {cs : CNF}
    (hp : ComparisonPropagation.Positive cs)
    (hs : ComparisonPropagation.Supported (List.range b.heads.length) cs)
    (hz : ¬CNFHolds (fun _ => false) cs) (ho : CNFHolds (fun _ => true) cs) :
    (nominal b cs).eval id (fun _ => false) = false ∧
      (nominal b cs).eval id (fun _ => true) = true := by
  constructor
  · apply Bool.eq_false_iff.mpr
    intro h
    have hh := (nominal_correct (positive_headPositive hp) _).mp h
    apply hz
    apply (CNFPropagation.holds_congr ?_).mp hh
    intro i hi
    simp [world, BoolExpr.eval]
  · apply (nominal_correct (positive_headPositive hp) _).mpr
    apply (CNFPropagation.holds_congr ?_).mpr ho
    intro i hi
    have hit : i < b.heads.length := List.mem_range.mp (hs i hi)
    simp [world, hit]

end ModalityInference.ComparisonTupleCNF
