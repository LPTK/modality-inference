import Mathlib.Combinatorics.Colex
import Mathlib.Logic.Relation

/-! A signed implication graph admits one Boolean assignment precisely when
no literal and its complement are mutually reachable. Successor-set ordering
provides a uniform model without selecting each edge's endpoints independently.
The quantified characterization supports symbolic relational implementations;
this module is the semantic kernel, not an executable scheme solver. -/
namespace ModalityInference.ComparisonSignedGraph

structure Graph (α : Type*) where
  complement : α → α
  involutive : Function.Involutive complement
  edge : α → α → Prop
  contrapose : ∀{a b},edge a b → edge (complement b) (complement a)

abbrev Graph.Reaches {α} (g : Graph α) := Relation.ReflTransGen g.edge

def Graph.Consistent {α} (g : Graph α) : Prop :=
  ∀a,¬(g.Reaches a (g.complement a) ∧ g.Reaches (g.complement a) a)

structure Graph.Model {α} (g : Graph α) (value : α → Bool) : Prop where
  complement : ∀a,value (g.complement a)=!value a
  edge : ∀{a b},g.edge a b → value a≤value b

theorem Graph.reaches_contrapose {α} (g : Graph α) {a b} (h : g.Reaches a b) :
    g.Reaches (g.complement b) (g.complement a) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact Relation.ReflTransGen.head (g.contrapose h) ih

theorem Graph.Model.reaches {α} {g : Graph α} {value} (hm : g.Model value)
    {a b} (h : g.Reaches a b) : value a≤value b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans (hm.edge h)

theorem Graph.Model.consistent {α} {g : Graph α} {value} (hm : g.Model value) :
    g.Consistent := by
  intro a h
  have he := le_antisymm (hm.reaches h.1) (hm.reaches h.2)
  rw [hm.complement] at he
  cases hv : value a <;> simp_all

noncomputable def Graph.successors {α} [Fintype α] (g : Graph α) (a : α) : Finset α :=
  @Finset.filter α (fun b => g.Reaches a b) (Classical.decPred _) Finset.univ

theorem Graph.mem_successors {α} [Fintype α] (g : Graph α) (a b : α) :
    b∈g.successors a ↔ g.Reaches a b := by
  classical
  simp [Graph.successors]

theorem Graph.successors_subset {α} [Fintype α] (g : Graph α) {a b}
    (h : g.Reaches a b) : g.successors b⊆g.successors a := by
  intro c hc
  exact (g.mem_successors a c).mpr (h.trans ((g.mem_successors b c).mp hc))

theorem Graph.successors_ne {α} [Fintype α] (g : Graph α) (hc : g.Consistent) (a : α) :
    g.successors a≠g.successors (g.complement a) := by
  intro he
  apply hc a
  constructor
  · apply (g.mem_successors _ _).mp
    rw [he]
    exact (g.mem_successors _ _).mpr .refl
  · apply (g.mem_successors _ _).mp
    rw [←he]
    exact (g.mem_successors _ _).mpr .refl

noncomputable def Graph.canonical {α} [Fintype α] [LinearOrder α] (g : Graph α) (a : α) : Bool :=
  decide (toColex (g.successors a)<toColex (g.successors (g.complement a)))

theorem Graph.canonical_complement {α} [Fintype α] [LinearOrder α]
    (g : Graph α) (hc : g.Consistent) (a : α) :
    g.canonical (g.complement a)=!g.canonical a := by
  have hne : toColex (g.successors a)≠toColex (g.successors (g.complement a)) :=
    fun h => g.successors_ne hc a (congrArg ofColex h)
  simp only [Graph.canonical,g.involutive a]
  by_cases h : toColex (g.successors a)<toColex (g.successors (g.complement a))
  · simp [h,not_lt_of_gt h]
  · have hr := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    simp [h,hr]

theorem Graph.canonical_edge {α} [Fintype α] [LinearOrder α]
    (g : Graph α) {a b} (hab : g.edge a b) : g.canonical a≤g.canonical b := by
  apply Bool.le_iff_imp.mpr
  intro ha
  have hlt : toColex (g.successors a)<toColex (g.successors (g.complement a)) :=
    of_decide_eq_true ha
  apply decide_eq_true
  exact lt_of_le_of_lt (Finset.Colex.toColex_le_toColex_of_subset
    (g.successors_subset (.single hab)))
    (lt_of_lt_of_le hlt (Finset.Colex.toColex_le_toColex_of_subset
      (g.successors_subset (.single (g.contrapose hab)))))

theorem Graph.canonical_model {α} [Fintype α] [LinearOrder α]
    (g : Graph α) (hc : g.Consistent) : g.Model g.canonical :=
  ⟨g.canonical_complement hc,fun h => g.canonical_edge h⟩

theorem Graph.model_iff {α} [Fintype α] [LinearOrder α] (g : Graph α) :
    (∃value,g.Model value) ↔ g.Consistent :=
  ⟨fun ⟨_,h⟩ => h.consistent,fun h => ⟨_,g.canonical_model h⟩⟩

/-- A first-order formula for the canonical assignment. The input tuples can
be quantified symbolically instead of enumerating all graph vertices. -/
theorem Graph.canonical_iff {α} [Fintype α] [LinearOrder α] (g : Graph α) (a : α) :
    g.canonical a=true ↔
      ∃b,g.Reaches (g.complement a) b ∧ ¬g.Reaches a b ∧
        ∀c,g.Reaches a c → ¬g.Reaches (g.complement a) c → c<b := by
  simp only [Graph.canonical,decide_eq_true_eq,
    Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt,Graph.mem_successors]

end ModalityInference.ComparisonSignedGraph
