import ModalityInference.ComparisonExecutableSyntaxSupport

/-! Agreement only on the finite accesses made by a query suffices to preserve
its value; filtering a lookup table preserves the first matching retained row. -/
namespace ModalityInference.ComparisonExecutableSyntax

variable {M V : Type*}

structure AccessAgreement (E F : Data M V) (keys : List Access) : Prop where
  total : E.total = F.total
  control : E.control = F.control
  shift : E.shift = F.shift
  prod : ∀ p, .prod p ∈ keys → E.prod p = F.prod p
  sum : ∀ p, .sum p ∈ keys → E.sum p = F.sum p
  fn : E.fn = F.fn
  join : E.join = F.join
  meet : E.meet = F.meet
  atom : E.atom = F.atom
  unit : E.unit = F.unit
  credit : E.credit = F.credit
  frozen : ∀ a, .frozen a ∈ keys → E.frozenValue a = F.frozenValue a

namespace AccessAgreement

variable {E F : Data M V} {keys : List Access} (h : AccessAgreement E F keys)

include h

theorem eval_eq (a : CompareTy) (p : Option ModExpr)
    (ha : accesses E.total a p ⊆ keys) : E.eval a p = F.eval a p := by
  induction a generalizing p <;> cases p <;>
    simp_all [accesses, Data.eval, List.cons_subset, List.append_subset,
      h.total, h.control, h.shift, h.fn, h.join, h.meet, h.atom, h.unit, h.credit,
      h.prod, h.sum, h.frozen]

end AccessAgreement

theorem selectRows_find_eq {α β : Type*} [DecidableEq α]
    (keys : List α) (rows : List (α × β)) (key : α) :
    (selectRows keys rows).find? (fun row => decide (row.1 = key)) =
      if key ∈ keys then rows.find? (fun row => decide (row.1 = key)) else none := by
  induction keys with
  | nil => simp [selectRows]
  | cons head tail ih =>
    simp only [selectRows, List.filterMap_cons] at ih ⊢
    cases hf : rows.find? (fun row => decide (row.1 = head)) with
    | none =>
      by_cases he : key = head
      · subst key
        simp only [Option.map_none, ih, hf, ite_self, List.mem_cons_self]
      · simp only [Option.map_none, ih, List.mem_cons, he, false_or]
    | some row =>
      have hr : row.1 = head := of_decide_eq_true
        (List.find?_some (p := fun r : α × β => decide (r.1 = head)) hf)
      by_cases he : head = key
      · rw [he] at hf hr ⊢
        simp only [Option.map_some, List.find?_cons, decide_true,
          List.mem_cons_self, if_pos, hf, Option.some.injEq]
        exact Prod.ext hr.symm rfl
      · simp only [Option.map_some, List.find?_cons, he, decide_false,
          ih, List.mem_cons, Ne.symm he, false_or]

theorem selectRows_find {α β : Type*} [DecidableEq α]
    (keys : List α) (rows : List (α × β)) {key : α} (hk : key ∈ keys) :
    (selectRows keys rows).find? (fun row => decide (row.1 = key)) =
      rows.find? (fun row => decide (row.1 = key)) := by
  simpa only [hk, if_pos] using selectRows_find_eq keys rows key

theorem selectRows_length_le {α β : Type*} [DecidableEq α]
    (keys : List α) (rows : List (α × β)) : (selectRows keys rows).length ≤ keys.length :=
  List.length_filterMap_le _ _

theorem selectRows_subset {α β : Type*} [DecidableEq α]
    (keys : List α) (rows : List (α × β)) : selectRows keys rows ⊆ rows := by
  intro row hrow
  obtain ⟨key, _, hrow⟩ := List.mem_filterMap.mp hrow
  obtain ⟨found, hf, rfl⟩ := Option.map_eq_some_iff.mp hrow
  have hk : found.1 = key := of_decide_eq_true
    (List.find?_some (p := fun r : α × β => decide (r.1 = key)) hf)
  simpa only [← hk] using List.mem_of_find?_eq_some hf

theorem selectRows_key_mem {α β : Type*} [DecidableEq α]
    (keys : List α) (rows : List (α × β)) {row : α × β}
    (hrow : row ∈ selectRows keys rows) : row.1 ∈ keys := by
  obtain ⟨key, hkey, hrow⟩ := List.mem_filterMap.mp hrow
  obtain ⟨found, _, rfl⟩ := Option.map_eq_some_iff.mp hrow
  exact hkey

theorem accesses_subset_accessList (total : ModExpr → Bool)
    {queries : List (CompareTy × Option ModExpr)} {a : CompareTy} {p : Option ModExpr}
    (hq : (a,p) ∈ queries) : accesses total a p ⊆ accessList total queries :=
  fun _ hk => List.mem_flatMap.mpr ⟨(a,p), hq, hk⟩

theorem prod_mem_literalPrefixes {keys : List Access} {p : ModExpr}
    (hp : .prod (some p) ∈ keys) : p ∈ literalPrefixes keys :=
  List.mem_filterMap.mpr ⟨.prod (some p), hp, rfl⟩

theorem sum_mem_literalPrefixes {keys : List Access} {p : ModExpr}
    (hp : .sum (some p) ∈ keys) : p ∈ literalPrefixes keys :=
  List.mem_filterMap.mpr ⟨.sum (some p), hp, rfl⟩

theorem frozen_mem_frozenKeys {keys : List Access} {a : CompareTy}
    (ha : .frozen a ∈ keys) : a ∈ frozenKeys keys :=
  List.mem_filterMap.mpr ⟨.frozen a, ha, rfl⟩

end ModalityInference.ComparisonExecutableSyntax
