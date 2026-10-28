import ModalityInference.ComparisonObserverMachineRestriction
import ModalityInference.Proofs.ComparisonObserverMachineCheck
import ModalityInference.Proofs.ModeWitness

/-! Restricting the name tables preserves supported lookups and actions.
Checked machines remain checked in contexts without raw subtype rows, provided
all scalar names are retained. No restriction on the old name tables is needed. -/
namespace ModalityInference.ComparisonObserverMachineRestriction

open ComparisonObserverMachineCheck ComparisonObserverRangeEncoding
  ComparisonStructuralLayout

variable {State : Type} {types types' : List TypeVar} {modes modes' : List ModVar}

private theorem getElem_idxOf_mem {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {a : α}
    (ha : a ∈ xs) : xs[xs.idxOf a]? = some a := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    by_cases hb : b = a
    · subst b
      simp
    · have hx : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hb)
      have he : (b == a) = false := beq_eq_false_iff_ne.mpr hb
      simpa [List.idxOf_cons, he] using ih hx

theorem atomValue_restrict (d : Description State) {v} (hv : v ∈ types') :
    atomValue types' (restrict types modes types' modes' d) v = atomValue types d v := by
  simp [atomValue, restrict, hv, List.getElem?_map, getElem_idxOf_mem hv]

theorem modeValue_restrict (d : Description State) {v} (hv : v ∈ modes') :
    modeValue modes' (restrict types modes types' modes' d) v = modeValue modes d v := by
  simp [modeValue, restrict, hv, List.getElem?_map, getElem_idxOf_mem hv]

theorem action_restrict (d : Description State) {m : ModExpr}
    (hm : m.vars ⊆ modes'.toFinset) (x : Bool) :
    action modes' (restrict types modes types' modes' d) m x = action modes d m x := by
  unfold action
  rw [ModExpr.eval_congr m
    (σ := some ∘ modeValue modes' (restrict types modes types' modes' d))
    (τ := some ∘ modeValue modes d)
    (fun v hv => congrArg some (modeValue_restrict d (List.mem_toFinset.mp (hm hv))))]
  rfl

theorem scalarOK_restrict {Δ : Bounds} (hΔ : Δ.modVars ⊆ modes'.toFinset)
    (d : Description State) (h : scalarOK Δ modes d = true) :
    scalarOK Δ modes' (restrict types modes types' modes' d) = true := by
  apply scalarOK_correct.mpr
  exact (scalarOK_correct.mp h).imp id (fun hm => (ModeModels.congr Δ
    (fun v hv => (modeValue_restrict d (List.mem_toFinset.mp (hΔ hv))).symm)).mp hm)

theorem sameInputs_restrict {p c : Description State} (h : sameInputs modes p c = true) :
    sameInputs modes' (restrict types modes types' modes' p)
      (restrict types modes types' modes' c) = true := by
  cases hc : c.coordinate <;>
    simp only [sameInputs, show (restrict types modes types' modes' c).coordinate =
      c.coordinate from rfl, hc, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h ⊢
  all_goals intro v hv
  all_goals rw [modeValue_restrict _ hv, modeValue_restrict _ hv]
  all_goals
    by_cases hv' : v ∈ modes
    · exact h v hv'
    · simp [modeValue, hv']

theorem pairOK_restrict {p c : Description State} (h : pairOK modes p c = true) :
    pairOK modes' (restrict types modes types' modes' p)
      (restrict types modes types' modes' c) = true := by
  simp only [pairOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact h.imp id (fun ⟨he,hi⟩ => ⟨he,sameInputs_restrict hi⟩)

theorem check_restrict {count : Nat} {Δ : Bounds}
    (hΔ : Δ.modVars ⊆ modes'.toFinset) (hn : ∀ a b, Constraint.sub a b ∉ Δ)
    {data : Fin count → Description (Fin count)} (h : check Δ types modes data = true) :
    check Δ types' modes' (fun i => restrict types modes types' modes' (data i)) = true := by
  apply check_correct.mpr
  intro i
  have hi := check_correct.mp h i
  refine ⟨scalarOK_restrict hΔ _ hi.scalar, hi.unit, hi.credit, ?_, hi.closed,
    hi.branch, pairOK_restrict hi.prod, pairOK_restrict hi.sum, hi.fn, ?_⟩
  · intro v hv
    rw [atomValue_restrict _ hv]
    change (data i).range (atomValue types (data i) v) = true
    by_cases hv' : v ∈ types
    · exact hi.atom v hv'
    · simpa [atomValue, hv'] using hi.unit
  · exact declared_correct.mpr (fun a b hab => (hn a b hab).elim)

theorem atoms_length (d : Description State) :
    (restrict types modes types' modes' d).atoms.length = types'.length := List.length_map _

theorem modes_length (d : Description State) :
    (restrict types modes types' modes' d).modes.length = modes'.length := List.length_map _

variable {count : Nat} (data : Fin count → Description (Fin count))

theorem admitted_restrict (x : Bits count) :
    admitted (fun i => restrict types modes types' modes' (data i)) x = admitted data x := rfl

theorem vectors_restrict :
    vectors (fun i => restrict types modes types' modes' (data i)) = vectors data := rfl

theorem unit_restrict :
    unit (fun i => restrict types modes types' modes' (data i)) = unit data := rfl

theorem credit_restrict :
    credit (fun i => restrict types modes types' modes' (data i)) = credit data := rfl

theorem atom_restrict {v : TypeVar} (hv : v ∈ types') :
    atom (fun i => restrict types modes types' modes' (data i)) types' v = atom data types v :=
  funext (fun i => atomValue_restrict (data i) hv)

theorem modal_restrict {m : ModExpr} (hm : m.vars ⊆ modes'.toFinset) (x : Bits count) :
    modal (fun i => restrict types modes types' modes' (data i)) modes' m x =
      modal data modes m x := funext (fun i => action_restrict (data i) hm (x i))

theorem op_restrict (k : Constructor) (x y : Bits count) :
    op (fun i => restrict types modes types' modes' (data i)) k x y = op data k x y := rfl

end ModalityInference.ComparisonObserverMachineRestriction
