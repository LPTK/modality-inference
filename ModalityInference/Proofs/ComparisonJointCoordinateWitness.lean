import ModalityInference.Proofs.ComparisonFixedModeWitness
import ModalityInference.Proofs.ComparisonJointGroupWitness
import ModalityInference.Proofs.ComparisonJointAxisSummary
import ModalityInference.ComparisonJointAssembly

/-! Finite positive coordinate formulas for one admissible shared type action.
Signed scalar parameters preserve residual projections and fixed image support
makes the formulas functions of the shared strategy's outputs. -/
namespace ModalityInference.ComparisonJointCoordinateWitness

open ComparisonPropagation ComparisonSelectorPropagation ComparisonControls
open ComparisonJointGroup ComparisonFixedModeWitness

private theorem meet_positive {a b : CNF} (ha : Positive a) (hb : Positive b) :
    Positive (meet a b) := by
  intro clause hc literal hl
  obtain ⟨d,hd,hl⟩ := CompactCNF.clean_literal hc hl
  exact (List.mem_append.mp hd).elim (fun h => ha d h literal hl) (fun h => hb d h literal hl)

private theorem meet_supported {domain : List Nat} {a b : CNF}
    (ha : Supported domain a) (hb : Supported domain b) : Supported domain (meet a b) := by
  intro v hv
  obtain ⟨clause,hc,p,hl⟩ := CNFPropagation.mem_atoms.mp (CompactCNF.clean_atoms hv)
  exact (List.mem_append.mp hc).elim
    (fun h => ha v (CNFPropagation.mem_atoms.mpr ⟨clause,h,p,hl⟩))
    (fun h => hb v (CNFPropagation.mem_atoms.mpr ⟨clause,h,p,hl⟩))

/-- Each polarity of a scalar atom is represented by its own positive coordinate. -/
def scalar (heads selectors : Nat) : BoolExpr → Bool → CNF
  | .const b, p => if b == p then [] else [[]]
  | .atom v, p => [[(heads + 2 * (selectors + v) + if p then 0 else 1, true)]]
  | .imp a b, p => if p then join (scalar heads selectors a false) (scalar heads selectors b true)
      else meet (scalar heads selectors a true) (scalar heads selectors b false)
  | .and a b, p => if p then meet (scalar heads selectors a true) (scalar heads selectors b true)
      else join (scalar heads selectors a false) (scalar heads selectors b false)
  | .or a b, p => if p then join (scalar heads selectors a true) (scalar heads selectors b true)
      else meet (scalar heads selectors a false) (scalar heads selectors b false)

theorem scalar_positive (heads selectors : Nat) (e : BoolExpr) (p : Bool) :
    Positive (scalar heads selectors e p) := by
  induction e generalizing p with
  | const b => cases p <;> cases b <;> simp [scalar, Positive]
  | atom v => simp [scalar, Positive]
  | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    cases p <;> simp only [scalar, Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact meet_positive (iha _) (ihb _) | exact join_positive (iha _) (ihb _)

theorem scalar_supported {heads selectors modes : Nat} {e : BoolExpr}
    (he : ∀ i ∈ e.atoms, i < modes) (p : Bool) :
    Supported (List.range (heads + 2 * (selectors + modes))) (scalar heads selectors e p) := by
  induction e generalizing p with
  | const b => cases p <;> cases b <;> simp [scalar, Supported, CNFPropagation.atoms]
  | atom v =>
    intro i hi
    have hv := he v (by simp [BoolExpr.atoms])
    simp only [scalar, CNFPropagation.atoms, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false, exists_eq_left, List.mem_map, Prod.exists,
      Prod.mk.injEq] at hi
    cases p <;> simp_all <;> omega
  | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    have ha : ∀ i ∈ a.atoms, i < modes := fun i hi => he i (by simp [BoolExpr.atoms, hi])
    have hb : ∀ i ∈ b.atoms, i < modes := fun i hi => he i (by simp [BoolExpr.atoms, hi])
    cases p <;> simp only [scalar, Bool.false_eq_true, ↓reduceIte]
    all_goals first | exact meet_supported (iha ha _) (ihb hb _) | exact join_supported (iha ha _) (ihb hb _)

theorem scalar_correct {heads selectors modes : Nat} {e : BoolExpr}
    (he : ∀ i ∈ e.atoms, i < modes) {choice world : Nat → Bool}
    (hw : Slice heads (selectors + modes) choice world) (p : Bool) :
    CNFHolds world (scalar heads selectors e p) ↔ e.eval (fun i => choice (selectors + i)) = p := by
  induction e generalizing p with
  | const b => cases p <;> cases b <;> simp [scalar, CNFHolds, ClauseHolds, BoolExpr.eval]
  | atom v =>
    have hv := he v (by simp [BoolExpr.atoms])
    have hh := hw (selectors + v) (by omega)
    cases p <;> simp [scalar, CNFHolds, ClauseHolds, BoolExpr.eval, hh.1, hh.2]
  | and a b iha ihb | or a b iha ihb | imp a b iha ihb =>
    have ha : ∀ i ∈ a.atoms, i < modes := fun i hi => he i (by simp [BoolExpr.atoms, hi])
    have hb : ∀ i ∈ b.atoms, i < modes := fun i hi => he i (by simp [BoolExpr.atoms, hi])
    cases p <;> simp only [scalar, Bool.false_eq_true, ↓reduceIte, meet_correct, join_correct,
      iha ha, ihb hb, BoolExpr.eval]
    all_goals cases a.eval (fun i => choice (selectors+i)) <;>
      cases b.eval (fun i => choice (selectors+i)) <;> decide

theorem atomVariable_lt {cutoff i : Nat} (h : (SymbolicModes.atomVariable i).index < cutoff) :
    i < 6 * cutoff := by
  unfold SymbolicModes.atomVariable at h
  split at h <;> simp only [ModVar.index] at h <;> omega

theorem projection_atoms {cutoff modes : Nat} {m : ModExpr} (hb : 6 * cutoff ≤ modes)
    (h : ∀ v ∈ m.vars, v.index < cutoff) :
    (∀ i ∈ m.project.locality.atoms, i < modes) ∧
    (∀ i ∈ m.project.affinity.atoms, i < modes) ∧
    (∀ i ∈ m.project.uniqueness.atoms, i < modes) := by
  have hs := ComparisonControls.project_support m
  exact ⟨fun i hi => (atomVariable_lt (h _ ((m.mem_freeVariables _).mp (hs.1 i hi).2))).trans_le hb,
    fun i hi => (atomVariable_lt (h _ ((m.mem_freeVariables _).mp (hs.2.1 i hi).2))).trans_le hb,
    fun i hi => (atomVariable_lt (h _ ((m.mem_freeVariables _).mp (hs.2.2 i hi).2))).trans_le hb⟩

def formula (heads : List TypeVar) (selectors : Nat) (c : Coordinate) : CompareTy → CNF
  | .var v => [[(heads.idxOf v, true)]]
  | .join a b => join (formula heads selectors c a) (formula heads selectors c b)
  | .meet a b => meet (formula heads selectors c a) (formula heads selectors c b)
  | .modal a m => match c with
    | .unaffected => formula heads selectors c a
    | .locality => meet (formula heads selectors c a) (scalar heads.length selectors m.project.locality true)
    | .affinity => meet (formula heads selectors c a) (scalar heads.length selectors m.project.affinity true)
    | .uniqueness => join (formula heads selectors c a) (scalar heads.length selectors m.project.uniqueness false)
  | _ => [[]]

theorem formula_positive (heads : List TypeVar) (selectors : Nat) (c : Coordinate) (a : CompareTy) :
    Positive (formula heads selectors c a) := by
  induction a with
  | var v => simp [formula, Positive]
  | unit | credit | prod | sum | fn => simp [formula, Positive]
  | modal a m ih =>
    cases c <;> simp only [formula]
    · exact ih
    · exact meet_positive ih (scalar_positive _ _ _ _)
    · exact meet_positive ih (scalar_positive _ _ _ _)
    · exact join_positive ih (scalar_positive _ _ _ _)
  | join a b iha ihb => exact join_positive iha ihb
  | meet a b iha ihb => exact meet_positive iha ihb

theorem formula_supported {heads : List TypeVar} {selectors cutoff modes : Nat}
    (hb : 6 * cutoff ≤ modes) {c : Coordinate} {a : CompareTy}
    (hs : ComparisonInterpolation.Supports (· ∈ heads) (fun v => v.index < cutoff) a) :
    Supported (List.range (heads.length + 2 * (selectors + modes))) (formula heads selectors c a) := by
  induction a with
  | var v =>
    intro i hi
    have hv : v ∈ heads := hs
    have he : i = heads.idxOf v := by simpa [formula, CNFPropagation.atoms] using hi
    subst i
    exact List.mem_range.mpr ((List.idxOf_lt_length_of_mem hv).trans_le (Nat.le_add_right _ _))
  | unit | credit | prod | sum | fn => simp [formula, Supported, CNFPropagation.atoms]
  | modal a m ih =>
    have hh := projection_atoms hb hs.2
    cases c <;> simp only [formula]
    · exact ih hs.1
    · exact meet_supported (ih hs.1) (scalar_supported hh.1 true)
    · exact meet_supported (ih hs.1) (scalar_supported hh.2.1 true)
    · exact join_supported (ih hs.1) (scalar_supported hh.2.2 false)
  | join a b iha ihb => exact join_supported (iha hs.1) (ihb hs.2)
  | meet a b iha ihb => exact meet_supported (iha hs.1) (ihb hs.2)

/-- Scalar formulas are evaluated on the common output parameter slice. -/
theorem formula_correct {heads : List TypeVar} {selectors cutoff modes : Nat}
    (hb : 6 * cutoff ≤ modes) {c : Coordinate} {a : CompareTy}
    (hs : ComparisonInterpolation.Supports (fun _ => True) (fun v => v.index < cutoff) a)
    {choice world : Nat → Bool} (hw : Slice heads.length (selectors + modes) choice world) :
    CNFHolds world (formula heads selectors c a) ↔
      rawValue c (fun i => choice (selectors + i)) (fun v => world (heads.idxOf v)) a = true := by
  induction a with
  | var | unit | credit | prod | sum | fn => simp [formula, rawValue, CNFHolds, ClauseHolds]
  | join a b iha ihb =>
    simp only [formula, join_correct, iha hs.1, ihb hs.2, rawValue, Bool.or_eq_true]
  | meet a b iha ihb =>
    simp only [formula, meet_correct, iha hs.1, ihb hs.2, rawValue, Bool.and_eq_true]
  | modal a m ih =>
    have hh := projection_atoms hb hs.2
    cases c <;> simp only [formula, rawValue, apply, Coordinate.modal, Coordinate.modalWith,
      SymbolicCNF.substitute_eval, BoolExpr.eval, id_eq, meet_correct, join_correct, ih hs.1,
      scalar_correct hh.1 hw true, scalar_correct hh.2.1 hw true, scalar_correct hh.2.2 hw false]
    all_goals simp

theorem rawValue_fixed {cutoff : Nat} {σ : CompareSubstitution}
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v) {a : CompareTy}
    (hs : ComparisonInterpolation.Supports (fun _ => True) (fun v => v.index < cutoff) a)
    (c : Coordinate) (inputs : Nat → Bool) (heads : TypeVar → Bool) :
    rawValue c (SchemeModeSynthesis.strategy σ.mode inputs) heads a = rawValue c inputs heads a := by
  induction a with
  | var | unit | credit | prod | sum | fn => rfl
  | join a b iha ihb | meet a b iha ihb => simp only [rawValue, iha hs.1, ihb hs.2]
  | modal a m ih =>
    simp only [rawValue, ih hs.1]
    exact apply_fixed c m σ.mode inputs _ (fun v hv => hf v (hs.2 v hv))

/-- Fixed image support provides the output-space factorization required by
joint synthesis, not merely coordinate dependence on arbitrary raw inputs. -/
theorem formula_strategy {heads : List TypeVar} {selectors cutoff modes : Nat}
    (hb : 6 * cutoff ≤ modes) {c : Coordinate} {a : CompareTy} {σ : CompareSubstitution}
    (hs : ComparisonInterpolation.Supports (fun _ => True) (fun v => v.index < cutoff) a)
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    {choice world inputs : Nat → Bool}
    (hm : ∀ i, choice (selectors + i) = SchemeModeSynthesis.strategy σ.mode inputs i)
    (hw : Slice heads.length (selectors + modes) choice world) :
    CNFHolds world (formula heads selectors c a) ↔
      rawValue c inputs (fun v => world (heads.idxOf v)) a = true := by
  rw [formula_correct hb hs hw]
  rw [show (fun i => choice (selectors+i)) = SchemeModeSynthesis.strategy σ.mode inputs from funext hm]
  rw [rawValue_fixed hf hs]

def coordinates {α : Type} (values : Coordinate → Fin count → α) (i : Fin (4 * count)) : α :=
  if h : i.val < count then values .unaffected ⟨i.val,h⟩
  else if h : i.val < 2 * count then values .locality ⟨i.val-count,by omega⟩
  else if h : i.val < 3 * count then values .affinity ⟨i.val-2*count,by omega⟩
  else values .uniqueness ⟨i.val-3*count,by have := i.isLt; omega⟩

@[simp] theorem coordinates_state {α : Type} (values : Coordinate → Fin count → α)
    (c : Coordinate) (i : Fin count) : coordinates values (state c i) = values c i := by
  have hi := i.isLt
  cases c <;> simp only [coordinates, state, coordinateNumber]
  all_goals split_ifs <;> try omega
  all_goals (congr 1; ext; simp only; omega)

theorem coordinates_bool (values : Coordinate → Fin count → Bool) :
    coordinates values = coordinateValue values := rfl

theorem coordinates_all {α : Type} {values : Coordinate → Fin count → α} {P : α → Prop}
    (h : ∀ c i, P (values c i)) (i : Fin (4*count)) : P (coordinates values i) := by
  unfold coordinates
  split_ifs <;> exact h _ _

theorem coordinates_relation {α β : Type} {left : Coordinate → Fin count → α}
    {right : Coordinate → Fin count → β} {R : α → β → Prop}
    (h : ∀ c i, R (left c i) (right c i)) (i : Fin (4*count)) :
    R (coordinates left i) (coordinates right i) := by
  unfold coordinates
  split_ifs <;> exact h _ _

def active (component : Bool) : Coordinate → Bool
  | .unaffected => true
  | .locality => component
  | .affinity | .uniqueness => !component

def store (component : Bool) (selectors : Nat) (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) : Store (4*g.leaves.length) :=
  Vector.ofFn fun (j : Fin (4 * g.leaves.length)) => coordinates (fun c (i : Fin g.leaves.length) => if active component c then
    formula g.heads selectors c (σ.type (.flex g.leaves[i])) else [[]]) j

@[simp] theorem store_state (component : Bool) (selectors : Nat) (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) (c : Coordinate) (i : Fin g.leaves.length) :
    (store component selectors g σ)[state c i] = if active component c then
      formula g.heads selectors c (σ.type (.flex g.leaves[i])) else [[]] := by
  simp only [store, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  exact coordinates_state _ c i

theorem store_positive (component : Bool) (selectors : Nat) (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) : (store component selectors g σ).Positive := by
  intro j
  simp only [store, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  apply coordinates_all (P := Positive) (i := j)
  intro c i
  split
  · exact formula_positive _ _ _ _
  · simp [Positive]

theorem store_supported {cutoff modes : Nat} {g : ComparisonGroups.Group} {σ : CompareSubstitution}
    (hb : 6 * cutoff ≤ modes)
    (hs : ∀ i : Fin g.leaves.length, ComparisonInterpolation.Supports (· ∈ g.heads)
      (fun v => v.index < cutoff) (σ.type (.flex g.leaves[i])))
    (component : Bool) (selectors : Nat) :
    (store component selectors g σ).Supported (g.heads.length+2*(selectors+modes)) := by
  intro j
  simp only [store, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  apply coordinates_all (P := Supported (List.range _)) (i := j)
  intro c i
  split
  · exact formula_supported hb (hs i)
  · simp [Supported, CNFPropagation.atoms]

theorem store_strategy {g : ComparisonGroups.Group} {σ : CompareSubstitution} {cutoff modes : Nat}
    (hb : 6 * cutoff ≤ modes) (hs : FixedImages cutoff σ)
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (component : Bool) (selectors : Nat) {choice world inputs : Nat → Bool}
    (hm : ∀ i, choice (selectors+i) = SchemeModeSynthesis.strategy σ.mode inputs i)
    (hw : Slice g.heads.length (selectors+modes) choice world) (i : Fin (4*g.leaves.length)) :
    CNFHolds world (store component selectors g σ)[i] ↔ axisValues component g σ world inputs i = true := by
  simp only [store, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  rw [axisValues, ← coordinates_bool]
  apply coordinates_relation (R := fun cs b => CNFHolds world cs ↔ b = true) ?_ i
  intro c j
  have hh := formula_strategy (heads := g.heads) hb (hs.1 (.flex g.leaves[j])) hf hm hw (c := c)
  cases c <;> cases component <;> simp_all only [active, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, CNFHolds, ClauseHolds, List.mem_singleton, forall_eq,
    List.not_mem_nil, false_and, exists_const, iff_self, Fin.getElem_fin]

theorem formula_nominal (heads : List TypeVar) (selectors : Nat) (a : CompareTy) :
    formula heads selectors .unaffected a = nominalFormula heads a := by
  induction a <;> simp_all only [formula, nominalFormula]

/-- Every coordinate store shares the exact same head-only nominal image. -/
theorem store_boundary (component : Bool) (selectors : Nat) (g : ComparisonGroups.Group)
    (σ : CompareSubstitution) (i : Fin g.leaves.length) :
    (store component selectors g σ)[state .unaffected i] = (nominalStore g σ)[i] := by
  rw [store_state]
  simp only [active, ↓reduceIte, formula_nominal, nominalStore,
    Fin.getElem_fin, Vector.getElem_ofFn]

theorem store_values {g : ComparisonGroups.Group} {σ : CompareSubstitution} {cutoff modes : Nat}
    (hb : 6 * cutoff ≤ modes) (hs : FixedImages cutoff σ)
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (component : Bool) (selectors : Nat) {choice world inputs : Nat → Bool}
    (hm : ∀ i, choice (selectors+i) = SchemeModeSynthesis.strategy σ.mode inputs i)
    (hw : Slice g.heads.length (selectors+modes) choice world) :
    ComparisonJointProgram.values (store component selectors g σ) world =
      axisValues component g σ world inputs := by
  funext i
  apply Bool.eq_iff_iff.mpr
  rw [ComparisonJointProgram.values_true]
  exact store_strategy hb hs hf component selectors hm hw i

/-- A raw finite clause valuation is reproduced exactly from the positive
store whenever its mode coordinates lie in the reserved parameter range. -/
theorem store_axis_valuation {g : ComparisonGroups.Group} {σ : CompareSubstitution}
    {cutoff modes : Nat} (hb : 6 * cutoff ≤ modes) (hs : FixedImages cutoff σ)
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (component : Bool) (selectors : Nat) {choice world inputs : Nat → Bool}
    (hm : ∀ i, choice (selectors+i) = SchemeModeSynthesis.strategy σ.mode inputs i)
    (hw : Slice g.heads.length (selectors+modes) choice world)
    {v : Nat} (hv : v < 4*g.leaves.length+g.heads.length+modes) :
    ComparisonJointEncoding.valuation
        (ComparisonJointProgram.values (store component selectors g σ) world)
        (ComparisonJointProgram.axisInputs g.heads.length selectors world) v =
      ComparisonJointAxes.valuation g.heads.length (axisValues component g σ)
        (SchemeModeSynthesis.strategy σ.mode) world inputs v := by
  rw [store_values hb hs hf component selectors hm hw]
  unfold ComparisonJointEncoding.valuation ComparisonJointAxes.valuation
  split_ifs with hstate hhead
  · rfl
  · simp [ComparisonJointProgram.axisInputs, show v-4*g.leaves.length < g.heads.length by omega]
  · have hi : v-4*g.leaves.length-g.heads.length < modes := by omega
    have hh := (hw (selectors+(v-4*g.leaves.length-g.heads.length)) (by omega)).1
    rw [hm] at hh
    simpa only [ComparisonJointProgram.axisInputs,
      show ¬v-4*g.leaves.length < g.heads.length by omega, ↓reduceIte, Nat.sub_sub] using hh

/-- The finite coordinate store satisfies the actual axis program for all
outputs of the common strategy and agrees with its head-only nominal store. -/
theorem store_sliceValid {g : ComparisonGroups.Group} {σ : CompareSubstitution}
    {cutoff modes selectors : Nat} {component : Bool} {clauses : CNF}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    (hb : 6 * cutoff ≤ modes) (hs : FixedImages cutoff σ)
    (hheads : ∀ i : Fin g.leaves.length, ComparisonInterpolation.Supports (· ∈ g.heads)
      (fun v => v.index < cutoff) (σ.type (.flex g.leaves[i])))
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hselectors : clauses.length ≤ selectors)
    (hsource : Supported (List.range (4*g.leaves.length+g.heads.length+modes)) clauses)
    (hc : ComparisonJointHorn.Linear (· < 4*g.leaves.length) clauses)
    (hown : ∀ headWorld inputs, CNFHolds
      (ComparisonJointAxes.encode
        (ComparisonJointAxisSummary.parameterWorld embedding choice (fun _ => false))
        (ComparisonJointAxes.valuation g.heads.length (axisValues component g σ)
          (SchemeModeSynthesis.strategy σ.mode) headWorld inputs))
      (ComparisonJointAxes.ownClauses ModalSynthesis.locality component
        (4*g.leaves.length) g.heads.length clauses)) :
    ∀ inputs, SliceValid g.heads.length (selectors+modes)
      (ComparisonJointAxisSummary.parameterWorld embedding choice (SchemeModeSynthesis.strategy σ.mode inputs))
      (ComparisonJointAxisSummary.program ModalSynthesis.locality component (4*g.leaves.length)
        g.heads.length selectors modes clauses) (store component selectors g σ) := by
  intro inputs
  apply (ComparisonJointProgram.axisProgram_sliceValid (store_supported hb hheads component selectors)
    hc _).mpr
  intro world hw
  apply (CNFPropagation.holds_congr ?_).mpr (hown world inputs)
  intro v hv
  rcases ComparisonJointAxes.ownClauses_atoms hv with ⟨i,hi,rfl⟩ | ⟨w,rfl,_,hw'⟩
  · have his : i < selectors := lt_of_lt_of_le hi hselectors
    simp only [ComparisonJointAxes.encode, show (2*i+1)/2=i by omega]
    have he := (hw i (by omega)).1
    simpa [ComparisonJointAxisSummary.parameterWorld, ComparisonJointAxisSummary.decode, his] using he
  · simp only [ComparisonJointAxes.encode, Nat.mul_mod_right, show 2*w/2=w by omega]
    exact store_axis_valuation hb hs hf component selectors
      (fun i => ComparisonJointAxisSummary.parameterWorld_mode embedding choice _ i) hw
      (List.mem_range.mp (hsource w hw'))

theorem store_boundaryAgreement (component : Bool) (selectors modes : Nat)
    (g : ComparisonGroups.Group) (σ : CompareSubstitution) (choice : Nat → Bool) :
    ComparisonBoundaryPropagation.BoundaryAgreement g.heads.length (selectors+modes) choice
      (ComparisonJointAssembly.boundary g.leaves.length) (store component selectors g σ)
      (nominalStore g σ) := by
  intro world _ i
  simp only [ComparisonJointAssembly.boundary, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  exact Iff.of_eq (congrArg (CNFHolds world) (by
    simpa only [Fin.getElem_fin] using (store_boundary component selectors g σ i)))

theorem axis_compile_complete {g : ComparisonGroups.Group} {σ : CompareSubstitution}
    {cutoff modes selectors : Nat} {component : Bool} {clauses : CNF}
    {embedding : Fin selectors → Fin constants} {choice : Fin constants → Bool}
    (hb : 6 * cutoff ≤ modes) (hs : FixedImages cutoff σ)
    (hheads : ∀ i : Fin g.leaves.length, ComparisonInterpolation.Supports (· ∈ g.heads)
      (fun v => v.index < cutoff) (σ.type (.flex g.leaves[i])))
    (hf : ∀ v, v.index < cutoff → σ.mode v = .var v)
    (hparameters : 0 < selectors+modes) (hselectors : clauses.length ≤ selectors)
    (hc : ComparisonJointHorn.Linear (· < 4*g.leaves.length) clauses)
    (hnominal : (nominalStore g σ).Supported g.heads.length)
    (hown : ∀ headWorld inputs, CNFHolds
      (ComparisonJointAxes.encode
        (ComparisonJointAxisSummary.parameterWorld embedding choice (fun _ => false))
        (ComparisonJointAxes.valuation g.heads.length (axisValues component g σ)
          (SchemeModeSynthesis.strategy σ.mode) headWorld inputs))
      (ComparisonJointAxes.ownClauses ModalSynthesis.locality component
        (4*g.leaves.length) g.heads.length clauses))
    (hsource : Supported (List.range (4*g.leaves.length+g.heads.length+modes)) clauses) :
    ComparisonJointGuarded.Holds choice (nominalStore g σ) (SchemeModeSynthesis.strategy σ.mode)
      (ComparisonJointAxisSummary.compile ModalSynthesis.locality component (4*g.leaves.length)
        g.heads.length selectors modes embedding clauses (ComparisonJointAssembly.boundary g.leaves.length)) := by
  apply (ComparisonJointSummary.compileGuarded_correct _ _ _ _ _ _).mpr
  intro inputs
  have hh := ComparisonBoundaryPropagation.summarize_complete_parametric hparameters
    (store_positive component selectors g σ) (store_supported hb hheads component selectors)
    (store_sliceValid hb hs hheads hf hselectors hsource hc hown inputs)
    (store_boundaryAgreement component selectors modes g σ _)
  exact ComparisonJointSummary.selected_of_slice hh hnominal

end ModalityInference.ComparisonJointCoordinateWitness
