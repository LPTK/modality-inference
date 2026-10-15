import ModalityInference.ComparisonJointGroup
import ModalityInference.Proofs.ComparisonJointEncoding
import ModalityInference.Proofs.Projection

/-! Exact compilation of collected opaque inequalities into four shared type
observations, retaining scalar guards and compatibility constraints. -/
namespace ModalityInference.ComparisonJointGroup

open ComparisonPropagation ComparisonControls

/-- The mode tail is shared by every observation and every flexible image. -/
def modes (heads : Nat) (parameters : Nat → Bool) : Nat → Bool :=
  fun i => parameters (heads + i)

def leafValue (heads : List TypeVar) (names : List Nat) (coordinate : Coordinate)
    (parameters : Nat → Bool) (values : Fin (4 * names.length) → Bool) (v : TypeVar) : Bool :=
  match v with
  | .flex n => match index names n with
      | some i => values (state coordinate i)
      | none => parameters (heads.idxOf v)
  | .rigid _ => parameters (heads.idxOf v)

def apply (coordinate : Coordinate) (parameters : Nat → Bool) (value : Bool) (m : ModExpr) : Bool :=
  (coordinate.modal (.const value) m).eval parameters

def fixedValue (heads : List TypeVar) (coordinate : Coordinate)
    (parameters : Nat → Bool) (a : ComparisonGroups.Atom) : Bool :=
  apply coordinate (modes heads.length parameters) (parameters (heads.idxOf a.head)) a.mode

def atomValue (heads : List TypeVar) (names : List Nat) (coordinate : Coordinate)
    (parameters : Nat → Bool) (values : Fin (4 * names.length) → Bool) (a : ComparisonGroups.Atom) : Bool :=
  apply coordinate (modes heads.length parameters)
    (leafValue heads names coordinate parameters values a.head) a.mode

def TheoryHolds (assumptions required : Bounds) (g : ComparisonGroups.Group)
    (coordinate : Coordinate) (parameters : Nat → Bool) : Prop :=
  (∀ pair ∈ g.assumptions,
    fixedValue g.heads coordinate parameters pair.1 = true →
      fixedValue g.heads coordinate parameters pair.2 = true) ∧
    (coordinate = .unaffected ∨ (guards assumptions required).eval (modes g.heads.length parameters) = true)

def CoordinateHolds (assumptions required : Bounds) (g : ComparisonGroups.Group)
    (coordinate : Coordinate) (parameters : Nat → Bool)
    (values : Fin (4 * g.leaves.length) → Bool) : Prop :=
  TheoryHolds assumptions required g coordinate parameters →
    ∀ pair ∈ g.goals,
      atomValue g.heads g.leaves coordinate parameters values pair.1 = true →
      atomValue g.heads g.leaves coordinate parameters values pair.2 = true

@[simp] theorem modeFormula_eval (heads : Nat) (e : BoolExpr) (parameters : Nat → Bool) :
    (modeFormula heads e).eval parameters = e.eval (modes heads parameters) := by
  simp only [modeFormula, SymbolicCNF.substitute_eval, BoolExpr.eval]
  rfl

theorem index_value [BEq α] {xs : List α} {x : α} {i : Fin xs.length}
    (h : index xs x = some i) : i.val = xs.idxOf x := by
  dsimp only [index] at h
  split at h
  · cases h
    rfl
  · cases h

theorem fixed_correct {heads : List TypeVar} {coordinate : Coordinate}
    {a : ComparisonGroups.Atom} {e : BoolExpr} (h : fixed heads coordinate a = .success e)
    (parameters : Nat → Bool) :
    e.eval parameters = fixedValue heads coordinate parameters a := by
  unfold fixed at h
  cases hi : index heads a.head with
  | none => simp [hi] at h
  | some i =>
    simp only [hi, RunResult.success.injEq] at h
    subst e
    have he := index_value hi
    cases coordinate <;>
      simp [fixedValue, apply, Coordinate.modal, Coordinate.modalWith,
        BoolExpr.eval, SymbolicCNF.substitute_eval, modes, he]

theorem action_correct {fuel heads : Nat} {coordinate : Coordinate} {m : ModExpr} {result : Action}
    (h : action fuel heads coordinate m = .success result) (parameters : Nat → Bool) (value : Bool) :
    result.Holds parameters (value = true) ↔
      apply coordinate (modes heads parameters) value m = true := by
  unfold action at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i lower hl
  split at h <;> try contradiction
  rename_i upper hu
  cases h
  rw [Action.Holds, CompactCNF.toCNF_correct hl, CompactCNF.toCNF_correct hu,
    modeFormula_eval, modeFormula_eval]
  cases coordinate <;>
    simp [lowerFormula, upperFormula, apply, Coordinate.modal, Coordinate.modalWith,
      SymbolicCNF.substitute_eval, BoolExpr.eval, Bool.or_eq_true, Bool.and_eq_true]

theorem compileActions_correct (left right : Action) (theory : CNF) (a b : Leaf count)
    (parameters : Nat → Bool) (values : Fin count → Prop) :
    (∀ obligation ∈ compileActions left right theory a b, obligation.Holds parameters values) ↔
      (CNFHolds parameters theory → left.Holds parameters (a.Holds parameters values) →
        right.Holds parameters (b.Holds parameters values)) := by
  cases a <;> cases b <;>
    simp only [compileActions, List.forall_mem_cons, Obligation.Holds,
      implies_correct, meet_correct, negate_correct, Leaf.Holds,
      Action.Holds, Action.apply, join_correct] <;> tauto

theorem leaf_correct {heads : List TypeVar} {names : List Nat} {coordinate : Coordinate}
    {v : TypeVar} {result : Leaf (4 * names.length)}
    (h : leaf heads names coordinate v = .success result)
    (parameters : Nat → Bool) (values : Fin (4 * names.length) → Bool) :
    result.Holds parameters (fun i => values i = true) ↔
      leafValue heads names coordinate parameters values v = true := by
  unfold leaf at h
  cases v with
  | rigid n =>
    cases hi : index heads (.rigid n) with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, RunResult.success.injEq] at h
      cases h
      simp [Leaf.Holds, CNFHolds, ClauseHolds, leafValue, index_value hi]
  | flex n =>
    cases hn : index names n with
    | some i =>
      simp only [hn, RunResult.success.injEq] at h
      cases h
      simp [leafValue, Leaf.Holds, hn]
    | none =>
      cases hi : index heads (.flex n) with
      | none => simp [hn, hi] at h
      | some i =>
        simp only [hn, hi, RunResult.success.injEq] at h
        cases h
        simp [Leaf.Holds, CNFHolds, ClauseHolds, leafValue, hn, index_value hi]

private instance : LawfulMonad RunResult := LawfulMonad.mk'
  (id_map := fun x => by cases x <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x _ _ => by cases x <;> rfl)

private theorem mapM_forall {α β : Type} {f : α → RunResult β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .success ys) (P : β → Prop) (Q : α → Prop)
    (he : ∀ x y, f x = .success y → (P y ↔ Q x)) :
    (∀ y ∈ ys, P y) ↔ ∀ x ∈ xs, Q x := by
  induction xs generalizing ys with
  | nil => cases h; simp
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hx : f x <;> simp only [hx] at h <;> try contradiction
    next y =>
      cases hxs : xs.mapM f <;> simp only [hxs] at h <;> try contradiction
      next rest =>
        cases h
        simp only [List.forall_mem_cons, he x y hx, ih hxs]

private theorem all_eval_true (es : List BoolExpr) (parameters : Nat → Bool) :
    (BoolExpr.all es).eval parameters = true ↔ ∀ e ∈ es, e.eval parameters = true := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

theorem fixedBound_correct {heads : List TypeVar} {coordinate : Coordinate}
    {pair : ComparisonGroups.Inequality} {result : BoolExpr}
    (h : fixedBound heads coordinate pair = .success result) (parameters : Nat → Bool) :
    result.eval parameters = true ↔
      (fixedValue heads coordinate parameters pair.1 = true →
        fixedValue heads coordinate parameters pair.2 = true) := by
  unfold fixedBound at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i left hl
  split at h <;> try contradiction
  rename_i right hr
  cases h
  rw [BoolExpr.eval_imp_true, fixed_correct hl, fixed_correct hr]

theorem theory_correct {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {c : Coordinate} {declared : List BoolExpr}
    (h : g.assumptions.mapM (fixedBound g.heads c) = .success declared)
    (parameters : Nat → Bool) :
    (theory c g.heads.length assumptions required declared).eval parameters = true ↔
      TheoryHolds assumptions required g c parameters := by
  have hd := mapM_forall h (fun e => e.eval parameters = true)
    (fun pair => fixedValue g.heads c parameters pair.1 = true →
      fixedValue g.heads c parameters pair.2 = true)
    (fun _ _ he => fixedBound_correct he parameters)
  have hb : (c == .unaffected) = true ↔ c = .unaffected := by cases c <;> decide
  simp only [theory, BoolExpr.eval, Bool.and_eq_true, all_eval_true, hd, TheoryHolds, hb]
  by_cases hc : c = .unaffected <;> simp [hc, BoolExpr.eval]

theorem bound_correct {fuel : Nat} {heads : List TypeVar} {names : List Nat}
    {c : Coordinate} {theory : CNF} {pair : ComparisonGroups.Inequality}
    {result : List (Obligation (4 * names.length))}
    (h : bound fuel heads names c theory pair = .success result)
    (parameters : Nat → Bool) (values : Fin (4 * names.length) → Bool) :
    (∀ obligation ∈ result, obligation.Holds parameters (fun i => values i = true)) ↔
      (CNFHolds parameters theory → atomValue heads names c parameters values pair.1 = true →
        atomValue heads names c parameters values pair.2 = true) := by
  unfold bound at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i a ha
  split at h <;> try contradiction
  rename_i b hb
  split at h <;> try contradiction
  rename_i left hl
  split at h <;> try contradiction
  rename_i right hr
  cases h
  rw [compileActions_correct, leaf_correct ha, leaf_correct hb,
    action_correct hl, action_correct hr]
  rfl

/-- Successful compilation is exactly the four-coordinate leaf obligation,
with declared heads and original scalar guards left in its antecedent. -/
theorem coordinate_correct {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {c : Coordinate} {result : CNF} (h : coordinate fuel assumptions required g c = .success result)
    (parameters : Nat → Bool) (values : Fin (4 * g.leaves.length) → Bool) :
    CNFHolds (ComparisonJointEncoding.valuation values parameters) result ↔
      CoordinateHolds assumptions required g c parameters values := by
  unfold coordinate at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i declared hd
  split at h <;> try contradiction
  rename_i clauses hc
  split at h <;> try contradiction
  rename_i goals hg
  cases h
  rw [ComparisonJointEncoding.encodeAll_correct]
  simp only [List.forall_mem_flatten]
  rw [mapM_forall hg _ _ (fun pair output he => bound_correct he parameters values)]
  rw [show CNFHolds parameters clauses ↔ TheoryHolds assumptions required g c parameters from
    (CompactCNF.toCNF_correct hc parameters).trans (theory_correct hd parameters)]
  simp only [CoordinateHolds]
  tauto

def Input.Holds (input : Input) (heads : Nat) (parameters : Nat → Bool)
    (values : Fin count → Bool) : Prop :=
  CNFHolds (ComparisonJointEncoding.valuation values parameters) input.nominal ∧
  CNFHolds (ComparisonJointEncoding.valuation values parameters) input.locality ∧
  CNFHolds (ComparisonJointEncoding.valuation values parameters) input.other ∧
  CNFHolds (modes heads parameters) input.scalar

def Compatible (values : Fin (4 * count) → Bool) : Prop :=
  (∀ i : Fin count, values (state .locality i) = true → values (state .unaffected i) = true) ∧
  (∀ i : Fin count, values (state .affinity i) = true → values (state .unaffected i) = true) ∧
  (∀ i : Fin count, values (state .unaffected i) = true → values (state .uniqueness i) = true)

def GroupHolds (assumptions required : Bounds) (g : ComparisonGroups.Group)
    (parameters : Nat → Bool) (values : Fin (4 * g.leaves.length) → Bool) : Prop :=
  (∀ c, CoordinateHolds assumptions required g c parameters values) ∧ Compatible values ∧
    ((boundsModeFormula assumptions).eval (modes g.heads.length parameters) = true →
      (boundsModeFormula required).eval (modes g.heads.length parameters) = true)

theorem sandwich_correct (left right : Coordinate) (parameters : Nat → Bool)
    (values : Fin (4 * count) → Bool) :
    CNFHolds (ComparisonJointEncoding.valuation values parameters) (sandwich left right count) ↔
      ∀ i : Fin count, values (state left i) = true → values (state right i) = true := by
  simp only [sandwich, CNFHolds, List.forall_mem_map, List.mem_finRange, true_implies]
  apply forall_congr' fun i => ?_
  simp only [clauseHolds_cons, ComparisonJointEncoding.valuation_state]
  have hn : ¬ClauseHolds (ComparisonJointEncoding.valuation values parameters) [] := by simp [ClauseHolds]
  simp only [hn, or_false]
  cases values (state left i) <;> simp

/-- One successful group compilation preserves all four modal observations,
their common nominal bounds, and the complete scalar obligation. -/
theorem prepare_correct {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (h : prepare fuel assumptions required g = .success result)
    (parameters : Nat → Bool) (values : Fin (4 * g.leaves.length) → Bool) :
    result.Holds g.heads.length parameters values ↔ GroupHolds assumptions required g parameters values := by
  unfold prepare at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i nominal hn
  split at h <;> try contradiction
  rename_i locality hl
  split at h <;> try contradiction
  rename_i affinity hf
  split at h <;> try contradiction
  rename_i uniqueness hu
  split at h <;> try contradiction
  rename_i scalar hs
  cases h
  simp only [Input.Holds, cnfHolds_append, coordinate_correct hn,
    coordinate_correct hl, coordinate_correct hf, coordinate_correct hu,
    sandwich_correct, CompactCNF.toCNF_correct hs, BoolExpr.eval_imp_true,
    GroupHolds, Compatible]
  have hall : (∀ c, CoordinateHolds assumptions required g c parameters values) ↔
      CoordinateHolds assumptions required g .unaffected parameters values ∧
      CoordinateHolds assumptions required g .locality parameters values ∧
      CoordinateHolds assumptions required g .affinity parameters values ∧
      CoordinateHolds assumptions required g .uniqueness parameters values := by
    constructor
    · intro hc; exact ⟨hc _, hc _, hc _, hc _⟩
    · rintro ⟨hn, hl, hf, hu⟩ c
      cases c <;> assumption
  rw [hall]
  tauto

/-- Every opaque endpoint is either a retained fixed head or one allocated leaf. -/
def HeadCovered (heads : List TypeVar) (names : List Nat) (v : TypeVar) : Prop :=
  v ∈ heads ∨ ∃ n ∈ names, v = .flex n

def Covered (g : ComparisonGroups.Group) : Prop :=
  (∀ pair ∈ g.assumptions, pair.1.head ∈ g.heads ∧ pair.2.head ∈ g.heads) ∧
  (∀ pair ∈ g.goals,
    HeadCovered g.heads g.leaves pair.1.head ∧ HeadCovered g.heads g.leaves pair.2.head)

theorem index_exists [BEq α] [LawfulBEq α] {values : List α} {value : α}
    (h : value ∈ values) : ∃ i, index values value = some i := by
  have hi := List.idxOf_lt_length_of_mem h
  exact ⟨⟨values.idxOf value, hi⟩, by simp [index, hi]⟩

theorem fixed_complete {heads : List TypeVar} {a : ComparisonGroups.Atom}
    (h : a.head ∈ heads) (c : Coordinate) : ∃ result, fixed heads c a = .success result := by
  obtain ⟨i, hi⟩ := index_exists h
  exact ⟨c.modalWith (heads.length + ·) (.atom i.val) a.mode, by simp [fixed, hi]⟩

theorem fixedBound_complete {heads : List TypeVar} {pair : ComparisonGroups.Inequality}
    (h : pair.1.head ∈ heads ∧ pair.2.head ∈ heads) (c : Coordinate) :
    ∃ result, fixedBound heads c pair = .success result := by
  obtain ⟨left, hl⟩ := fixed_complete h.1 c
  obtain ⟨right, hr⟩ := fixed_complete h.2 c
  exact ⟨.imp left right, by simp [fixedBound, hl, hr, bind, pure, RunResult.bind]⟩

theorem leaf_complete {heads : List TypeVar} {names : List Nat} {v : TypeVar}
    (h : HeadCovered heads names v) (c : Coordinate) :
    ∃ result, leaf heads names c v = .success result := by
  rcases h with hv | ⟨n, hn, rfl⟩
  · obtain ⟨i, hi⟩ := index_exists hv
    cases v with
    | rigid n => exact ⟨.fixed [[(i.val, true)]], by simp [leaf, hi]⟩
    | flex n =>
      cases hn : index names n with
      | some j => exact ⟨.flex (state c j), by simp [leaf, hn]⟩
      | none => exact ⟨.fixed [[(i.val, true)]], by simp [leaf, hn, hi]⟩
  · obtain ⟨i, hi⟩ := index_exists hn
    exact ⟨.flex (state c i), by simp [leaf, hi]⟩

theorem action_complete (heads : Nat) (c : Coordinate) (m : ModExpr) :
    ∃ n result, ∀ fuel ≥ n, action fuel heads c m = .success result := by
  obtain ⟨nl, lower, hl⟩ := CompactCNF.toCNF_complete (modeFormula heads (lowerFormula c m)) true
  obtain ⟨nu, upper, hu⟩ := CompactCNF.toCNF_complete (modeFormula heads (upperFormula c m)) true
  exact ⟨nl + nu, ⟨lower, upper⟩, fun fuel hf => by
    simp [action, hl fuel (by omega), hu fuel (by omega), bind, pure, RunResult.bind]⟩

theorem bound_complete {heads : List TypeVar} {names : List Nat}
    {pair : ComparisonGroups.Inequality}
    (h : HeadCovered heads names pair.1.head ∧ HeadCovered heads names pair.2.head)
    (c : Coordinate) (theory : CNF) :
    ∃ n result, ∀ fuel ≥ n, bound fuel heads names c theory pair = .success result := by
  obtain ⟨a, ha⟩ := leaf_complete h.1 c
  obtain ⟨b, hb⟩ := leaf_complete h.2 c
  obtain ⟨nl, left, hl⟩ := action_complete heads.length c pair.1.mode
  obtain ⟨nr, right, hr⟩ := action_complete heads.length c pair.2.mode
  exact ⟨nl + nr, compileActions left right theory a b, fun fuel hf => by
    simp [bound, ha, hb, hl fuel (by omega), hr fuel (by omega), bind, pure, RunResult.bind]⟩

private theorem mapM_success {α β : Type} (xs : List α) (f : α → RunResult β)
    (h : ∀ x ∈ xs, ∃ y, f x = .success y) : ∃ ys, xs.mapM f = .success ys := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ys, hys⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys, bind, pure, RunResult.bind]⟩

private theorem mapM_complete {α β : Type} (xs : List α) (f : Nat → α → RunResult β)
    (h : ∀ x ∈ xs, ∃ n y, ∀ fuel ≥ n, f fuel x = .success y) :
    ∃ n ys, ∀ fuel ≥ n, xs.mapM (f fuel) = .success ys := by
  induction xs with
  | nil => exact ⟨0, [], fun _ _ => rfl⟩
  | cons x xs ih =>
    obtain ⟨nx, y, hy⟩ := h x List.mem_cons_self
    obtain ⟨ns, ys, hys⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨nx + ns, y :: ys, fun fuel hf => by
      simp [List.mapM_cons, hy fuel (by omega), hys fuel (by omega), bind, pure, RunResult.bind]⟩

/-- Finite head coverage is sufficient for eventual compilation; modality
expressions retain all of their guards and need not be globally defined. -/
theorem coordinate_complete {g : ComparisonGroups.Group} (h : Covered g)
    (assumptions required : Bounds) (c : Coordinate) :
    ∃ n result, ∀ fuel ≥ n, coordinate fuel assumptions required g c = .success result := by
  obtain ⟨declared, hd⟩ := mapM_success g.assumptions (fixedBound g.heads c)
    (fun pair hp => fixedBound_complete (h.1 pair hp) c)
  obtain ⟨nt, theory, ht⟩ := CompactCNF.toCNF_complete
    (theory c g.heads.length assumptions required declared) true
  obtain ⟨ng, goals, hg⟩ := mapM_complete g.goals (fun fuel => bound fuel g.heads g.leaves c theory)
    (fun pair hp => bound_complete (h.2 pair hp) c theory)
  exact ⟨nt + ng, ComparisonJointEncoding.encodeAll goals.flatten, fun fuel hf => by
    simp [coordinate, hd, ht fuel (by omega), hg fuel (by omega), bind, pure, RunResult.bind]⟩

theorem prepare_complete {g : ComparisonGroups.Group} (h : Covered g)
    (assumptions required : Bounds) :
    ∃ n result, ∀ fuel ≥ n, prepare fuel assumptions required g = .success result := by
  obtain ⟨nn, nominal, hn⟩ := coordinate_complete h assumptions required .unaffected
  obtain ⟨nl, locality, hl⟩ := coordinate_complete h assumptions required .locality
  obtain ⟨nf, affinity, hf⟩ := coordinate_complete h assumptions required .affinity
  obtain ⟨nu, uniqueness, hu⟩ := coordinate_complete h assumptions required .uniqueness
  obtain ⟨ns, scalar, hs⟩ := CompactCNF.toCNF_complete
    (.imp (boundsModeFormula assumptions) (boundsModeFormula required)) true
  refine ⟨nn + nl + nf + nu + ns, ⟨nominal,
    locality ++ sandwich .locality .unaffected g.leaves.length,
    affinity ++ uniqueness ++ sandwich .affinity .unaffected g.leaves.length ++
      sandwich .unaffected .uniqueness g.leaves.length, scalar⟩, ?_⟩
  intro fuel hbudget
  simp [prepare, hn fuel (by omega), hl fuel (by omega), hf fuel (by omega),
    hu fuel (by omega), hs fuel (by omega), bind, pure, RunResult.bind]

theorem coordinate_linear {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {c : Coordinate} {result : CNF} (h : coordinate fuel assumptions required g c = .success result) :
    ComparisonJointHorn.Linear (· < 4 * g.leaves.length) result := by
  unfold coordinate at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact ComparisonJointEncoding.encodeAll_linear _

theorem sandwich_linear (left right : Coordinate) (count : Nat) :
    ComparisonJointHorn.Linear (· < 4 * count) (sandwich left right count) := by
  intro clause hc
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  intro v w b hv hw _ _
  grind

private theorem linear_append {P : Nat → Prop} {left right : CNF}
    (hl : ComparisonJointHorn.Linear P left) (hr : ComparisonJointHorn.Linear P right) :
    ComparisonJointHorn.Linear P (left ++ right) := by
  intro clause hc
  exact (List.mem_append.mp hc).elim (hl clause) (hr clause)

theorem prepare_linear {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (h : prepare fuel assumptions required g = .success result) :
    ComparisonJointHorn.Linear (· < 4 * g.leaves.length) result.nominal ∧
    ComparisonJointHorn.Linear (· < 4 * g.leaves.length) result.locality ∧
    ComparisonJointHorn.Linear (· < 4 * g.leaves.length) result.other := by
  unfold prepare at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i nominal hn
  split at h <;> try contradiction
  rename_i locality hl
  split at h <;> try contradiction
  rename_i affinity hf
  split at h <;> try contradiction
  rename_i uniqueness hu
  split at h <;> try contradiction
  cases h
  exact ⟨coordinate_linear hn, linear_append (coordinate_linear hl) (sandwich_linear _ _ _),
    linear_append (linear_append (linear_append (coordinate_linear hf) (coordinate_linear hu))
      (sandwich_linear _ _ _)) (sandwich_linear _ _ _)⟩

end ModalityInference.ComparisonJointGroup
