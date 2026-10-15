import ModalityInference.Proofs.ComparisonJointGroupSupport

/-! Only the selected coordinate block can occur in the state part of a
compiled group observation. -/
namespace ModalityInference.ComparisonJointGroup

open ComparisonPropagation ComparisonControls

private def LeafStates (P : Fin count → Prop) : Leaf count → Prop
  | .fixed _ => True
  | .flex i => P i

private def ObligationStates (P : Fin count → Prop) : Obligation count → Prop
  | .lower i _ | .upper i _ => P i
  | .edge i j _ => P i ∧ P j
  | .check _ => True

private theorem leaf_states {heads : List TypeVar} {names : List Nat} {c : Coordinate}
    {v : TypeVar} {result : Leaf (4 * names.length)}
    (h : leaf heads names c v = .success result) :
    LeafStates (fun i => coordinateNumber c * names.length ≤ i.val ∧
      i.val < (coordinateNumber c + 1) * names.length) result := by
  unfold leaf at h
  cases v with
  | rigid n =>
    cases hi : index heads (.rigid n) <;> simp only [hi] at h <;> try contradiction
    cases h
    trivial
  | flex n =>
    cases hn : index names n with
    | some i =>
      simp only [hn, RunResult.success.injEq] at h
      cases h
      dsimp [LeafStates, state]
      simp only [Nat.add_mul, Nat.one_mul]
      have := i.isLt
      omega
    | none =>
      cases hi : index heads (.flex n) <;> simp only [hn, hi] at h <;> try contradiction
      cases h
      trivial

private theorem compileActions_states {left right : Action} {theory : CNF}
    {P : Fin count → Prop} {a b : Leaf count} (ha : LeafStates P a) (hb : LeafStates P b) :
    ∀ obligation ∈ compileActions left right theory a b, ObligationStates P obligation := by
  cases a <;> cases b <;>
    simp_all only [compileActions, List.forall_mem_cons, List.not_mem_nil, false_implies,
      ObligationStates, LeafStates, and_self]
  all_goals simp

private theorem bound_states {fuel : Nat} {heads : List TypeVar} {names : List Nat}
    {c : Coordinate} {theory : CNF} {pair : ComparisonGroups.Inequality}
    {result : List (Obligation (4 * names.length))}
    (h : bound fuel heads names c theory pair = .success result) :
    ∀ obligation ∈ result, ObligationStates (fun i => coordinateNumber c * names.length ≤ i.val ∧
      i.val < (coordinateNumber c + 1) * names.length) obligation := by
  unfold bound at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i a ha
  split at h <;> try contradiction
  rename_i b hb
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact compileActions_states (leaf_states ha) (leaf_states hb)

private theorem prepend_state {count : Nat} {states : Clause} {guards : CNF} {v : Nat}
    (hv : v ∈ CNFPropagation.atoms
      (ComparisonJointEncoding.prepend states (rename (count + ·) guards))) (hlt : v < count) :
    ∃ polarity, (v, polarity) ∈ states := by
  obtain ⟨clause, hc, polarity, hl⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨shifted, hs, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hl with hl | hl
  · exact ⟨polarity, hl⟩
  · obtain ⟨clause, _, rfl⟩ := List.mem_map.mp hs
    obtain ⟨⟨w, b⟩, _, he⟩ := List.mem_map.mp hl
    cases he
    dsimp only at hlt
    omega

private theorem encode_state {P : Fin count → Prop} {obligation : Obligation count}
    (ho : ObligationStates P obligation) {v : Nat} (hlt : v < count)
    (hv : v ∈ CNFPropagation.atoms (ComparisonJointEncoding.encode obligation)) : P ⟨v, hlt⟩ := by
  cases obligation with
  | lower i condition | upper i condition =>
    obtain ⟨polarity, hv⟩ := prepend_state hv hlt
    cases List.mem_singleton.mp hv
    exact ho
  | edge i j condition =>
    obtain ⟨polarity, hv⟩ := prepend_state hv hlt
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ho.1
    · cases List.mem_singleton.mp hv; exact ho.2
  | check condition =>
    have hv : v ∈ CNFPropagation.atoms (ComparisonJointEncoding.prepend []
        (rename (count + ·) condition)) := by
      simpa only [ComparisonJointEncoding.prepend, List.nil_append, List.map_id',
        ComparisonJointEncoding.encode] using hv
    obtain ⟨polarity, hv⟩ := prepend_state hv hlt
    simp at hv

private theorem mapM_property {α β : Type} {f : α → RunResult β}
    {xs : List α} {ys : List β} (h : xs.mapM f = .success ys) {P : β → Prop}
    (hp : ∀ x ∈ xs, ∀ y, f x = .success y → P y) : ∀ y ∈ ys, P y := by
  induction xs generalizing ys with
  | nil => cases h; simp
  | cons x xs ih =>
    simp only [List.mapM_cons, bind, pure, RunResult.bind] at h
    cases hx : f x <;> simp only [hx] at h <;> try contradiction
    next y =>
      cases hxs : xs.mapM f <;> simp only [hxs] at h <;> try contradiction
      next rest =>
        cases h
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hp x List.mem_cons_self _ hx
        · exact ih hxs (fun x hx => hp x (List.mem_cons_of_mem _ hx)) z hz

/-- The state prefix contains only the chosen observation block. -/
theorem coordinate_state_atoms {fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {c : Coordinate} {result : CNF}
    (h : coordinate fuel assumptions required g c = .success result)
    {v : Nat} (hv : v ∈ CNFPropagation.atoms result) (hlt : v < 4 * g.leaves.length) :
    coordinateNumber c * g.leaves.length ≤ v ∧ v < (coordinateNumber c + 1) * g.leaves.length := by
  unfold coordinate at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i goals hg
  cases h
  obtain ⟨clause, hc, polarity, hl⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨obligation, ho, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨output, hout, ho⟩ := List.mem_flatten.mp ho
  exact encode_state (mapM_property hg (fun _ _ _ h => bound_states h) output hout obligation ho)
    hlt (CNFPropagation.mem_atoms.mpr ⟨clause, hc, polarity, hl⟩)

/-- Nominal clauses mention exactly the nominal state block and retained head
prefix; inactive affected-coordinate slots and scalar atoms are absent. -/
theorem prepare_nominal_atoms {fuel : Nat} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {result : Input}
    (h : prepare fuel assumptions required g = .success result)
    {v : Nat} (hv : v ∈ CNFPropagation.atoms result.nominal) :
    v < g.leaves.length ∨
      4 * g.leaves.length ≤ v ∧ v < 4 * g.leaves.length + g.heads.length := by
  have hb := List.mem_range.mp ((prepare_supported h).1 v hv)
  by_cases hl : v < 4 * g.leaves.length
  · obtain ⟨_, _, _, hn, _⟩ := prepare_coordinates h
    have hc := coordinate_state_atoms hn hv hl
    exact .inl (by simpa only [coordinateNumber, Nat.zero_add, Nat.one_mul] using hc.2)
  · exact .inr ⟨by omega, hb⟩

end ModalityInference.ComparisonJointGroup
