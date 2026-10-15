import ModalityInference.Proofs.ComparisonJointGroupInvariance

/-! Every observation emitted by the group compiler comes from its state and
head prefixes or an atom of an original scalar expression. -/
namespace ModalityInference.ComparisonJointGroup

open ComparisonPropagation ComparisonControls

def modeAtoms (c : Coordinate) (m : ModExpr) : List Nat :=
  (lowerFormula c m).atoms ++ (upperFormula c m).atoms

def coordinateAtoms (c : Coordinate) (assumptions required : Bounds)
    (g : ComparisonGroups.Group) : List Nat :=
  (if c == .unaffected then [] else (guards assumptions required).atoms) ++
    (g.assumptions ++ g.goals).flatMap fun pair => modeAtoms c pair.1.mode ++ modeAtoms c pair.2.mode

def atomDomain (count heads : Nat) (scalars : List Nat) : List Nat :=
  List.range (count + heads) ++ scalars.map (count + heads + ·)

private theorem supported_iff (domain : List Nat) (cs : CNF) :
    Supported domain cs ↔ ∀ c ∈ cs, ∀ literal ∈ c, literal.1 ∈ domain := by
  constructor
  · intro h c hc literal hl
    exact h _ (CNFPropagation.mem_atoms.mpr ⟨c, hc, literal.2, hl⟩)
  · intro h v hv
    obtain ⟨c, hc, p, hp⟩ := CNFPropagation.mem_atoms.mp hv
    exact h c hc (v, p) hp

private theorem append_supported {domain : List Nat} {a b : CNF}
    (ha : Supported domain a) (hb : Supported domain b) : Supported domain (a ++ b) := by
  rw [supported_iff] at ha hb ⊢
  intro c hc
  exact (List.mem_append.mp hc).elim (ha c) (hb c)

private theorem meet_supported {domain : List Nat} {a b : CNF}
    (ha : Supported domain a) (hb : Supported domain b) : Supported domain (meet a b) :=
  fun v hv => append_supported ha hb v (CompactCNF.clean_atoms hv)

private theorem negateClause_supported {domain : List Nat} {c : Clause}
    (h : ∀ literal ∈ c, literal.1 ∈ domain) : Supported domain (negateClause c) := by
  rw [supported_iff]
  intro d hd literal hl
  obtain ⟨⟨i, p⟩, hi, rfl⟩ := List.mem_map.mp hd
  simp only [List.mem_singleton] at hl
  cases hl
  exact h (i, p) hi

private theorem negate_supported {domain : List Nat} {cs : CNF}
    (h : Supported domain cs) : Supported domain (negate cs) := by
  rw [supported_iff] at h
  induction cs with
  | nil => simp [negate, Supported, CNFPropagation.atoms]
  | cons c cs ih =>
    exact join_supported (negateClause_supported (h c List.mem_cons_self))
      (ih (fun d hd => h d (List.mem_cons_of_mem _ hd)))

private theorem implies_supported {domain : List Nat} {a b : CNF}
    (ha : Supported domain a) (hb : Supported domain b) : Supported domain (implies a b) :=
  join_supported (negate_supported ha) hb

private theorem rename_supported {domain target : List Nat} {cs : CNF} {f : Nat → Nat}
    (h : Supported domain cs) (hf : ∀ i ∈ domain, f i ∈ target) : Supported target (rename f cs) := by
  rw [supported_iff] at h ⊢
  intro c hc literal hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨⟨i, p⟩, hi, he⟩ := List.mem_map.mp hl
  cases he
  exact hf i (h d hd (i, p) hi)

private theorem atomDomain_prefix {count heads v : Nat} {scalars : List Nat}
    (h : v < count + heads) : v ∈ atomDomain count heads scalars := by
  exact List.mem_append_left _ (List.mem_range.mpr h)

private theorem atomDomain_scalar {count heads v : Nat} {scalars : List Nat}
    (h : v ∈ scalars) : count + heads + v ∈ atomDomain count heads scalars := by
  exact List.mem_append_right _ (List.mem_map.mpr ⟨v, h, rfl⟩)

private theorem atomDomain_shift {count heads v : Nat} {scalars : List Nat}
    (h : v ∈ atomDomain 0 heads scalars) : count + v ∈ atomDomain count heads scalars := by
  rcases List.mem_append.mp h with h | h
  · exact atomDomain_prefix (by have := List.mem_range.mp h; omega)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp h
    simpa [Nat.add_assoc] using atomDomain_scalar (count := count) (heads := heads) hw

private theorem modeFormula_atoms {heads : Nat} {e : BoolExpr} {v : Nat}
    (h : v ∈ (modeFormula heads e).atoms) : ∃ w ∈ e.atoms, v = heads + w := by
  obtain ⟨w, hw, hv⟩ := SymbolicCNF.substitute_atoms h
  exact ⟨w, hw, by simpa [BoolExpr.atoms] using hv⟩

private theorem modalWith_atoms {heads i : Nat} {c : Coordinate} {m : ModExpr} {v : Nat}
    (h : v ∈ (c.modalWith (heads + ·) (.atom i) m).atoms) :
    v = i ∨ ∃ w ∈ modeAtoms c m, v = heads + w := by
  cases c <;> simp only [Coordinate.modalWith, BoolExpr.atoms, List.mem_dedup, List.mem_append,
    List.mem_singleton, List.not_mem_nil, or_false] at h
  · exact .inl h
  all_goals
    rcases h with h | h
    · exact .inl h
    · obtain ⟨w, hw, he⟩ := SymbolicCNF.substitute_atoms h
      refine .inr ⟨w, ?_, ?_⟩
      · simpa [modeAtoms, lowerFormula, upperFormula, BoolExpr.atoms] using hw
      · simpa [BoolExpr.atoms] using he

private def LeafSupported (domain : List Nat) : Leaf count → Prop
  | .fixed clauses => Supported domain clauses
  | .flex _ => True

private def ActionSupported (domain : List Nat) (a : Action) : Prop :=
  Supported domain a.lower ∧ Supported domain a.upper

private def ObligationSupported (domain : List Nat) : Obligation count → Prop
  | .lower _ condition | .edge _ _ condition | .upper _ condition | .check condition =>
      Supported domain condition

private theorem leaf_supported {heads : List TypeVar} {names scalars : List Nat} {c : Coordinate}
    {v : TypeVar} {result : Leaf (4 * names.length)}
    (h : leaf heads names c v = .success result) :
    LeafSupported (atomDomain 0 heads.length scalars) result := by
  unfold leaf at h
  cases v with
  | rigid n =>
    cases hi : index heads (.rigid n) with
    | none => simp [hi] at h
    | some i =>
      simp only [hi, RunResult.success.injEq] at h
      cases h
      intro v hv
      have he : v = i.val := by simpa [CNFPropagation.atoms] using hv
      subst v
      exact atomDomain_prefix (by simp [i.isLt])
  | flex n =>
    cases hn : index names n with
    | some i => simp only [hn, RunResult.success.injEq] at h; cases h; trivial
    | none =>
      cases hi : index heads (.flex n) with
      | none => simp [hn, hi] at h
      | some i =>
        simp only [hn, hi, RunResult.success.injEq] at h
        cases h
        intro v hv
        have he : v = i.val := by simpa [CNFPropagation.atoms] using hv
        subst v
        exact atomDomain_prefix (by simp [i.isLt])

private theorem fixed_supported {heads : List TypeVar} {c : Coordinate} {a : ComparisonGroups.Atom}
    {result : BoolExpr} {scalars : List Nat} (h : fixed heads c a = .success result)
    (hm : ∀ v ∈ modeAtoms c a.mode, v ∈ scalars) :
    ∀ v ∈ result.atoms, v ∈ atomDomain 0 heads.length scalars := by
  unfold fixed at h
  cases hi : index heads a.head with
  | none => simp [hi] at h
  | some i =>
    simp only [hi, RunResult.success.injEq] at h
    subst result
    intro v hv
    rcases modalWith_atoms hv with rfl | ⟨w, hw, rfl⟩
    · exact atomDomain_prefix (by simp [i.isLt])
    · simpa only [Nat.zero_add] using atomDomain_scalar (count := 0) (heads := heads.length) (hm w hw)

private theorem action_supported {fuel heads : Nat} {c : Coordinate} {m : ModExpr}
    {result : Action} {scalars : List Nat} (h : action fuel heads c m = .success result)
    (hm : ∀ v ∈ modeAtoms c m, v ∈ scalars) :
    ActionSupported (atomDomain 0 heads scalars) result := by
  unfold action at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i lower hl
  split at h <;> try contradiction
  rename_i upper hu
  cases h
  constructor
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := modeFormula_atoms (CompactCNF.toCNF_atoms hl hv)
    simpa only [Nat.zero_add] using atomDomain_scalar (count := 0) (heads := heads)
      (hm w (List.mem_append_left _ hw))
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := modeFormula_atoms (CompactCNF.toCNF_atoms hu hv)
    simpa only [Nat.zero_add] using atomDomain_scalar (count := 0) (heads := heads)
      (hm w (List.mem_append_right _ hw))

private theorem action_apply_supported {domain : List Nat} {a : Action} {c : CNF}
    (ha : ActionSupported domain a) (hc : Supported domain c) :
    Supported domain (a.apply c) :=
  meet_supported (join_supported hc ha.1) ha.2

private theorem compileActions_supported {domain : List Nat} {left right : Action}
    {theory : CNF} {a b : Leaf count}
    (hl : ActionSupported domain left) (hr : ActionSupported domain right)
    (ht : Supported domain theory) (ha : LeafSupported domain a) (hb : LeafSupported domain b) :
    ∀ obligation ∈ compileActions left right theory a b, ObligationSupported domain obligation := by
  cases a <;> cases b <;> simp only [compileActions, List.forall_mem_cons,
    List.not_mem_nil, false_implies, ObligationSupported, LeafSupported] at *
  · exact ⟨implies_supported ht (implies_supported (action_apply_supported hl ha)
      (action_apply_supported hr hb)), fun _ => True.intro⟩
  · exact ⟨meet_supported ht (meet_supported (action_apply_supported hl ha) (negate_supported hr.1)),
      implies_supported ht (implies_supported (action_apply_supported hl ha) hr.2), fun _ => True.intro⟩
  · exact ⟨implies_supported (meet_supported ht hl.2) (action_apply_supported hr hb),
      implies_supported ht (implies_supported (meet_supported hl.1 hl.2) (action_apply_supported hr hb)), fun _ => True.intro⟩
  · exact ⟨meet_supported ht (meet_supported (meet_supported hl.1 hl.2) (negate_supported hr.1)),
      meet_supported ht (meet_supported hl.2 (negate_supported hr.1)),
      implies_supported (meet_supported ht hl.2) hr.2,
      implies_supported ht (implies_supported (meet_supported hl.1 hl.2) hr.2), fun _ => True.intro⟩

private theorem fixedBound_supported {heads : List TypeVar} {c : Coordinate}
    {pair : ComparisonGroups.Inequality} {result : BoolExpr} {scalars : List Nat}
    (h : fixedBound heads c pair = .success result)
    (hm : ∀ v ∈ modeAtoms c pair.1.mode ++ modeAtoms c pair.2.mode, v ∈ scalars) :
    ∀ v ∈ result.atoms, v ∈ atomDomain 0 heads.length scalars := by
  unfold fixedBound at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i left hl
  split at h <;> try contradiction
  rename_i right hr
  cases h
  intro v hv
  simp only [BoolExpr.atoms, List.mem_dedup, List.mem_append] at hv
  rcases hv with hv | hv
  · exact fixed_supported hl (fun i hi => hm i (List.mem_append_left _ hi)) v hv
  · exact fixed_supported hr (fun i hi => hm i (List.mem_append_right _ hi)) v hv

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

private theorem all_atoms_supported {domain : List Nat} {es : List BoolExpr}
    (h : ∀ e ∈ es, ∀ v ∈ e.atoms, v ∈ domain) :
    ∀ v ∈ (BoolExpr.all es).atoms, v ∈ domain := by
  induction es with
  | nil => simp [BoolExpr.all, BoolExpr.atoms]
  | cons e es ih =>
    intro v hv
    simp only [BoolExpr.all, List.foldr_cons, BoolExpr.atoms, List.mem_dedup, List.mem_append] at hv
    exact hv.elim (h e List.mem_cons_self v)
      (ih (fun e he => h e (List.mem_cons_of_mem _ he)) v)

private theorem theory_supported {heads : Nat} {assumptions required : Bounds} {c : Coordinate}
    {declared : List BoolExpr} {scalars : List Nat}
    (hd : ∀ e ∈ declared, ∀ v ∈ e.atoms, v ∈ atomDomain 0 heads scalars)
    (hg : c ≠ .unaffected → ∀ v ∈ (guards assumptions required).atoms, v ∈ scalars) :
    ∀ v ∈ (theory c heads assumptions required declared).atoms,
      v ∈ atomDomain 0 heads scalars := by
  have hbe : (c == .unaffected) = true ↔ c = .unaffected := by cases c <;> decide
  intro v hv
  simp only [theory, BoolExpr.atoms, List.mem_dedup, List.mem_append, hbe] at hv
  rcases hv with hv | hv
  · exact all_atoms_supported hd v hv
  · by_cases hc : c = .unaffected
    · simp [hc, BoolExpr.atoms] at hv
    · simp only [hc, if_false] at hv
      obtain ⟨w, hw, rfl⟩ := modeFormula_atoms hv
      simpa only [Nat.zero_add] using atomDomain_scalar (count := 0) (heads := heads) (hg hc w hw)

private theorem bound_supported {fuel : Nat} {heads : List TypeVar} {names scalars : List Nat}
    {c : Coordinate} {theory : CNF} {pair : ComparisonGroups.Inequality}
    {result : List (Obligation (4 * names.length))}
    (h : bound fuel heads names c theory pair = .success result)
    (ht : Supported (atomDomain 0 heads.length scalars) theory)
    (hm : ∀ v ∈ modeAtoms c pair.1.mode ++ modeAtoms c pair.2.mode, v ∈ scalars) :
    ∀ obligation ∈ result, ObligationSupported (atomDomain 0 heads.length scalars) obligation := by
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
  exact compileActions_supported
    (action_supported hl (fun v hv => hm v (List.mem_append_left _ hv)))
    (action_supported hr (fun v hv => hm v (List.mem_append_right _ hv)))
    ht (leaf_supported ha) (leaf_supported hb)

private theorem prepend_supported {count heads : Nat} {scalars : List Nat}
    {states : Clause} {guards : CNF}
    (hs : ∀ literal ∈ states, literal.1 < count)
    (hg : Supported (atomDomain 0 heads scalars) guards) :
    Supported (atomDomain count heads scalars)
      (ComparisonJointEncoding.prepend states (rename (count + ·) guards)) := by
  have hg := rename_supported hg (fun _ hv => atomDomain_shift (count := count) hv)
  rw [supported_iff] at hg ⊢
  intro c hc literal hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hl with hl | hl
  · exact atomDomain_prefix (by have := hs literal hl; omega)
  · exact hg d hd literal hl

private theorem encode_supported {heads : Nat} {scalars : List Nat} {obligation : Obligation count}
    (h : ObligationSupported (atomDomain 0 heads scalars) obligation) :
    Supported (atomDomain count heads scalars) (ComparisonJointEncoding.encode obligation) := by
  cases obligation with
  | lower i condition =>
    apply prepend_supported (hg := negate_supported h)
    intro literal hl
    cases List.mem_singleton.mp hl
    exact i.isLt
  | edge i j condition =>
    apply prepend_supported (hg := negate_supported h)
    intro literal hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact i.isLt
    · cases List.mem_singleton.mp hl
      exact j.isLt
  | upper i condition =>
    apply prepend_supported (hg := h)
    intro literal hl
    cases List.mem_singleton.mp hl
    exact i.isLt
  | check condition => exact rename_supported h (fun _ hv => atomDomain_shift hv)

private theorem encodeAll_supported {heads : Nat} {scalars : List Nat}
    {obligations : List (Obligation count)}
    (h : ∀ obligation ∈ obligations, ObligationSupported (atomDomain 0 heads scalars) obligation) :
    Supported (atomDomain count heads scalars) (ComparisonJointEncoding.encodeAll obligations) := by
  rw [supported_iff]
  intro clause hc literal hl
  obtain ⟨obligation, ho, hc⟩ := List.mem_flatMap.mp hc
  exact encode_supported (h obligation ho) _ (CNFPropagation.mem_atoms.mpr ⟨clause, hc, literal.2, hl⟩)

private theorem coordinateAtoms_modes {c : Coordinate} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} {pair : ComparisonGroups.Inequality}
    (hp : pair ∈ g.assumptions ++ g.goals) :
    ∀ v ∈ modeAtoms c pair.1.mode ++ modeAtoms c pair.2.mode,
      v ∈ coordinateAtoms c assumptions required g := by
  intro v hv
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨pair, hp, hv⟩)

private theorem coordinateAtoms_guards {c : Coordinate} {assumptions required : Bounds}
    {g : ComparisonGroups.Group} (hc : c ≠ .unaffected) :
    ∀ v ∈ (guards assumptions required).atoms, v ∈ coordinateAtoms c assumptions required g := by
  have he : (c == .unaffected) = true ↔ c = .unaffected := by cases c <;> decide
  intro v hv
  exact List.mem_append_left _ (by simpa only [he, hc, if_false] using hv)

/-- Actual coordinate compilation has a finite atom domain determined entirely
by allocated states, retained heads, and the original scalar syntax. -/
theorem coordinate_supported {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {c : Coordinate} {result : CNF} (h : coordinate fuel assumptions required g c = .success result) :
    Supported (atomDomain (4 * g.leaves.length) g.heads.length
      (coordinateAtoms c assumptions required g)) result := by
  unfold coordinate at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  rename_i declared hd
  split at h <;> try contradiction
  rename_i clauses hc
  split at h <;> try contradiction
  rename_i goals hg
  cases h
  have ht : Supported (atomDomain 0 g.heads.length (coordinateAtoms c assumptions required g)) clauses := by
    intro v hv
    apply theory_supported (mapM_property hd (fun pair hp _ h =>
      fixedBound_supported h (coordinateAtoms_modes (List.mem_append_left _ hp))))
      coordinateAtoms_guards v (CompactCNF.toCNF_atoms hc hv)
  apply encodeAll_supported
  intro obligation ho
  obtain ⟨output, hout, ho⟩ := List.mem_flatten.mp ho
  exact mapM_property hg (fun pair hp _ h => bound_supported h ht
    (coordinateAtoms_modes (List.mem_append_right _ hp))) output hout obligation ho

@[simp] theorem coordinateAtoms_unaffected (assumptions required : Bounds) (g : ComparisonGroups.Group) :
    coordinateAtoms .unaffected assumptions required g = [] := by
  have he : (Coordinate.unaffected == .unaffected) = true := rfl
  simp [coordinateAtoms, he, modeAtoms, lowerFormula, upperFormula, BoolExpr.atoms]

private theorem atomDomain_mono {count heads : Nat} {left right : List Nat}
    (h : ∀ v ∈ left, v ∈ right) : ∀ v ∈ atomDomain count heads left, v ∈ atomDomain count heads right := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact List.mem_append_left _ hv
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact atomDomain_scalar (h w hw)

theorem sandwich_supported (a b : Coordinate) (count heads : Nat) (scalars : List Nat) :
    Supported (atomDomain (4 * count) heads scalars) (sandwich a b count) := by
  rw [supported_iff]
  intro clause hc literal hl
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_cons.mp hl with rfl | hl
  · exact atomDomain_prefix (by have := (state a i).isLt; omega)
  · cases List.mem_singleton.mp hl
    exact atomDomain_prefix (by have := (state b i).isLt; omega)

/-- The nominal output has no scalar atoms. The locality and other outputs
contain only atoms from their actual input guards and matching projections. -/
theorem prepare_supported {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {result : Input} (h : prepare fuel assumptions required g = .success result) :
    Supported (List.range (4 * g.leaves.length + g.heads.length)) result.nominal ∧
    Supported (atomDomain (4 * g.leaves.length) g.heads.length
      (coordinateAtoms .locality assumptions required g)) result.locality ∧
    Supported (atomDomain (4 * g.leaves.length) g.heads.length
      (coordinateAtoms .affinity assumptions required g ++ coordinateAtoms .uniqueness assumptions required g))
      result.other ∧
    Supported (guards assumptions required).atoms result.scalar := by
  obtain ⟨_, _, _, hn, hl, hf, hu, hs, hle, hoe⟩ := prepare_coordinates h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [coordinateAtoms_unaffected, atomDomain, List.map_nil, List.append_nil] using
      coordinate_supported hn
  · rw [hle]
    exact append_supported (coordinate_supported hl) (sandwich_supported _ _ _ _ _)
  · rw [hoe]
    apply append_supported
    · apply append_supported
      · apply append_supported
        · exact fun v hv => atomDomain_mono (fun _ hw => List.mem_append_left _ hw) v
            (coordinate_supported hf v hv)
        · exact fun v hv => atomDomain_mono (fun _ hw => List.mem_append_right _ hw) v
            (coordinate_supported hu v hv)
      · exact sandwich_supported _ _ _ _ _
    · exact sandwich_supported _ _ _ _ _
  · intro v hv
    simpa only [guards, BoolExpr.atoms] using CompactCNF.toCNF_atoms hs hv

/-- A finite input atom bound yields the exact arithmetic namespace bound
required by signed-parameter encoding. -/
theorem atomDomain_bound {count heads limit : Nat} {scalars : List Nat}
    (h : ∀ v ∈ scalars, v < limit) : ∀ v ∈ atomDomain count heads scalars, v < count + heads + limit := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · have := List.mem_range.mp hv
    omega
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have := h w hw
    omega

/-- Output scalar atoms have concrete provenance, not merely a bound chosen
after compilation. -/
theorem coordinate_atoms {fuel : Nat} {assumptions required : Bounds} {g : ComparisonGroups.Group}
    {c : Coordinate} {result : CNF} (h : coordinate fuel assumptions required g c = .success result)
    {v : Nat} (hv : v ∈ CNFPropagation.atoms result) :
    v < 4 * g.leaves.length + g.heads.length ∨
      ∃ w ∈ coordinateAtoms c assumptions required g,
        v = 4 * g.leaves.length + g.heads.length + w := by
  rcases List.mem_append.mp (coordinate_supported h v hv) with hv | hv
  · exact .inl (List.mem_range.mp hv)
  · obtain ⟨w, hw, he⟩ := List.mem_map.mp hv
    exact .inr ⟨w, hw, he.symm⟩

end ModalityInference.ComparisonJointGroup
