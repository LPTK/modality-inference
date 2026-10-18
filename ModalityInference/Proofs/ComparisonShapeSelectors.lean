import ModalityInference.ComparisonShapeSelectors
import ModalityInference.Proofs.ComparisonShapeCandidates
import ModalityInference.Proofs.CompactCNF

/-! Shared selectors encode and decode simultaneous finite shape assignments.
Their compiled theory and every enabled structural branch are exact. -/

namespace ModalityInference.ComparisonShapeSelectors

private theorem all_eval (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all es).eval world = true ↔ ∀e∈es, e.eval world = true := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

private theorem any_eval (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any es).eval world = true ↔ ∃e∈es, e.eval world = true := by
  induction es <;> simp_all [BoolExpr.any, BoolExpr.eval]

private theorem not_both_eval (a b : BoolExpr) (world : Nat → Bool) :
    (BoolExpr.imp a (.imp b (.const false))).eval world = true ↔
      ¬(a.eval world = true ∧ b.eval world = true) := by
  cases ha : a.eval world <;> cases hb : b.eval world <;> simp [BoolExpr.eval, ha, hb]

private theorem any_map_eval {α : Type} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any (xs.map f)).eval world = true ↔ ∃x∈xs, (f x).eval world = true := by
  rw [any_eval]
  constructor
  · rintro ⟨e, he, hv⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    exact ⟨x, hx, hv⟩
  · rintro ⟨x, hx, hv⟩
    exact ⟨f x, List.mem_map.mpr ⟨x, hx, rfl⟩, hv⟩

private theorem pair_eval (layout : Layout) (world : Nat → Bool) (v : TypeVar)
    (i j : Fin layout.choices.length) :
    (if i=j then BoolExpr.const true else
      .imp (.atom (layout.atom v i)) (.imp (.atom (layout.atom v j)) (.const false))).eval world = true ↔
    (i≠j → ¬(world (layout.atom v i)=true ∧ world (layout.atom v j)=true)) := by
  by_cases h : i=j
  · simp [h, BoolExpr.eval]
  · simp only [h, if_false, ne_eq, not_false_eq_true, true_implies]
    exact not_both_eval (.atom (layout.atom v i)) (.atom (layout.atom v j)) world

theorem Layout.one_correct (layout : Layout) (world : Nat → Bool) (v : TypeVar) :
    (layout.one v).eval world = true ↔
      ∃!i : Fin layout.choices.length, world (layout.atom v i) = true := by
  have he : (layout.one v).eval world = true ↔
      (∃i : Fin layout.choices.length, world (layout.atom v i) = true) ∧
      ∀i j : Fin layout.choices.length, i ≠ j →
        ¬(world (layout.atom v i) = true ∧ world (layout.atom v j) = true) := by
    change (_ && _) = true ↔ _
    rw [Bool.and_eq_true, any_map_eval, all_eval]
    simp only [List.forall_mem_flatMap, List.forall_mem_map, List.mem_finRange,
      forall_true_left, true_and, pair_eval, BoolExpr.eval]
  rw [he]
  constructor
  · rintro ⟨⟨i, hi⟩, huniq⟩
    exact ⟨i, hi, fun j hj => by by_contra hne; exact huniq j i hne ⟨hj, hi⟩⟩
  · rintro ⟨i, hi, huniq⟩
    exact ⟨⟨i, hi⟩, fun j k hne ⟨hj, hk⟩ => hne ((huniq j hj).trans (huniq k hk).symm)⟩

theorem Layout.theory_correct (layout : Layout) (world : Nat → Bool) :
    layout.theory.eval world = true ↔
      ∀v∈layout.parameters, ∃!i : Fin layout.choices.length, world (layout.atom v i) = true := by
  simp only [Layout.theory, all_eval, List.forall_mem_map, Layout.one_correct]

theorem Layout.atom_injective {layout : Layout} {v w : TypeVar}
    (hv : v∈layout.parameters) (hw : w∈layout.parameters) {i j : Nat}
    (hi : i<layout.choices.length) (hj : j<layout.choices.length)
    (he : layout.atom v i = layout.atom w j) : v=w ∧ i=j := by
  have hn : 0<layout.choices.length := Nat.zero_lt_of_lt hi
  have he' : layout.choices.length * layout.parameters.idxOf v + i =
      layout.choices.length * layout.parameters.idxOf w + j := by
    exact Nat.add_left_cancel (by simpa only [Layout.atom, Nat.add_assoc] using he)
  have hi' := congrArg (· / layout.choices.length) he'
  simp only [Nat.mul_add_div hn, Nat.div_eq_of_lt hi, Nat.div_eq_of_lt hj, Nat.add_zero] at hi'
  have hiv := List.idxOf_lt_length_of_mem hv
  have hiw := List.idxOf_lt_length_of_mem hw
  have hv' : layout.parameters[layout.parameters.idxOf v] = v := by
    simpa only [List.idxOf, beq_iff_eq] using
      (List.findIdx_getElem (xs := layout.parameters) (p := (· == v))
        (w := List.idxOf_lt_length_of_mem hv))
  have hw' : layout.parameters[layout.parameters.idxOf w] = w := by
    simpa only [List.idxOf, beq_iff_eq] using
      (List.findIdx_getElem (xs := layout.parameters) (p := (· == w))
        (w := List.idxOf_lt_length_of_mem hw))
  have hv'' : layout.parameters[layout.parameters.idxOf w] = v := by
    simpa only [hi'] using hv'
  exact ⟨hv''.symm.trans hw', by rw [hi'] at he'; omega⟩

theorem Layout.encode_atom {layout : Layout} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v∈layout.parameters, ρ v∈layout.choices) {v : TypeVar}
    (hv : v∈layout.parameters) {i : Nat} (hi : i<layout.choices.length) :
    layout.encode ρ (layout.atom v i) = true ↔ i=layout.choices.idxOf (ρ v) := by
  simp only [Layout.encode, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨rfl, hi⟩ := Layout.atom_injective hv hw hi
      (List.idxOf_lt_length_of_mem (hρ w hw)) he
    exact hi
  · intro he
    exact ⟨v, hv, by rw [he]⟩

theorem Layout.theory_encode {layout : Layout} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v∈layout.parameters, ρ v∈layout.choices) :
    layout.theory.eval (layout.encode ρ) = true := by
  apply layout.theory_correct _ |>.mpr
  intro v hv
  let i : Fin layout.choices.length :=
    ⟨layout.choices.idxOf (ρ v), List.idxOf_lt_length_of_mem (hρ v hv)⟩
  refine ⟨i, (Layout.encode_atom hρ hv i.isLt).mpr rfl, ?_⟩
  intro j hj
  exact Fin.ext ((Layout.encode_atom hρ hv j.isLt).mp hj)

theorem Layout.decode_active {layout : Layout} {world : Nat → Bool}
    (h : layout.theory.eval world = true) {v : TypeVar} (hv : v∈layout.parameters)
    (i : Fin layout.choices.length) (hi : world (layout.atom v i)=true) :
    layout.decode world v = layout.choices[i] := by
  obtain ⟨j, hj, hu⟩ := (layout.theory_correct world).mp h v hv
  unfold Layout.decode
  cases hf : (List.finRange layout.choices.length).find? (fun (i : Fin layout.choices.length) => world (layout.atom v i)) with
  | none =>
    exact (List.find?_eq_none.mp hf i (by simp) hi).elim
  | some k =>
    have hk := List.find?_some hf
    have he : k=i := (hu k hk).trans (hu i hi).symm
    simp only [he]

theorem Layout.decode_mem {layout : Layout} {world : Nat → Bool}
    (h : layout.theory.eval world = true) {v : TypeVar} (hv : v∈layout.parameters) :
    layout.decode world v ∈ layout.choices := by
  obtain ⟨i, hi, _⟩ := (layout.theory_correct world).mp h v hv
  rw [Layout.decode_active h hv i hi]
  exact List.getElem_mem i.isLt

theorem Layout.decode_encode {layout : Layout} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v∈layout.parameters, ρ v∈layout.choices) {v : TypeVar} (hv : v∈layout.parameters) :
    layout.decode (layout.encode ρ) v = ρ v := by
  let i : Fin layout.choices.length :=
    ⟨layout.choices.idxOf (ρ v), List.idxOf_lt_length_of_mem (hρ v hv)⟩
  rw [Layout.decode_active (Layout.theory_encode hρ) hv i
    ((Layout.encode_atom hρ hv i.isLt).mpr rfl)]
  simpa only [i, List.idxOf, beq_iff_eq] using
    (List.findIdx_getElem (xs := layout.choices) (p := (· == ρ v)) (w := i.isLt))

theorem Layout.compile_correct {layout : Layout} {fuel : Nat} {clauses : CNF}
    (h : layout.compile fuel = .success clauses) (world : Nat → Bool) :
    CNFHolds world clauses ↔
      ∀v∈layout.parameters, ∃!i : Fin layout.choices.length, world (layout.atom v i) = true :=
  (CompactCNF.toCNF_correct h world).trans (layout.theory_correct world)

theorem Layout.compile_complete (layout : Layout) :
    ∃threshold clauses, ∀fuel≥threshold, layout.compile fuel = .success clauses :=
  CompactCNF.toCNF_complete layout.theory true

theorem Layout.branches_sound (layout : Layout) (world : Nat → Bool)
    (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hselected : ∀v∈s.vars, ∀i : Fin layout.choices.length,
      world (layout.atom v i)=true → layout.choices[i]=ρ v) :
    ∀b∈layout.branches s, b.guard.eval world=true → b.shape=s.subst ρ := by
  induction s with
  | var v =>
    intro b hb hg
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
    exact hselected v (by simp [ComparisonShape.vars]) i hg
  | unit | credit =>
    intro b hb hg
    obtain rfl := List.mem_singleton.mp hb
    rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    intro branch hb hg
    obtain ⟨left, hl, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨right, hr, rfl⟩ := List.mem_map.mp hb
    have hh : left.guard.eval world=true ∧ right.guard.eval world=true := by
      simpa only [BoolExpr.eval, Bool.and_eq_true] using hg
    exact congrArg₂ _
      (iha (fun v hv => hselected v (List.mem_append_left _ hv)) left hl hh.1)
      (ihb (fun v hv => hselected v (List.mem_append_right _ hv)) right hr hh.2)

theorem Layout.branches_complete (layout : Layout) (world : Nat → Bool)
    (ρ : TypeVar → ComparisonShape) (s : ComparisonShape)
    (hselected : ∀v∈s.vars, ∃i : Fin layout.choices.length,
      world (layout.atom v i)=true ∧ layout.choices[i]=ρ v) :
    ∃b∈layout.branches s, b.guard.eval world=true ∧ b.shape=s.subst ρ := by
  induction s with
  | var v =>
    obtain ⟨i, hi, he⟩ := hselected v (by simp [ComparisonShape.vars])
    exact ⟨_, List.mem_map.mpr ⟨i, by simp, rfl⟩, hi, he⟩
  | unit => exact ⟨_, List.mem_singleton_self _, rfl, rfl⟩
  | credit => exact ⟨_, List.mem_singleton_self _, rfl, rfl⟩
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    obtain ⟨left, hl, hgl, hel⟩ := iha (fun v hv => hselected v (List.mem_append_left _ hv))
    obtain ⟨right, hr, hgr, her⟩ := ihb (fun v hv => hselected v (List.mem_append_right _ hv))
    exact ⟨_, List.mem_flatMap.mpr ⟨left, hl, List.mem_map.mpr ⟨right, hr, rfl⟩⟩,
      (by simpa only [BoolExpr.eval, Bool.and_eq_true] using And.intro hgl hgr),
      congrArg₂ _ hel her⟩

theorem Layout.branches_decoded {layout : Layout} {world : Nat → Bool}
    (h : layout.theory.eval world=true) (s : ComparisonShape)
    (hscope : ∀v∈s.vars, v∈layout.parameters) :
    (∀b∈layout.branches s, b.guard.eval world=true → b.shape=s.subst (layout.decode world)) ∧
    (∃b∈layout.branches s, b.guard.eval world=true ∧ b.shape=s.subst (layout.decode world)) := by
  constructor
  · exact layout.branches_sound world (layout.decode world) s
      (fun v hv i hi => (Layout.decode_active h (hscope v hv) i hi).symm)
  · apply layout.branches_complete
    intro v hv
    obtain ⟨i, hi, _⟩ := (layout.theory_correct world).mp h v (hscope v hv)
    exact ⟨i, hi, (Layout.decode_active h (hscope v hv) i hi).symm⟩

theorem Layout.branches_encoded {layout : Layout} {ρ : TypeVar → ComparisonShape}
    (hρ : ∀v∈layout.parameters, ρ v∈layout.choices) (s : ComparisonShape)
    (hscope : ∀v∈s.vars, v∈layout.parameters) :
    (∀b∈layout.branches s, b.guard.eval (layout.encode ρ)=true → b.shape=s.subst ρ) ∧
    (∃b∈layout.branches s, b.guard.eval (layout.encode ρ)=true ∧ b.shape=s.subst ρ) := by
  have he : s.subst (layout.decode (layout.encode ρ)) = s.subst ρ :=
    ComparisonShapeSolver.subst_congr s (fun v hv => Layout.decode_encode hρ (hscope v hv))
  simpa only [he] using Layout.branches_decoded (Layout.theory_encode hρ) s hscope

theorem ofTemplates_scope {first : Nat} {choices templates : List ComparisonShape}
    {s : ComparisonShape} (hs : s∈templates) {v : TypeVar} (hv : v∈s.vars) :
    v∈(ofTemplates first choices templates).parameters :=
  List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨s, hs, hv⟩)

theorem Layout.atom_bounds {layout : Layout} {v : TypeVar} (hv : v∈layout.parameters)
    (i : Fin layout.choices.length) : layout.first ≤ layout.atom v i ∧ layout.atom v i < layout.next := by
  have hi := List.idxOf_lt_length_of_mem hv
  have hmul := Nat.mul_le_mul_left layout.choices.length (Nat.succ_le_of_lt hi)
  rw [Nat.mul_succ] at hmul
  dsimp only [Layout.atom, Layout.next]
  omega

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

theorem Layout.one_atoms {layout : Layout} {v : TypeVar} (hv : v∈layout.parameters) :
    ∀n∈(layout.one v).atoms, layout.first≤n ∧ n<layout.next := by
  intro n hn
  simp only [Layout.one, BoolExpr.atoms, List.mem_dedup, List.mem_append] at hn
  rcases hn with hn | hn
  · apply any_atoms _ n hn
    intro e he n hn
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    obtain rfl := List.mem_singleton.mp hn
    exact Layout.atom_bounds hv i
  · apply all_atoms _ n hn
    intro e he n hn
    obtain ⟨i, _, he⟩ := List.mem_flatMap.mp he
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    by_cases h : i=j
    · simp [h, BoolExpr.atoms] at hn
    · simp only [h, if_false, BoolExpr.atoms, List.mem_dedup, List.mem_append,
        List.mem_singleton, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl
      · exact Layout.atom_bounds hv i
      · exact Layout.atom_bounds hv j

theorem Layout.theory_atoms (layout : Layout) :
    ∀n∈layout.theory.atoms, layout.first≤n ∧ n<layout.next := by
  apply all_atoms
  intro e he
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
  exact Layout.one_atoms hv

theorem Layout.branches_atoms (layout : Layout) (s : ComparisonShape)
    (hscope : ∀v∈s.vars, v∈layout.parameters) :
    ∀b∈layout.branches s, ∀n∈b.guard.atoms, layout.first≤n ∧ n<layout.next := by
  induction s with
  | var v =>
    intro b hb n hn
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb
    obtain rfl := List.mem_singleton.mp hn
    exact Layout.atom_bounds (hscope v (by simp [ComparisonShape.vars])) i
  | unit | credit =>
    intro b hb n hn
    obtain rfl := List.mem_singleton.mp hb
    exact (List.not_mem_nil hn).elim
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    intro branch hb n hn
    obtain ⟨left, hl, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨right, hr, rfl⟩ := List.mem_map.mp hb
    simp only [BoolExpr.atoms, List.mem_dedup, List.mem_append] at hn
    exact hn.elim
      (iha (fun v hv => hscope v (List.mem_append_left _ hv)) left hl n)
      (ihb (fun v hv => hscope v (List.mem_append_right _ hv)) right hr n)

end ModalityInference.ComparisonShapeSelectors
