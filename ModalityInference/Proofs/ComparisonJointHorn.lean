import ModalityInference.ComparisonJointHorn
import ModalityInference.Proofs.ComparisonPropagation
import ModalityInference.Proofs.ModalSynthesis

namespace ModalityInference.ComparisonJointHorn

/-- Every polarity has at most one state atom; other atoms are unrestricted guards. -/
def LinearClause (state : Nat → Prop) (c : Clause) : Prop :=
  ∀ ⦃v w : Nat⦄ ⦃b : Bool⦄, (v, b) ∈ c → (w, b) ∈ c → state v → state w → v = w

def Linear (state : Nat → Prop) (cs : CNF) : Prop :=
  ∀ c ∈ cs, LinearClause state c

theorem LinearClause.subset {state : Nat → Prop} {a b : Clause}
    (h : LinearClause state a) (hb : ∀ literal ∈ b, literal ∈ a) :
    LinearClause state b := by
  intro v w b hv hw hsv hsw
  exact h (hb _ hv) (hb _ hw) hsv hsw

theorem cleanCNF_linear {state : Nat → Prop} {cs : CNF} (h : Linear state cs) :
    Linear state (cleanCNF cs) := by
  intro c hc
  simp only [cleanCNF, List.mem_dedup, List.mem_filter, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc.1
  exact (h d hd).subset fun _ hm => List.mem_dedup.mp hm

theorem compact_linear {state : Nat → Prop} {cs : CNF} (h : Linear state cs) :
    Linear state (CompactCNF.clean cs) := by
  induction cs with
  | nil => intro c hc; cases hc
  | cons c cs ih =>
    intro d hd
    rcases CompactCNF.mem_insert hd with rfl | hd
    · exact (h c (.head _)).subset fun _ hm => (CompactCNF.mem_canonical _ _).mp hm
    · exact ih (fun c hc => h c (.tail _ hc)) d hd

theorem resolve_linear {state : Nat → Prop} {c d : Clause} {pivot : Nat}
    (hc : LinearClause state c) (hd : LinearClause state d) (hp : state pivot)
    (hcpos : (pivot, true) ∈ c) (hdneg : (pivot, false) ∈ d) :
    LinearClause state (CNFPropagation.without pivot c ++ CNFPropagation.without pivot d) := by
  intro v w b hv hw hsv hsw
  simp only [List.mem_append, CNFPropagation.without, List.mem_filter, bne_iff_ne] at hv hw
  rcases hv with ⟨hv, hnv⟩ | ⟨hv, hnv⟩ <;> rcases hw with ⟨hw, hnw⟩ | ⟨hw, hnw⟩
  · exact hc hv hw hsv hsw
  · cases b
    · exact False.elim (hnw (hd hw hdneg hsw hp))
    · exact False.elim (hnv (hc hv hcpos hsv hp))
  · cases b
    · exact False.elim (hnv (hd hv hdneg hsv hp))
    · exact False.elim (hnw (hc hw hcpos hsw hp))
  · exact hd hv hw hsv hsw

/-- Eliminating a state atom preserves the unary lower/upper form. -/
theorem eliminate_linear {state : Nat → Prop} {cs : CNF} {pivot : Nat}
    (h : Linear state cs) (hp : state pivot) :
    Linear state (CNFPropagation.eliminate cs pivot) := by
  apply cleanCNF_linear
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact h c (List.mem_filter.mp hc).1
  · obtain ⟨l, hl, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc
    simp [CNFPropagation.lower, CNFPropagation.upper] at hl hu
    obtain ⟨a, ⟨ha, hap, _⟩, rfl⟩ := hl
    obtain ⟨b, ⟨hb, hbn, _⟩, rfl⟩ := hu
    exact resolve_linear (h a ha) (h b hb) hp hap hbn

private theorem insert_linear {state : Nat → Prop} {clause : Clause} {cs : CNF}
    (hc : LinearClause state clause) (hcs : Linear state cs) :
    Linear state (CompactCNF.insert (CompactCNF.canonical clause) cs) := by
  intro d hd
  rcases CompactCNF.mem_insert hd with rfl | hd
  · exact hc.subset fun _ hm => (CompactCNF.mem_canonical _ _).mp hm
  · exact hcs d hd

private theorem fold_linear {α : Type} {state : Nat → Prop} {items : List α}
    {f : α → CNF → CNF} {rest : CNF}
    (hf : ∀a∈items, ∀cs, Linear state cs → Linear state (f a cs))
    (hr : Linear state rest) : Linear state (items.foldr f rest) := by
  induction items with
  | nil => exact hr
  | cons a as ih =>
    exact hf a (.head _) _ (ih (fun b hb => hf b (.tail _ hb)))

theorem resolution_linear {state : Nat → Prop} {cs : CNF} {pivot : Nat}
    (h : Linear state cs) (hp : state pivot) :
    Linear state (ComparisonResolution.eliminate cs pivot) := by
  unfold ComparisonResolution.eliminate
  apply fold_linear
  · intro l hl rest hr
    apply fold_linear
    · intro u hu rest hr
      apply insert_linear
      · simp [CNFPropagation.lower, CNFPropagation.upper] at hl hu
        obtain ⟨a, ⟨ha, hap, _⟩, rfl⟩ := hl
        obtain ⟨b, ⟨hb, hbn, _⟩, rfl⟩ := hu
        exact resolve_linear (h a ha) (h b hb) hp hap hbn
      · exact hr
    · exact hr
  · exact fun c hc => h c (List.mem_filter.mp hc).1

theorem LinearClause.restrict {state retained : Nat → Prop} {c : Clause}
    (h : LinearClause state c) (hr : ∀ v, retained v → state v) :
    LinearClause retained c := by
  intro v w b hv hw hsv hsw
  exact h hv hw (hr v hsv) (hr w hsw)

/-- Coordinate-state elimination does not create multi-state lower or upper clauses. -/
private theorem projectLoop_linear {state : Nat → Prop} {cs : CNF} {pivots : List Nat}
    (h : Linear state cs) (hp : ∀ v ∈ pivots, state v) :
    Linear state (ComparisonPropagation.projectLoop pivots cs) := by
  induction pivots generalizing cs with
  | nil => exact h
  | cons v vs ih =>
    exact ih (resolution_linear h (hp v (.head _)))
      (fun w hw => hp w (.tail _ hw))

/-- Coordinate-state elimination does not create multi-state lower or upper clauses. -/
theorem project_linear {state : Nat → Prop} {cs : CNF} {pivots : List Nat}
    (h : Linear state cs) (hp : ∀ v ∈ pivots, state v) :
    Linear state (ComparisonPropagation.project pivots cs) :=
  projectLoop_linear (compact_linear h) hp

/-- After coordinate elimination, only nominal state atoms remain; guards are unrestricted. -/
theorem coordinate_residual {nominal : Nat → Prop} {cs : CNF} {coordinates : List Nat}
    (h : Linear (fun v => nominal v ∨ v ∈ coordinates) cs) :
    Linear nominal (ComparisonPropagation.project coordinates cs) ∧
      ∀ v ∈ CNFPropagation.atoms (ComparisonPropagation.project coordinates cs),
        v ∉ coordinates := by
  refine ⟨fun c hc => (project_linear h (fun _ hv => Or.inr hv) c hc).restrict
    (fun _ hv => Or.inl hv), ?_⟩
  exact fun _ hv => (ComparisonPropagation.project_atoms hv).2

/-- Even identifiers retain state atoms; the odd clause selectors are guards. -/
def EvenState (state : Nat → Prop) (v : Nat) : Prop :=
  v % 2 = 0 ∧ state (v / 2)

theorem component_linear {state : Nat → Prop} {cs : CNF}
    (h : Linear state cs) (side : Nat → Bool) (b : Bool) :
    Linear (EvenState state) (ModalSynthesis.component side b cs) := by
  intro d hd
  obtain ⟨⟨c, i⟩, hi, rfl⟩ := List.mem_map.mp hd
  intro v w p hv hw hsv hsw
  have hnv : v ≠ 2 * i + 1 := by have hv := hsv.1; omega
  have hnw : w ≠ 2 * i + 1 := by have hw := hsw.1; omega
  simp only [List.mem_cons, Prod.mk.injEq, hnv, hnw, false_and, false_or,
    List.mem_map, List.mem_filter, Prod.exists] at hv hw
  obtain ⟨a, _, ⟨ha, _⟩, rfl, rfl⟩ := hv
  obtain ⟨d, _, ⟨hd, _⟩, rfl, rfl⟩ := hw
  have he := h c (List.fst_mem_of_mem_zipIdx hi) ha hd
    (by simpa [EvenState] using hsv) (by simpa [EvenState] using hsw)
  exact congrArg (2 * ·) he

def valuation (decode : Nat → Option (Fin count)) (values : Fin count → Bool)
    (parameters : Nat → Bool) (v : Nat) : Bool :=
  (decode v).elim (parameters v) values

theorem stateIndex_member {decode : Nat → Option (Fin count)} {c : Clause}
    {polarity : Bool} {i : Fin count} (h : stateIndex decode polarity c = some i) :
    ∃ v, (v, polarity) ∈ c ∧ decode v = some i := by
  obtain ⟨⟨v, p⟩, hf, hi⟩ := Option.bind_eq_some_iff.mp h
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  cases hp.2
  exact ⟨v, List.mem_of_find?_eq_some hf, hi⟩

theorem stateIndex_of_member {decode : Nat → Option (Fin count)} {c : Clause}
    (hc : LinearClause (fun v => (decode v).isSome = true) c)
    {polarity : Bool} {v : Nat} {i : Fin count}
    (hv : (v, polarity) ∈ c) (hi : decode v = some i) :
    stateIndex decode polarity c = some i := by
  have hs : (c.find? fun literal => (decode literal.1).isSome && literal.2 == polarity).isSome = true :=
    List.find?_isSome.mpr ⟨(v, polarity), hv, by simp [hi]⟩
  obtain ⟨⟨w, p⟩, hf⟩ := Option.isSome_iff_exists.mp hs
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  cases hp.2
  have he := hc hv (List.mem_of_find?_eq_some hf) (by simp [hi]) hp.1
  simp [stateIndex, hf, ← he, hi]

theorem clause_normal_form {decode : Nat → Option (Fin count)} {c : Clause}
    (hc : LinearClause (fun v => (decode v).isSome = true) c)
    (values : Fin count → Bool) (parameters : Nat → Bool) :
    ClauseHolds (valuation decode values parameters) c ↔
      ClauseHolds parameters (guards decode c) ∨
      (∃ i, stateIndex decode false c = some i ∧ values i = false) ∨
      (∃ i, stateIndex decode true c = some i ∧ values i = true) := by
  constructor
  · rintro ⟨v, b, hv, he⟩
    cases hd : decode v with
    | none => exact Or.inl ⟨v, b, List.mem_filter.mpr ⟨hv, by simp [hd]⟩,
        by simpa [valuation, hd] using he⟩
    | some i =>
      have he : values i = b := by simpa [valuation, hd] using he
      cases b
      · exact Or.inr (Or.inl ⟨i, stateIndex_of_member hc hv hd, he⟩)
      · exact Or.inr (Or.inr ⟨i, stateIndex_of_member hc hv hd, he⟩)
  · rintro (hg | ⟨i, hi, he⟩ | ⟨i, hi, he⟩)
    · obtain ⟨v, b, hv, he⟩ := hg
      have hd := (List.mem_filter.mp hv).2
      have hd : decode v = none := Option.isNone_iff_eq_none.mp hd
      exact ⟨v, b, (List.mem_filter.mp hv).1, by simpa [valuation, hd] using he⟩
    · obtain ⟨v, hv, hd⟩ := stateIndex_member hi
      exact ⟨v, false, hv, by simpa [valuation, hd] using he⟩
    · obtain ⟨v, hv, hd⟩ := stateIndex_member hi
      exact ⟨v, true, hv, by simpa [valuation, hd] using he⟩

/-- Linear CNF compilation uses exactly the existing propagation obligation semantics. -/
theorem compileClause_correct {decode : Nat → Option (Fin count)} {c : Clause}
    (hc : LinearClause (fun v => (decode v).isSome = true) c)
    (values : Fin count → Bool) (parameters : Nat → Bool) :
    (compileClause decode c).Holds parameters (fun i => values i = true) ↔
      ClauseHolds (valuation decode values parameters) c := by
  rw [clause_normal_form hc]
  cases hn : stateIndex decode false c <;> cases hp : stateIndex decode true c <;>
    simp only [compileClause, hn, hp, ComparisonPropagation.Obligation.Holds,
      ComparisonPropagation.negate_correct]
  all_goals simp only [CNFHolds, List.mem_singleton, forall_eq, Option.some.injEq,
    reduceCtorEq, false_and, exists_false, false_or, or_false]
  all_goals grind

theorem compileClauses_correct {decode : Nat → Option (Fin count)} {cs : CNF}
    (hc : Linear (fun v => (decode v).isSome = true) cs)
    (values : Fin count → Bool) (parameters : Nat → Bool) :
    (∀ obligation ∈ cs.map (compileClause decode),
      obligation.Holds parameters (fun i => values i = true)) ↔
      CNFHolds (valuation decode values parameters) cs := by
  simp only [List.forall_mem_map]
  exact forall_congr' fun c => imp_congr_right fun hmem =>
    compileClause_correct (hc c hmem) values parameters

/-- The constant selector split is an equivalence for dependency-respecting strategies. -/
theorem uniform_components_iff {side : Nat → Bool} {flex : List Nat}
    {strategy : (Nat → Bool) → Nat → Bool} (hs : ModalSynthesis.Uniform side flex strategy)
    (cs : CNF) :
    (∀ parameters, CNFHolds (strategy parameters) cs) ↔
      ∃ selectors, ∀ b parameters,
        CNFHolds (ModalSynthesis.encode selectors (strategy parameters))
          (ModalSynthesis.component side b cs) := by
  refine ⟨ModalSynthesis.factor_selectors hs, ?_⟩
  rintro ⟨selectors, h⟩ parameters c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hh := (ModalSynthesis.component_holds side (selectors (2 * i + 1)) cs _).mp
    (h (selectors (2 * i + 1)) parameters) i hi
  have hne : selectors (2 * i + 1) ≠ !selectors (2 * i + 1) := by
    cases selectors (2 * i + 1) <;> decide
  simp only [ModalSynthesis.encode_odd, ModalSynthesis.encode_even, hne, false_or] at hh
  obtain ⟨v, b, hv, he⟩ := hh
  exact ⟨v, b, (List.mem_filter.mp hv).1, he⟩

end ModalityInference.ComparisonJointHorn
