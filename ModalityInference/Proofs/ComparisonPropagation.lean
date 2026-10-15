import ModalityInference.ComparisonPropagation
import ModalityInference.Proofs.SymbolicCNF
import ModalityInference.Proofs.CompactCNF
import ModalityInference.Proofs.ComparisonInterpolation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

namespace ModalityInference.ComparisonPropagation

@[simp] private theorem odd_div (v : Nat) : (2 * v + 1) / 2 = v := by omega

def Positive (clauses : CNF) : Prop :=
  ∀ clause ∈ clauses, ∀ literal ∈ clause, literal.2 = true

def Supported (domain : List Nat) (clauses : CNF) : Prop :=
  ∀ v ∈ CNFPropagation.atoms clauses, v ∈ domain

theorem rename_correct (f : Nat → Nat) (clauses : CNF) (σ : Nat → Bool) :
    CNFHolds σ (rename f clauses) ↔ CNFHolds (σ ∘ f) clauses := by
  constructor
  · intro h c hc
    obtain ⟨v, b, hv, hb⟩ := h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
    obtain ⟨⟨w, p⟩, hw, he⟩ := List.mem_map.mp hv
    cases he
    exact ⟨w, p, hw, hb⟩
  · intro h c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨v, b, hv, hb⟩ := h d hd
    exact ⟨f v, b, List.mem_map.mpr ⟨(v, b), hv, rfl⟩, hb⟩

private theorem clean_literal {cs : CNF} {c : Clause} {l : Literal}
    (hc : c ∈ cleanCNF cs) (hl : l ∈ c) : ∃ d ∈ cs, l ∈ d := by
  simp only [cleanCNF, List.mem_dedup, List.mem_filter, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc.1
  exact ⟨d, hd, List.mem_dedup.mp hl⟩

private theorem eliminate_literal {cs : CNF} {v : Nat} {c : Clause} {l : Literal}
    (hc : c ∈ CNFPropagation.eliminate cs v) (hl : l ∈ c) :
    ∃ d ∈ cs, l ∈ d := by
  obtain ⟨d, hd, hl⟩ := clean_literal hc hl
  rcases List.mem_append.mp hd with hd | hd
  · exact ⟨d, (List.mem_filter.mp hd).1, hl⟩
  · obtain ⟨a, ha, hd⟩ := List.mem_flatMap.mp hd
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
    rcases List.mem_append.mp hl with hl | hl
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
      exact ⟨e, (List.mem_filter.mp he).1, (List.mem_filter.mp hl).1⟩
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
      exact ⟨e, (List.mem_filter.mp he).1, (List.mem_filter.mp hl).1⟩

private theorem project_literal {vs : List Nat} {cs : CNF} {c : Clause} {l : Literal}
    (hc : c ∈ project vs cs) (hl : l ∈ c) :
    ∃ d ∈ cs, l ∈ d := by
  induction vs generalizing cs c with
  | nil => exact CompactCNF.clean_literal hc hl
  | cons v vs ih =>
    obtain ⟨d, hd, hl⟩ := ih hc hl
    obtain ⟨e, he, hl⟩ := eliminate_literal hd hl
    exact CompactCNF.clean_literal he hl

theorem project_atoms {vs : List Nat} {cs : CNF} {v : Nat}
    (hv : v ∈ CNFPropagation.atoms (project vs cs)) :
    v ∈ CNFPropagation.atoms cs ∧ v ∉ vs := by
  induction vs generalizing cs with
  | nil => exact ⟨CompactCNF.clean_atoms hv, by simp⟩
  | cons w ws ih =>
    obtain ⟨ha, hn⟩ := ih hv
    obtain ⟨ha, hne⟩ := CNFPropagation.eliminate_atoms ha
    exact ⟨CompactCNF.clean_atoms ha, by simp [hne, hn]⟩

theorem project_preserves (vs : List Nat) {cs : CNF} {σ : Nat → Bool}
    (h : CNFHolds σ cs) : CNFHolds σ (project vs cs) := by
  induction vs generalizing cs with
  | nil => exact (CompactCNF.clean_correct _ _).mpr h
  | cons v vs ih =>
    exact ih (CNFPropagation.eliminate_preserves v ((CompactCNF.clean_correct _ _).mpr h))

theorem project_complete (vs : List Nat) (cs : CNF) (σ : Nat → Bool) :
    CNFHolds σ (project vs cs) ↔
      ∃ τ, (∀ v ∉ vs, τ v = σ v) ∧ CNFHolds τ cs := by
  constructor
  · induction vs generalizing cs σ with
    | nil => intro h; exact ⟨σ, fun _ _ => rfl, (CompactCNF.clean_correct _ _).mp h⟩
    | cons v vs ih =>
      intro h
      obtain ⟨τ, he, ht⟩ := ih _ _ h
      obtain ⟨b, hb⟩ := (CNFPropagation.eliminate_iff _ _ _).mp ht
      refine ⟨Function.update τ v b, ?_, (CompactCNF.clean_correct _ _).mp hb⟩
      intro w hw
      have hwv : w ≠ v := fun h => hw (by simp [h])
      rw [Function.update_of_ne hwv]
      exact he w (fun h => hw (by simp [h]))
  · rintro ⟨τ, he, ht⟩
    exact (CNFPropagation.holds_congr
      (fun v hv => he v (project_atoms hv).2)).mp (project_preserves vs ht)

private theorem system_odd {domain : List Nat} {cs : CNF} {c : Clause} {l : Literal}
    (hc : c ∈ upwardSystem domain cs) (hl : l ∈ c) (ho : l.1 % 2 ≠ 0) :
    l.2 = true ∧ l.1 / 2 ∈ domain := by
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨⟨v, b⟩, _, he⟩ := List.mem_map.mp hl
    cases he
    simp at ho
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simp at ho
    · exact ⟨rfl, by simpa using hv⟩

private theorem residual_odd {domain : List Nat} {cs : CNF} {v : Nat}
    (hv : v ∈ CNFPropagation.atoms
      (project (upwardPivots domain cs) (upwardSystem domain cs))) :
    v % 2 ≠ 0 := by
  obtain ⟨hi, hn⟩ := project_atoms hv
  intro he
  apply hn
  simp only [upwardPivots, List.mem_filter, CNFPropagation.mem_pivots]
  exact ⟨hi, by simp [he]⟩

theorem upward_positive (domain : List Nat) (cs : CNF) : Positive (upward domain cs) := by
  intro c hc l hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
  have ho := residual_odd (CNFPropagation.mem_atoms.mpr ⟨d, hd, a.2, ha⟩)
  obtain ⟨e, he, ha⟩ := project_literal hd ha
  exact (system_odd he ha ho).1

theorem upward_supported (domain : List Nat) (cs : CNF) : Supported domain (upward domain cs) := by
  intro v hv
  obtain ⟨c, hc, b, hb⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hb
  cases he
  have ho := residual_odd (CNFPropagation.mem_atoms.mpr ⟨d, hd, a.2, ha⟩)
  obtain ⟨e, he, ha⟩ := project_literal hd ha
  exact (system_odd he ha ho).2

private theorem implication_clause (σ : Nat → Bool) (a b : Nat) :
    ClauseHolds σ [(a, false), (b, true)] ↔ (σ a = true → σ b = true) := by
  constructor
  · rintro ⟨v, p, hv, hp⟩ ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h
    · cases h
      simp [ha] at hp
    · cases h
      exact hp
  · intro h
    cases ha : σ a with
    | false => exact ⟨a, false, by simp, ha⟩
    | true => exact ⟨b, true, by simp, h ha⟩

private theorem upwardSystem_correct (domain : List Nat) (cs : CNF) (σ : Nat → Bool) :
    CNFHolds σ (upwardSystem domain cs) ↔
      CNFHolds (fun v => σ (2 * v)) cs ∧
        ∀ v ∈ domain, σ (2 * v) = true → σ (2 * v + 1) = true := by
  rw [upwardSystem, cnfHolds_append, rename_correct]
  simp only [CNFHolds, List.forall_mem_map, implication_clause, Function.comp_def]

/-- Exact existential projection followed by upward closure. Parameters outside
the retained basis are eliminated, not assigned a guessed value. -/
theorem upward_correct (domain : List Nat) (cs : CNF) (σ : Nat → Bool) :
    CNFHolds σ (upward domain cs) ↔
      ∃ τ, CNFHolds τ cs ∧ ∀ v ∈ domain, τ v = true → σ v = true := by
  rw [upward, rename_correct]
  constructor
  · intro h
    obtain ⟨ν, hν, hh⟩ := (project_complete _ _ _).mp h
    have hh := (upwardSystem_correct domain cs ν).mp hh
    refine ⟨fun v => ν (2 * v), hh.1, ?_⟩
    intro v hv he
    have ho : 2 * v + 1 ∉ upwardPivots domain cs := by
      simp [upwardPivots]
    have hn : ν (2 * v + 1) = σ v := by
      simpa using hν (2 * v + 1) ho
    exact hn ▸ hh.2 v hv he
  · rintro ⟨τ, ht, hle⟩
    let ν : Nat → Bool := fun v => if v % 2 = 0 then τ (v / 2) else σ (v / 2)
    have hn : CNFHolds ν (upwardSystem domain cs) := by
      apply (upwardSystem_correct domain cs ν).mpr
      simpa [ν] using And.intro ht hle
    apply (CNFPropagation.holds_congr (σ := ν) (τ := σ ∘ (· / 2)) ?_).mp
      (project_preserves _ hn)
    intro v hv
    simp [ν, residual_odd hv]

theorem upward_monotone (domain : List Nat) (cs : CNF) {σ τ : Nat → Bool}
    (hle : ∀ v ∈ domain, σ v = true → τ v = true)
    (h : CNFHolds σ (upward domain cs)) : CNFHolds τ (upward domain cs) := by
  obtain ⟨ν, hn, hns⟩ := (upward_correct domain cs σ).mp h
  exact (upward_correct domain cs τ).mpr ⟨ν, hn, fun v hv he => hle v hv (hns v hv he)⟩

theorem upward_least (domain : List Nat) (cs : CNF) (P : (Nat → Bool) → Prop)
    (hm : ∀ σ τ, (∀ v ∈ domain, σ v = true → τ v = true) → P σ → P τ)
    (h : ∀ σ, CNFHolds σ cs → P σ) :
    ∀ σ, CNFHolds σ (upward domain cs) → P σ := by
  intro σ hs
  obtain ⟨τ, ht, hts⟩ := (upward_correct domain cs σ).mp hs
  exact hm τ σ hts (h τ ht)

theorem join_correct (left right : CNF) (σ : Nat → Bool) :
    CNFHolds σ (join left right) ↔ CNFHolds σ left ∨ CNFHolds σ right := by
  exact CompactCNF.cnfOr_correct (limit := left.length * right.length)
    (by simp [CompactCNF.cnfOr, join]) σ

theorem meet_correct (left right : CNF) (σ : Nat → Bool) :
    CNFHolds σ (meet left right) ↔ CNFHolds σ left ∧ CNFHolds σ right := by
  rw [meet, CompactCNF.clean_correct, cnfHolds_append]

theorem negateClause_correct (clause : Clause) (σ : Nat → Bool) :
    CNFHolds σ (negateClause clause) ↔ ¬ClauseHolds σ clause := by
  constructor
  · intro h ⟨v, p, hv, he⟩
    have hh := h _ (List.mem_map.mpr ⟨(v, p), hv, rfl⟩)
    simp [ClauseHolds, he] at hh
  · intro h c hc
    obtain ⟨⟨v, p⟩, hv, rfl⟩ := List.mem_map.mp hc
    have he : σ v ≠ p := fun he => h ⟨v, p, hv, he⟩
    exact ⟨v, !p, by simp, by cases p <;> cases hv' : σ v <;> simp_all⟩

theorem negate_correct (clauses : CNF) (σ : Nat → Bool) :
    CNFHolds σ (negate clauses) ↔ ¬CNFHolds σ clauses := by
  induction clauses with
  | nil => simp [negate, CNFHolds, ClauseHolds]
  | cons c cs ih =>
    change CNFHolds σ (join (negateClause c) (negate cs)) ↔ _
    rw [join_correct, negateClause_correct, ih]
    simp only [CNFHolds, List.forall_mem_cons, not_and_or]

theorem implies_correct (left right : CNF) (σ : Nat → Bool) :
    CNFHolds σ (implies left right) ↔ (CNFHolds σ left → CNFHolds σ right) := by
  rw [implies, join_correct, negate_correct]
  tauto

def Action.Holds (action : Action) (σ : Nat → Bool) (value : Prop) : Prop :=
  (value ∨ CNFHolds σ action.lower) ∧ CNFHolds σ action.upper

def Leaf.Holds (leaf : Leaf count) (σ : Nat → Bool) (values : Fin count → Prop) : Prop :=
  match leaf with
  | .fixed value => CNFHolds σ value
  | .flex v => values v

def Endpoint.Holds (endpoint : Endpoint count) (action : ModExpr → Action)
    (σ : Nat → Bool) (values : Fin count → Prop) : Prop :=
  (action endpoint.mode).Holds σ (endpoint.leaf.Holds σ values)

def Obligation.Holds (obligation : Obligation count)
    (σ : Nat → Bool) (values : Fin count → Prop) : Prop :=
  match obligation with
  | .lower v condition => CNFHolds σ condition → values v
  | .edge u v condition => CNFHolds σ condition → values u → values v
  | .upper v condition => values v → CNFHolds σ condition
  | .check condition => CNFHolds σ condition

/-- Modalized occurrences, including both-flexible cycles, compile exactly into
lower, edge, upper and constant obligations. No scalar residual guard is assumed. -/
theorem compileBound_correct (action : ModExpr → Action) (theory : CNF)
    (bound : Bound count) (σ : Nat → Bool) (values : Fin count → Prop) :
    (∀ obligation ∈ compileBound action theory bound, obligation.Holds σ values) ↔
      (CNFHolds σ theory → bound.left.Holds action σ values → bound.right.Holds action σ values) := by
  rcases bound with ⟨⟨left, lm⟩, ⟨right, rm⟩⟩
  cases left <;> cases right <;>
    simp only [compileBound, List.forall_mem_cons,
      Obligation.Holds, implies_correct, meet_correct, negate_correct, Endpoint.Holds,
      Leaf.Holds, Action.Holds, Action.apply, join_correct] <;> tauto

theorem seed_correct (size : Nat) (σ : Nat → Bool) :
    CNFHolds σ (seed size) ↔ ∀ v < size, σ v = true := by
  simp [seed, CNFHolds, ClauseHolds]

theorem image_correct (size : Nat) (relation demand : CNF) (σ : Nat → Bool) :
    CNFHolds σ (image size relation demand) ↔
      ∃ τ, CNFHolds τ relation ∧ CNFHolds (fun v => τ (2 * v)) demand ∧
        ∀ v < size, τ (2 * v + 1) = true → σ v = true := by
  rw [image, rename_correct, upward_correct]
  simp only [cnfHolds_append, rename_correct, Function.comp_def, List.forall_mem_map,
    List.mem_range, odd_div, and_assoc]

theorem diagonal_correct (size : Nat) (condition : CNF) (σ : Nat → Bool) :
    CNFHolds σ (diagonal size condition) ↔
      CNFHolds (fun i => σ (2 * i)) condition ∧
        ∀ i < size, σ (2 * i) = σ (2 * i + 1) := by
  rw [diagonal, cnfHolds_append, rename_correct]
  apply and_congr Iff.rfl
  simp only [CNFHolds, List.forall_mem_flatMap, List.mem_range]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  cases he : σ (2 * i) <;> cases ho : σ (2 * i + 1) <;>
    simp [ClauseHolds, exists_or, he, ho]

theorem image_positive (size : Nat) (relation demand : CNF) :
    Positive (image size relation demand) := by
  intro c hc l hl
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hl
  exact upward_positive _ _ d hd a ha

theorem image_supported (size : Nat) (relation demand : CNF) :
    Supported (List.range size) (image size relation demand) := by
  intro v hv
  obtain ⟨c, hc, b, hb⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  obtain ⟨a, ha, he⟩ := List.mem_map.mp hb
  cases he
  obtain ⟨w, hw, he⟩ := List.mem_map.mp
    (upward_supported _ _ _ (CNFPropagation.mem_atoms.mpr ⟨d, hd, a.2, ha⟩))
  simpa [← he] using hw

theorem image_mono {size : Nat} {relation left right : CNF}
    (h : ∀ σ, CNFHolds σ left → CNFHolds σ right) (σ : Nat → Bool)
    (hm : CNFHolds σ (image size relation left)) :
    CNFHolds σ (image size relation right) := by
  obtain ⟨τ, hr, ht, hts⟩ := (image_correct _ _ _ _).mp hm
  exact (image_correct _ _ _ _).mpr ⟨τ, hr, h _ ht, hts⟩

theorem Positive.monotone {cs : CNF} (h : Positive cs) {σ τ : Nat → Bool}
    (hle : ∀ v, σ v = true → τ v = true) (hs : CNFHolds σ cs) : CNFHolds τ cs := by
  intro c hc
  obtain ⟨v, p, hv, he⟩ := hs c hc
  have hp : p = true := h c hc (v, p) hv
  rw [hp] at hv he
  exact ⟨v, true, hv, hle v he⟩

theorem Positive.monotone_supported {cs : CNF} {domain : List Nat}
    (hp : Positive cs) (hs : Supported domain cs) {σ τ : Nat → Bool}
    (hle : ∀ v ∈ domain, σ v = true → τ v = true)
    (h : CNFHolds σ cs) : CNFHolds τ cs := by
  intro c hc
  obtain ⟨v, p, hv, he⟩ := h c hc
  have hp' := hp c hc (v, p) hv
  have hv' := hs v (CNFPropagation.mem_atoms.mpr ⟨c, hc, p, hv⟩)
  cases hp'
  exact ⟨v, true, hv, hle v hv' he⟩

theorem join_positive {left right : CNF} (hl : Positive left) (hr : Positive right) :
    Positive (join left right) := by
  intro c hc l hm
  obtain ⟨d, hd, hm⟩ := CompactCNF.clean_literal hc hm
  obtain ⟨a, ha, hd⟩ := List.mem_flatMap.mp hd
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hd
  rcases List.mem_append.mp hm with hm | hm
  · exact hl a ha l hm
  · exact hr b hb l hm

theorem join_supported {domain : List Nat} {left right : CNF}
    (hl : Supported domain left) (hr : Supported domain right) :
    Supported domain (join left right) := by
  intro v hv
  obtain ⟨c, hc, p, hp⟩ := CNFPropagation.mem_atoms.mp (CompactCNF.clean_atoms hv)
  obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hp with hp | hp
  · exact hl v (CNFPropagation.mem_atoms.mpr ⟨a, ha, p, hp⟩)
  · exact hr v (CNFPropagation.mem_atoms.mpr ⟨b, hb, p, hp⟩)

theorem seed_positive (size : Nat) : Positive (seed size) := by
  intro c hc l hl
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp hc
  have he : l = (v, true) := by simpa using hl
  exact congrArg Prod.snd he

theorem seed_supported (size : Nat) : Supported (List.range size) (seed size) := by
  intro v hv
  obtain ⟨c, hc, p, hp⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hc
  have he : v = w := by simpa using congrArg Prod.fst (List.mem_singleton.mp hp)
  exact he ▸ hw

theorem initial_correct (size : Nat) (lower : Store count) (v : Fin count) (σ : Nat → Bool) :
    CNFHolds σ (initial size lower)[v] ↔
      (∀ i < size, σ i = true) ∨
        ∃ τ, CNFHolds τ lower[v] ∧ ∀ i < size, τ i = true → σ i = true := by
  simp only [initial, Fin.getElem_fin, Vector.getElem_ofFn, join_correct, seed_correct, upward_correct,
    List.mem_range]

theorem step_correct (size : Nat) (edges : List (Edge count))
    (store : Store count) (v : Fin count) (σ : Nat → Bool) :
    CNFHolds σ (step size edges store)[v] ↔ CNFHolds σ store[v] ∨
      ∃ e ∈ edges, e.target = v ∧ CNFHolds σ (image size e.relation store[e.source]) := by
  simp only [step, Fin.getElem_fin, Vector.getElem_ofFn, beq_iff_eq]
  induction edges with
  | nil => simp
  | cons e edges ih =>
    simp only [List.foldr_cons]
    by_cases he : e.target = v
    · simp [he, join_correct, ih, or_left_comm]
    · simp [he, ih]

def Store.Le (left right : Store count) : Prop :=
  ∀ (v : Fin count) (σ : Nat → Bool), CNFHolds σ left[v] → CNFHolds σ right[v]

theorem step_inflationary (size : Nat) (edges : List (Edge count)) (store : Store count) :
    Store.Le store (step size edges store) :=
  fun _ _ h => (step_correct _ _ _ _ _).mpr (.inl h)

theorem step_mono {size : Nat} {edges : List (Edge count)} {left right : Store count}
    (h : Store.Le left right) : Store.Le (step size edges left) (step size edges right) := by
  intro v σ hs
  rcases (step_correct _ _ _ _ _).mp hs with hs | ⟨e, he, ht, hs⟩
  · exact (step_correct _ _ _ _ _).mpr (.inl (h v σ hs))
  · exact (step_correct _ _ _ _ _).mpr (.inr
      ⟨e, he, ht, image_mono (h e.source) σ hs⟩)

def Store.Positive (store : Store count) : Prop :=
  ∀ v : Fin count, ComparisonPropagation.Positive store[v]
def Store.Supported (size : Nat) (store : Store count) : Prop :=
  ∀ v : Fin count, ComparisonPropagation.Supported (List.range size) store[v]
def Store.Equiv (left right : Store count) : Prop :=
  ∀ (v : Fin count) (σ : Nat → Bool), CNFHolds σ left[v] ↔ CNFHolds σ right[v]

theorem Store.Equiv.refl (store : Store count) : store.Equiv store := fun _ _ => Iff.rfl
theorem Store.Equiv.symm {left right : Store count} (h : left.Equiv right) : right.Equiv left :=
  fun v σ => (h v σ).symm
theorem Store.Equiv.trans {a b c : Store count} (h : a.Equiv b) (h' : b.Equiv c) : a.Equiv c :=
  fun v σ => (h v σ).trans (h' v σ)

theorem initial_positive (size : Nat) (lower : Store count) : (initial size lower).Positive := by
  intro v
  simpa only [initial, Fin.getElem_fin, Vector.getElem_ofFn] using
    join_positive (seed_positive size) (upward_positive (List.range size) lower[v])

theorem initial_supported (size : Nat) (lower : Store count) : (initial size lower).Supported size := by
  intro v
  simpa only [initial, Fin.getElem_fin, Vector.getElem_ofFn] using
    join_supported (seed_supported size) (upward_supported (List.range size) lower[v])

theorem step_positive {size : Nat} {edges : List (Edge count)} {store : Store count}
    (h : store.Positive) : (step size edges store).Positive := by
  intro v
  simp only [step, Fin.getElem_fin, Vector.getElem_ofFn]
  induction edges with
  | nil => exact h v
  | cons e edges ih =>
    simp only [List.foldr_cons]
    split
    · exact join_positive (image_positive _ _ _) ih
    · exact ih

theorem step_supported {size : Nat} {edges : List (Edge count)} {store : Store count}
    (h : store.Supported size) : (step size edges store).Supported size := by
  intro v
  simp only [step, Fin.getElem_fin, Vector.getElem_ofFn]
  induction edges with
  | nil => exact h v
  | cons e edges ih =>
    simp only [List.foldr_cons]
    split
    · exact join_supported (image_supported _ _ _) ih
    · exact ih

theorem step_congr {size : Nat} {edges : List (Edge count)} {left right : Store count}
    (h : left.Equiv right) : (step size edges left).Equiv (step size edges right) :=
  fun v σ => ⟨step_mono (fun w τ => (h w τ).mp) v σ,
    step_mono (fun w τ => (h w τ).mpr) v σ⟩

theorem iterate_positive {size : Nat} {edges : List (Edge count)} {store : Store count}
    (h : store.Positive) (n : Nat) : (iterate size edges n store).Positive := by
  induction n generalizing store with
  | zero => exact h
  | succ n ih => exact ih (step_positive h)

theorem iterate_supported {size : Nat} {edges : List (Edge count)} {store : Store count}
    (h : store.Supported size) (n : Nat) : (iterate size edges n store).Supported size := by
  induction n generalizing store with
  | zero => exact h
  | succ n ih => exact ih (step_supported h)

theorem iterate_succ (size : Nat) (edges : List (Edge count)) (n : Nat) (store : Store count) :
    iterate size edges (n + 1) store = step size edges (iterate size edges n store) := by
  induction n generalizing store with
  | zero => rfl
  | succ n ih => exact ih (step size edges store)

theorem iterate_add (size : Nat) (edges : List (Edge count)) (n m : Nat) (store : Store count) :
    iterate size edges (n + m) store = iterate size edges m (iterate size edges n store) := by
  induction n generalizing store with
  | zero => simp [iterate]
  | succ n ih => simpa only [Nat.succ_add, iterate] using ih (step size edges store)

theorem iterate_congr {size : Nat} {edges : List (Edge count)} {left right : Store count}
    (h : left.Equiv right) (n : Nat) :
    (iterate size edges n left).Equiv (iterate size edges n right) := by
  induction n generalizing left right with
  | zero => exact h
  | succ n ih => exact ih (step_congr h)

theorem iterate_fixed {size : Nat} {edges : List (Edge count)} {store : Store count}
    (h : (step size edges store).Equiv store) (n : Nat) :
    (iterate size edges n store).Equiv store := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact (iterate_congr h n).trans ih

theorem iterate_least {size : Nat} {edges : List (Edge count)} {initial bound : Store count}
    (h : initial.Le bound) (hb : (step size edges bound).Le bound) (n : Nat) :
    (iterate size edges n initial).Le bound := by
  induction n generalizing initial with
  | zero => exact h
  | succ n ih => exact ih (fun v σ hs => hb v σ (step_mono h v σ hs))

theorem saturate_equiv_iterate (size : Nat) (edges : List (Edge count))
    (n : Nat) (store : Store count) :
    (saturate size edges n store).Equiv (iterate size edges n store) := by
  induction n generalizing store with
  | zero => exact .refl _
  | succ n ih =>
    simp only [saturate]
    split
    · next he =>
        have hf : (step size edges store).Equiv store := by rw [he]; exact .refl _
        exact (iterate_fixed hf (n + 1)).symm
    · exact ih (step size edges store)

def extend (σ : Fin size → Bool) (v : Nat) : Bool :=
  if h : v < size then σ ⟨v, h⟩ else false

private theorem holds_restrict {size : Nat} {cs : CNF}
    (h : Supported (List.range size) cs) (σ : Nat → Bool) :
    CNFHolds σ cs ↔ CNFHolds (extend (fun i : Fin size => σ i)) cs := by
  apply CNFPropagation.holds_congr
  intro v hv
  have hi := List.mem_range.mp (h v hv)
  simp [extend, hi]

/-- Used only in the proof of the finite bound. The executable algorithm keeps
clauses and never materializes this finite set of coordinate valuations. -/
noncomputable def states (size : Nat) (store : Store count) :
    Finset (Fin count × (Fin size → Bool)) := by
  classical
  exact Finset.univ.filter fun p => CNFHolds (extend p.2) store[p.1]

@[simp] theorem mem_states {size : Nat} {store : Store count}
    {p : Fin count × (Fin size → Bool)} :
    p ∈ states size store ↔ CNFHolds (extend p.2) store[p.1] := by
  classical
  simp [states]

theorem states_subset {size : Nat} {left right : Store count} (h : left.Le right) :
    states size left ⊆ states size right := by
  intro p hp
  exact mem_states.mpr (h p.1 _ (mem_states.mp hp))

theorem states_eq_of_equiv {size : Nat} {left right : Store count} (h : left.Equiv right) :
    states size left = states size right := by
  ext p
  exact mem_states.trans ((h p.1 _).trans mem_states.symm)

theorem equiv_of_states_eq {size : Nat} {left right : Store count}
    (hl : left.Supported size) (hr : right.Supported size)
    (h : states size left = states size right) : left.Equiv right := by
  intro v σ
  rw [holds_restrict (hl v) σ, holds_restrict (hr v) σ]
  exact (mem_states (p := (v, fun i : Fin size => σ i))).symm.trans
    ((congrArg (fun s => (v, fun i : Fin size => σ i) ∈ s) h).to_iff.trans mem_states)

private theorem finite_chain_stable {α : Type} [Fintype α] (s : Nat → Finset α)
    (hsub : ∀ n, s n ⊆ s (n + 1))
    (hfixed : ∀ n k, s n = s (n + 1) → s n = s (n + k)) :
    s (Fintype.card α) = s (Fintype.card α + 1) := by
  by_contra hn
  have hne : ∀ n ≤ Fintype.card α, s n ≠ s (n + 1) := by
    intro n hle he
    have h₁ := hfixed n (Fintype.card α - n) he
    have h₂ := hfixed n (Fintype.card α + 1 - n) he
    rw [Nat.add_sub_of_le hle] at h₁
    rw [Nat.add_sub_of_le (by omega : n ≤ Fintype.card α + 1)] at h₂
    exact hn (h₁.symm.trans h₂)
  have hcard : ∀ n ≤ Fintype.card α + 1, n ≤ (s n).card := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hle
      have hi := ih (by omega)
      have hg := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsub n, hne n (by omega)⟩)
      omega
  have hg := hcard (Fintype.card α + 1) (by omega)
  have hu := (s (Fintype.card α + 1)).card_le_univ
  omega

/-- The concrete cardinality bound suffices even when modality cycles induce
nontrivial transitions between basis valuations. -/
theorem iterate_height_fixed {size : Nat} {edges : List (Edge count)} {store : Store count}
    (h : store.Supported size) :
    (step size edges (iterate size edges (height count size) store)).Equiv
      (iterate size edges (height count size) store) := by
  let s := fun n => states size (iterate size edges n store)
  have hs : ∀ n, s n ⊆ s (n + 1) := by
    intro n
    dsimp [s]
    rw [iterate_succ]
    exact states_subset (step_inflationary _ _ _)
  have hf : ∀ n k, s n = s (n + 1) → s n = s (n + k) := by
    intro n k he
    have hc : (step size edges (iterate size edges n store)).Equiv
        (iterate size edges n store) := by
      apply equiv_of_states_eq (step_supported (iterate_supported h n)) (iterate_supported h n)
      simpa only [s, iterate_succ] using he.symm
    dsimp [s]
    rw [iterate_add]
    exact (states_eq_of_equiv (iterate_fixed hc k)).symm
  have hh := finite_chain_stable s hs hf
  have hsize : Fintype.card (Fin count × (Fin size → Bool)) = height count size := by
    simp [height]
  rw [hsize] at hh
  apply equiv_of_states_eq (step_supported (iterate_supported h _)) (iterate_supported h _)
  simpa only [s, iterate_succ] using hh.symm

theorem propagate_fixed (size : Nat) (edges : List (Edge count)) (lower : Store count) :
    (step size edges (propagate size edges lower)).Equiv (propagate size edges lower) := by
  have he := saturate_equiv_iterate size edges (height count size) (initial size lower)
  exact (step_congr he).trans
    ((iterate_height_fixed (initial_supported size lower)).trans he.symm)

theorem propagate_least {size : Nat} {edges : List (Edge count)} {lower bound : Store count}
    (hl : (initial size lower).Le bound) (hb : (step size edges bound).Le bound) :
    (propagate size edges lower).Le bound := by
  intro v σ h
  have he := saturate_equiv_iterate size edges (height count size) (initial size lower)
  exact iterate_least hl hb _ v σ ((he v σ).mp h)

theorem saturate_positive {size : Nat} {edges : List (Edge count)} {store : Store count}
    (h : store.Positive) (n : Nat) : (saturate size edges n store).Positive := by
  induction n generalizing store with
  | zero => exact h
  | succ n ih =>
    simp only [saturate]
    split
    · exact h
    · exact ih (step_positive h)

theorem saturate_supported {size : Nat} {edges : List (Edge count)} {store : Store count}
    (h : store.Supported size) (n : Nat) : (saturate size edges n store).Supported size := by
  induction n generalizing store with
  | zero => exact h
  | succ n ih =>
    simp only [saturate]
    split
    · exact h
    · exact ih (step_supported h)

theorem propagate_positive (size : Nat) (edges : List (Edge count)) (lower : Store count) :
    (propagate size edges lower).Positive :=
  saturate_positive (initial_positive size lower) _

theorem propagate_supported (size : Nat) (edges : List (Edge count)) (lower : Store count) :
    (propagate size edges lower).Supported size :=
  saturate_supported (initial_supported size lower) _

theorem iterate_inflationary (size : Nat) (edges : List (Edge count))
    (store : Store count) (n : Nat) : store.Le (iterate size edges n store) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    rw [iterate_succ]
    exact fun v σ h => step_inflationary _ _ _ v σ (ih v σ h)

theorem propagate_initial (size : Nat) (edges : List (Edge count)) (lower : Store count) :
    (initial size lower).Le (propagate size edges lower) := by
  intro v σ h
  exact (saturate_equiv_iterate _ _ _ _ v σ).mpr (iterate_inflationary _ _ _ _ v σ h)

theorem propagate_lower (size : Nat) (edges : List (Edge count)) (lower : Store count) :
    lower.Le (propagate size edges lower) := by
  intro v σ h
  apply propagate_initial size edges lower v σ
  exact (initial_correct _ _ _ _).mpr (.inr ⟨σ, h, fun _ _ => id⟩)

theorem propagate_all_true (size : Nat) (edges : List (Edge count)) (lower : Store count)
    (v : Fin count) : CNFHolds (fun _ => true) (propagate size edges lower)[v] :=
  propagate_initial size edges lower v _ ((initial_correct _ _ _ _).mpr (.inl (by simp)))

def ZeroOn (size : Nat) (σ : Nat → Bool) : Prop := ∀ i < size, σ i = false

def Store.Nonzero (store : Store count) : Prop :=
  ∀ v : Fin count, ¬CNFHolds (fun _ => false) store[v]

def LowerNonzero (size : Nat) (lower : Store count) : Prop :=
  ∀ (v : Fin count) (σ : Nat → Bool), ZeroOn size σ → ¬CNFHolds σ lower[v]

def Edge.ZeroReflecting (size : Nat) (edge : Edge count) : Prop :=
  ∀ σ, CNFHolds σ edge.relation → ZeroOn size (fun i => σ (2 * i + 1)) →
    ZeroOn size (fun i => σ (2 * i))

theorem diagonal_zeroReflecting (size : Nat) (condition : CNF)
    (source target : Fin count) :
    (Edge.mk source target (diagonal size condition)).ZeroReflecting size := by
  intro σ hr hz i hi
  exact ((diagonal_correct _ _ _).mp hr).2 i hi |>.trans (hz i hi)

theorem initial_nonzero {size : Nat} {lower : Store count}
    (hsize : 0 < size) (h : LowerNonzero size lower) : (initial size lower).Nonzero := by
  intro v hh
  rcases (initial_correct _ _ _ _).mp hh with hs | ⟨σ, hs, hz⟩
  · have := hs 0 hsize
    contradiction
  · apply h v σ (fun i hi => ?_) hs
    cases he : σ i
    · rfl
    · have := hz i hi he
      contradiction

theorem step_nonzero {size : Nat} {edges : List (Edge count)} {store : Store count}
    (hz : store.Nonzero) (hs : store.Supported size)
    (he : ∀ e ∈ edges, e.ZeroReflecting size) : (step size edges store).Nonzero := by
  intro v hh
  rcases (step_correct _ _ _ _ _).mp hh with hh | ⟨e, hm, _, hh⟩
  · exact hz v hh
  · obtain ⟨σ, hr, hd, ho⟩ := (image_correct _ _ _ _).mp hh
    have hz' : ZeroOn size (fun i => σ (2 * i + 1)) := by
      intro i hi
      cases heq : σ (2 * i + 1)
      · exact heq
      · have := ho i hi heq
        contradiction
    have hi := he e hm σ hr hz'
    apply hz e.source
    exact (CNFPropagation.holds_congr (fun i hm => hi i (List.mem_range.mp (hs e.source i hm)))).mp hd

theorem saturate_nonzero {size : Nat} {edges : List (Edge count)} {store : Store count}
    (hz : store.Nonzero) (hs : store.Supported size)
    (he : ∀ e ∈ edges, e.ZeroReflecting size) (n : Nat) :
    (saturate size edges n store).Nonzero := by
  induction n generalizing store with
  | zero => exact hz
  | succ n ih =>
    simp only [saturate]
    split
    · exact hz
    · exact ih (step_nonzero hz hs he) (step_supported hs)

theorem propagate_nonzero {size : Nat} {edges : List (Edge count)} {lower : Store count}
    (hsize : 0 < size) (hl : LowerNonzero size lower)
    (he : ∀ e ∈ edges, e.ZeroReflecting size) :
    (propagate size edges lower).Nonzero :=
  saturate_nonzero (initial_nonzero hsize hl) (initial_supported _ _) he _

def Program.Closed (program : Program count) (store : Store count) : Prop :=
  program.lower.Le store ∧
    ∀ e ∈ program.edges, ∀ σ, CNFHolds σ e.relation →
      CNFHolds (fun i => σ (2 * i)) store[e.source] →
      CNFHolds (fun i => σ (2 * i + 1)) store[e.target]

theorem propagate_closed (size : Nat) (program : Program count) :
    program.Closed (propagate size program.edges program.lower) := by
  refine ⟨propagate_lower _ _ _, ?_⟩
  intro e he σ hr hd
  apply (propagate_fixed size program.edges program.lower e.target _).mp
  apply (step_correct _ _ _ _ _).mpr
  exact .inr ⟨e, he, rfl, (image_correct _ _ _ _).mpr
    ⟨σ, hr, hd, fun _ _ => id⟩⟩

/-- The least propagated store lies below every positive, basis-supported
solution of the original lower and relational obligations. -/
theorem propagate_least_closed {size : Nat} {program : Program count} {store : Store count}
    (hp : store.Positive) (hs : store.Supported size)
    (ht : ∀ v : Fin count, CNFHolds (fun _ => true) store[v])
    (hc : program.Closed store) :
    (propagate size program.edges program.lower).Le store := by
  apply propagate_least
  · intro v σ h
    rcases (initial_correct _ _ _ _).mp h with h | ⟨τ, h, hle⟩
    · exact (hp v).monotone_supported (hs v)
        (fun i hi _ => h i (List.mem_range.mp hi)) (ht v)
    · exact (hp v).monotone_supported (hs v)
        (fun i hi => hle i (List.mem_range.mp hi)) (hc.1 v τ h)
  · intro v σ h
    rcases (step_correct _ _ _ _ _).mp h with h | ⟨e, he, hv, h⟩
    · exact h
    · obtain ⟨τ, hr, hd, hle⟩ := (image_correct _ _ _ _).mp h
      have ht' := hc.2 e he τ hr hd
      cases hv
      exact (hp e.target).monotone_supported (hs e.target)
        (fun i hi => hle i (List.mem_range.mp hi)) ht'

def Store.Polynomial (size : Nat) (store : Store count) : Prop :=
  store.Positive ∧ store.Supported size ∧
    (∀ v : Fin count, CNFHolds (fun _ => true) store[v]) ∧ store.Nonzero

def Program.Valid (program : Program count) (store : Store count) : Prop :=
  program.Closed store ∧ ∀ σ, CNFHolds σ (residual program store)

def basisValue (basis : List CompareTy) (value : CompareTy → Bool) (v : Nat) : Bool :=
  ((basis[v]?).map value).getD false

theorem clauseType_correct {basis : List CompareTy} {clause : Clause} {t : CompareTy}
    (h : clauseType basis clause = some t) (value : CompareTy → Bool)
    (hj : ∀ a b, value (.join a b) = (value a || value b)) :
    value t = true ↔ ClauseHolds (basisValue basis value) clause := by
  induction clause generalizing t with
  | nil => simp [clauseType] at h
  | cons literal rest ih =>
    rcases literal with ⟨v, positive⟩
    cases positive with
    | false => simp [clauseType] at h
    | true =>
      cases hb : basis[v]? with
      | none => simp [clauseType, hb] at h
      | some a =>
        cases rest with
        | nil =>
          simp [clauseType, hb] at h
          cases h
          simp [ClauseHolds, basisValue, hb]
        | cons l rest =>
          cases ht : clauseType basis (l :: rest) with
          | none => rw [clauseType] at h; simp [hb, ht] at h
          | some b =>
            have he : .join a b = t := by rw [clauseType] at h; simpa [hb, ht] using h
            cases he
            rw [hj, Bool.or_eq_true, ih ht]
            simp [basisValue, hb]

/-- Any Boolean coordinate preserving joins and meets reads the reconstructed
type exactly as the positive CNF. This is the interface to ground profiles. -/
theorem reify_correct {basis : List CompareTy} {clauses : CNF} {t : CompareTy}
    (h : reify basis clauses = some t) (value : CompareTy → Bool)
    (hj : ∀ a b, value (.join a b) = (value a || value b))
    (hm : ∀ a b, value (.meet a b) = (value a && value b)) :
    value t = true ↔ CNFHolds (basisValue basis value) clauses := by
  induction clauses generalizing t with
  | nil => simp [reify] at h
  | cons c cs ih =>
    cases hc : clauseType basis c with
    | none => simp [reify, hc] at h
    | some a =>
      cases cs with
      | nil =>
        simp [reify, hc] at h
        cases h
        simpa [CNFHolds] using clauseType_correct hc value hj
      | cons c' cs =>
        cases hr : reify basis (c' :: cs) with
        | none => rw [reify] at h; simp [hc, hr] at h
        | some b =>
          have he : .meet a b = t := by rw [reify] at h; simpa [hc, hr] using h
          cases he
          rw [hm, Bool.and_eq_true, clauseType_correct hc value hj, ih hr]
          simp [CNFHolds]

theorem clauseType_property {basis : List CompareTy} {clause : Clause} {t : CompareTy}
    (h : clauseType basis clause = some t) (P : CompareTy → Prop)
    (hb : ∀ a ∈ basis, P a) (hj : ∀ a b, P a → P b → P (.join a b)) : P t := by
  induction clause generalizing t with
  | nil => simp [clauseType] at h
  | cons literal rest ih =>
    rcases literal with ⟨v, positive⟩
    cases positive with
    | false => simp [clauseType] at h
    | true =>
      cases ha : basis[v]? with
      | none => simp [clauseType, ha] at h
      | some a =>
        have hp := hb a (List.mem_of_getElem? ha)
        cases rest with
        | nil =>
          have he : a = t := by simpa [clauseType, ha] using h
          exact he ▸ hp
        | cons l rest =>
          cases ht : clauseType basis (l :: rest) with
          | none => rw [clauseType] at h; simp [ha, ht] at h
          | some b =>
            have he : .join a b = t := by rw [clauseType] at h; simpa [ha, ht] using h
            exact he ▸ hj a b hp (ih ht)

/-- Reification preserves every basis property closed under the two lattice
constructors, including scope, shape compatibility and definedness. -/
theorem reify_property {basis : List CompareTy} {clauses : CNF} {t : CompareTy}
    (h : reify basis clauses = some t) (P : CompareTy → Prop)
    (hb : ∀ a ∈ basis, P a) (hj : ∀ a b, P a → P b → P (.join a b))
    (hm : ∀ a b, P a → P b → P (.meet a b)) : P t := by
  induction clauses generalizing t with
  | nil => simp [reify] at h
  | cons c cs ih =>
    cases hc : clauseType basis c with
    | none => simp [reify, hc] at h
    | some a =>
      have hp := clauseType_property hc P hb hj
      cases cs with
      | nil =>
        have he : a = t := by simpa [reify, hc] using h
        exact he ▸ hp
      | cons c' cs =>
        cases hr : reify basis (c' :: cs) with
        | none => rw [reify] at h; simp [hc, hr] at h
        | some b =>
          have he : .meet a b = t := by rw [reify] at h; simpa [hc, hr] using h
          exact he ▸ hm a b hp (ih hr)

theorem reify_nonzero {basis : List CompareTy} {clauses : CNF} {t : CompareTy}
    (h : reify basis clauses = some t) : ¬CNFHolds (fun _ => false) clauses := by
  have hb : basisValue basis (fun _ => false) = fun _ => false := by
    funext v
    simp only [basisValue]
    cases basis[v]? <;> rfl
  have hc := reify_correct h (fun _ => false) (by simp) (by simp)
  rw [hb] at hc
  exact hc.not.mp (by simp)

theorem clauseType_complete {basis : List CompareTy} {clause : Clause}
    (hne : clause ≠ [])
    (h : ∀ l ∈ clause, l.2 = true ∧ l.1 < basis.length) :
    ∃ t, clauseType basis clause = some t := by
  induction clause with
  | nil => contradiction
  | cons literal rest ih =>
    rcases literal with ⟨v, positive⟩
    obtain ⟨rfl, hv⟩ := h (v, positive) (by simp)
    have hb : basis[v]? = some basis[v] := List.getElem?_eq_some_iff.mpr ⟨hv, rfl⟩
    cases rest with
    | nil => exact ⟨basis[v], by simp [clauseType, hb]⟩
    | cons l rest =>
      obtain ⟨t, ht⟩ := ih (by simp) (fun a ha => h a (by simp [ha]))
      refine ⟨.join basis[v] t, ?_⟩
      rw [clauseType]
      simp [hb, ht]

theorem reify_complete {basis : List CompareTy} {clauses : CNF}
    (hp : Positive clauses) (hs : Supported (List.range basis.length) clauses)
    (ht : CNFHolds (fun _ => true) clauses)
    (hf : ¬CNFHolds (fun _ => false) clauses) :
    ∃ t, reify basis clauses = some t := by
  have hn : clauses ≠ [] := by intro he; simp [he, CNFHolds] at hf
  have hc : ∀ c ∈ clauses, ∃ t, clauseType basis c = some t := by
    intro c hc
    apply clauseType_complete
    · intro he
      have hh := ht c hc
      simp [he, ClauseHolds] at hh
    · intro l hl
      exact ⟨hp c hc l hl, List.mem_range.mp
        (hs l.1 (CNFPropagation.mem_atoms.mpr ⟨c, hc, l.2, hl⟩))⟩
  clear hp hs ht hf
  induction clauses with
  | nil => contradiction
  | cons c cs ih =>
    obtain ⟨a, ha⟩ := hc c (by simp)
    cases cs with
    | nil => exact ⟨a, by simp [reify, ha]⟩
    | cons c' cs =>
      obtain ⟨b, hb⟩ := ih (by simp) (fun d hd => hc d (by simp [hd]))
      refine ⟨.meet a b, ?_⟩
      rw [reify]
      simp [ha, hb]

theorem reconstruct_correct {basis : List CompareTy} {store : Store count}
    {images : Vector CompareTy count} (h : reconstruct basis store = some images) :
    ∀ v : Fin count, reify basis store[v] = some images[v] := by
  unfold reconstruct at h
  split at h
  · next hs =>
    cases h
    intro v
    have hi := (Vector.all_eq_true.mp hs) v.val v.isLt
    simp only [Vector.getElem_finRange] at hi
    change (reify basis store[v]).isSome = true at hi
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    cases he : reify basis store[v] with
    | none =>
      have hi' : (none : Option CompareTy).isSome = true := he ▸ hi
      contradiction
    | some t => rfl
  · contradiction

theorem reconstruct_complete {basis : List CompareTy} {store : Store count}
    (h : ∀ v : Fin count, ∃ t, reify basis store[v] = some t) :
    ∃ images, reconstruct basis store = some images := by
  have hs : (Vector.finRange count).all (fun v => (reify basis store[v]).isSome) = true := by
    apply Vector.all_eq_true.mpr
    intro i hi
    obtain ⟨t, ht⟩ := h ⟨i, hi⟩
    simpa only [Vector.getElem_finRange, ht] using (show (some t).isSome = true from rfl)
  simp only [reconstruct, hs, ↓reduceIte]
  exact ⟨_, rfl⟩

theorem residual_correct (program : Program count) (store : Store count) (σ : Nat → Bool) :
    CNFHolds σ (residual program store) ↔ CNFHolds σ program.checks ∧
      ∀ v : Fin count, CNFHolds σ store[v] → CNFHolds σ program.upper[v] := by
  have fold : ∀ indices : List (Fin count),
      CNFHolds σ (indices.foldr
        (fun v rest => meet (implies store[v] program.upper[v]) rest) program.checks) ↔
        CNFHolds σ program.checks ∧
          ∀ v ∈ indices, CNFHolds σ store[v] → CNFHolds σ program.upper[v] := by
    intro indices
    induction indices with
    | nil => simp
    | cons v indices ih =>
      simp only [List.foldr_cons, meet_correct, implies_correct, ih, List.forall_mem_cons]
      tauto
  simpa [residual, List.finRange] using fold (List.finRange count)

theorem diagonal_edge_iff {size : Nat} {condition : CNF} {store : Store count}
    {source target : Fin count} (hs : store.Supported size) :
    (∀ σ, CNFHolds σ (diagonal size condition) →
      CNFHolds (fun i => σ (2 * i)) store[source] →
      CNFHolds (fun i => σ (2 * i + 1)) store[target]) ↔
    (∀ σ, CNFHolds σ condition → CNFHolds σ store[source] → CNFHolds σ store[target]) := by
  constructor
  · intro h σ hc hd
    have hr : CNFHolds (fun i => σ (i / 2)) (diagonal size condition) := by
      apply (diagonal_correct _ _ _).mpr
      exact ⟨by simpa using hc, by simp⟩
    simpa using h (fun i => σ (i / 2)) hr (by simpa using hd)
  · intro h σ hr hd
    obtain ⟨hc, he⟩ := (diagonal_correct _ _ _).mp hr
    have ht := h (fun i => σ (2 * i)) hc hd
    exact (CNFPropagation.holds_congr
      (fun i hi => he i (List.mem_range.mp (hs target i hi)))).mp ht

theorem Program.valid_iff (program : Program count) (store : Store count) :
    program.Valid store ↔ program.lower.Le store ∧
      (∀ e ∈ program.edges, ∀ σ, CNFHolds σ e.relation →
        CNFHolds (fun i => σ (2 * i)) store[e.source] →
        CNFHolds (fun i => σ (2 * i + 1)) store[e.target]) ∧
      (∀ σ, CNFHolds σ program.checks) ∧
      ∀ σ (v : Fin count), CNFHolds σ store[v] → CNFHolds σ program.upper[v] := by
  simp only [Program.Valid, Program.Closed, residual_correct, forall_and, and_assoc]

private theorem lower_update_correct (condition : CNF) (lower store : Store count)
    (v : Fin count) :
    Store.Le (Vector.ofFn fun w : Fin count =>
      if w == v then join condition lower[w] else lower[w]) store ↔
      lower.Le store ∧ ∀ σ, CNFHolds σ condition → CNFHolds σ store[v] := by
  simp only [Store.Le, Fin.getElem_fin, Vector.getElem_ofFn, beq_iff_eq]
  constructor
  · intro h
    constructor
    · intro w σ hw
      apply h w σ
      by_cases he : w = v
      · subst w; simp [join_correct, hw]
      · simp [he, hw]
    · intro σ hc
      apply h v σ
      simp [join_correct, hc]
  · rintro ⟨hl, hv⟩ w σ hw
    by_cases he : w = v
    · subst w
      simp only [↓reduceIte, join_correct] at hw
      exact hw.elim (hv σ) (hl v σ)
    · simp only [he, ↓reduceIte] at hw
      exact hl w σ hw

private theorem upper_update_correct (condition : CNF) (upper store : Store count)
    (v : Fin count) :
    (∀ σ (w : Fin count), CNFHolds σ store[w] →
      CNFHolds σ (Vector.ofFn fun i : Fin count =>
        if i == v then meet condition upper[i] else upper[i])[w]) ↔
    (∀ σ (w : Fin count), CNFHolds σ store[w] → CNFHolds σ upper[w]) ∧
      ∀ σ, CNFHolds σ store[v] → CNFHolds σ condition := by
  simp only [Fin.getElem_fin, Vector.getElem_ofFn, beq_iff_eq]
  constructor
  · intro h
    constructor
    · intro σ w hw
      have hh := h σ w hw
      by_cases he : w = v
      · subst w
        simp only [↓reduceIte, meet_correct] at hh
        exact hh.2
      · simpa only [he, ↓reduceIte] using hh
    · intro σ hv
      have hh := h σ v hv
      exact ((meet_correct _ _ _).mp (by simpa using hh)).1
  · rintro ⟨hu, hv⟩ σ w hw
    by_cases he : w = v
    · subst w
      simp only [↓reduceIte, meet_correct]
      exact ⟨hv σ hw, hu σ v hw⟩
    · simp only [he, ↓reduceIte]
      exact hu σ w hw

theorem Program.add_valid {size : Nat} {program : Program count} {store : Store count}
    (hs : store.Supported size) (obligation : Obligation count) :
    (program.add size obligation).Valid store ↔
      program.Valid store ∧ ∀ σ, obligation.Holds σ (fun v => CNFHolds σ store[v]) := by
  cases obligation with
  | lower v condition =>
    simp only [Program.valid_iff, Program.add, lower_update_correct, Obligation.Holds]
    tauto
  | upper v condition =>
    simp only [Program.valid_iff, Program.add, upper_update_correct, Obligation.Holds]
    tauto
  | edge source target condition =>
    simp only [Program.valid_iff, Program.add, List.forall_mem_cons, diagonal_edge_iff hs,
      Obligation.Holds]
    tauto
  | check condition =>
    simp only [Program.valid_iff, Program.add, meet_correct, forall_and, Obligation.Holds]
    tauto

theorem Program.empty_valid (count : Nat) (store : Store count) :
    (Program.empty count).Valid store := by
  rw [Program.valid_iff]
  simp [Program.empty, Store.Le, CNFHolds, ClauseHolds]

theorem compile_correct {size : Nat} (action : ModExpr → Action) (theory : CNF)
    (bounds : List (Bound count)) {store : Store count} (hs : store.Supported size) :
    (compile size action theory bounds).Valid store ↔
      ∀ bound ∈ bounds, ∀ σ, CNFHolds σ theory →
        bound.left.Holds action σ (fun v => CNFHolds σ store[v]) →
        bound.right.Holds action σ (fun v => CNFHolds σ store[v]) := by
  have fold : ∀ obligations : List (Obligation count), ∀ program : Program count,
      (obligations.foldl (Program.add size) program).Valid store ↔
        program.Valid store ∧ ∀ o ∈ obligations, ∀ σ,
          o.Holds σ (fun v => CNFHolds σ store[v]) := by
    intro obligations
    induction obligations with
    | nil => simp
    | cons o os ih =>
      intro program
      simp only [List.foldl_cons, ih, Program.add_valid hs, List.forall_mem_cons]
      tauto
  rw [compile, fold]
  simp only [Program.empty_valid, true_and, List.forall_mem_flatMap]
  apply forall_congr'
  intro bound
  apply forall_congr'
  intro _
  rw [show (∀ o ∈ compileBound action theory bound, ∀ σ,
      o.Holds σ (fun v => CNFHolds σ store[v])) ↔
      (∀ σ, ∀ o ∈ compileBound action theory bound,
        o.Holds σ (fun v => CNFHolds σ store[v])) from ⟨fun h σ o ho => h o ho σ,
        fun h o ho σ => h σ o ho⟩]
  exact forall_congr' fun σ => compileBound_correct action theory bound σ _

def Leaf.Nonzero (size : Nat) (leaf : Leaf count) : Prop :=
  match leaf with
  | .fixed value => ∀ σ, ZeroOn size σ → ¬CNFHolds σ value
  | .flex _ => True

def Obligation.Nonzero (size : Nat) (obligation : Obligation count) : Prop :=
  match obligation with
  | .lower _ condition => ∀ σ, ZeroOn size σ → ¬CNFHolds σ condition
  | _ => True

def Program.Nonzero (size : Nat) (program : Program count) : Prop :=
  LowerNonzero size program.lower ∧ ∀ e ∈ program.edges, e.ZeroReflecting size

theorem compileBound_nonzero {size : Nat} {action : ModExpr → Action} (theory : CNF)
    (bound : Bound count)
    (ha : ∀ m σ, ZeroOn size σ → ¬CNFHolds σ (action m).lower)
    (hb : bound.left.leaf.Nonzero size) :
    ∀ obligation ∈ compileBound action theory bound, obligation.Nonzero size := by
  rcases bound with ⟨⟨left, lm⟩, ⟨right, rm⟩⟩
  cases left <;> cases right <;> simp [compileBound, Obligation.Nonzero]
  · next value _ =>
      intro σ hz
      have hl := ha lm σ hz
      have hf := hb σ hz
      simp only [meet_correct, Action.apply, join_correct]
      tauto
  · intro σ hz
    have hl := ha lm σ hz
    simp only [meet_correct]
    tauto

theorem Program.empty_nonzero (size count : Nat) : (Program.empty count).Nonzero size := by
  simp [Program.Nonzero, Program.empty, LowerNonzero, CNFHolds, ClauseHolds]

theorem Program.add_nonzero {size : Nat} {program : Program count}
    (hp : program.Nonzero size) {obligation : Obligation count}
    (ho : obligation.Nonzero size) : (program.add size obligation).Nonzero size := by
  rcases hp with ⟨hl, he⟩
  cases obligation with
  | lower v condition =>
    refine ⟨?_, he⟩
    intro w σ hz hh
    simp only [Program.add, Fin.getElem_fin, Vector.getElem_ofFn, beq_iff_eq] at hh
    by_cases hw : w = v
    · simp only [hw, ↓reduceIte, join_correct] at hh
      exact hh.elim (ho σ hz) (hl v σ hz)
    · simp only [hw, ↓reduceIte] at hh
      exact hl w σ hz hh
  | edge source target condition =>
    refine ⟨hl, ?_⟩
    intro e hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact diagonal_zeroReflecting size condition source target
    · exact he e hm
  | upper v condition => exact ⟨hl, he⟩
  | check condition => exact ⟨hl, he⟩

theorem compile_nonzero {size : Nat} {action : ModExpr → Action} (theory : CNF)
    (bounds : List (Bound count))
    (ha : ∀ m σ, ZeroOn size σ → ¬CNFHolds σ (action m).lower)
    (hb : ∀ b ∈ bounds, b.left.leaf.Nonzero size) :
    (compile size action theory bounds).Nonzero size := by
  have ho : ∀ o ∈ bounds.flatMap (compileBound action theory), o.Nonzero size := by
    intro o hm
    obtain ⟨b, hmem, hm⟩ := List.mem_flatMap.mp hm
    exact compileBound_nonzero theory b ha (hb b hmem) o hm
  have fold : ∀ obligations : List (Obligation count), ∀ program : Program count,
      program.Nonzero size → (∀ o ∈ obligations, o.Nonzero size) →
        (obligations.foldl (Program.add size) program).Nonzero size := by
    intro obligations
    induction obligations with
    | nil => simp
    | cons o os ih =>
      intro program hp ho
      exact ih (program.add size o) (Program.add_nonzero hp (ho o (by simp)))
        (fun p hm => ho p (by simp [hm]))
  exact fold _ _ (Program.empty_nonzero size count) ho

/-- The residual reducer exposes the actual propagated store and an exact
syntax image for every variable; it does not decide any residual parameters. -/
theorem reduce_correct {basis : List CompareTy} {program : Program count}
    {result : Reduction count} (h : reduce basis program = .success result) :
    result.store = propagate basis.length program.edges program.lower ∧
      (∀ v : Fin count, reify basis result.store[v] = some result.images[v]) ∧
      result.obligation = residual program result.store := by
  dsimp only [reduce] at h
  split at h
  · contradiction
  · next images he =>
    cases h
    exact ⟨rfl, reconstruct_correct he, rfl⟩

theorem reduce_obligation {basis : List CompareTy} {program : Program count}
    {result : Reduction count} (h : reduce basis program = .success result) (σ : Nat → Bool) :
    CNFHolds σ result.obligation ↔ CNFHolds σ program.checks ∧
      ∀ v : Fin count, CNFHolds σ result.store[v] → CNFHolds σ program.upper[v] := by
  rw [(reduce_correct h).2.2]
  exact residual_correct program result.store σ

theorem reduce_images {basis : List CompareTy} {program : Program count}
    {result : Reduction count} (h : reduce basis program = .success result)
    (value : CompareTy → Bool)
    (hj : ∀ a b, value (.join a b) = (value a || value b))
    (hm : ∀ a b, value (.meet a b) = (value a && value b)) (v : Fin count) :
    value result.images[v] = true ↔ CNFHolds (basisValue basis value) result.store[v] :=
  reify_correct ((reduce_correct h).2.1 v) value hj hm

/-- Nonempty bases and zero-reflecting transitions need no type extrema. This
guarantee does not require the residual modality obligations to hold. -/
theorem reduce_complete {basis : List CompareTy} {program : Program count}
    (hb : 0 < basis.length) (hl : LowerNonzero basis.length program.lower)
    (he : ∀ e ∈ program.edges, e.ZeroReflecting basis.length) :
    ∃ result, reduce basis program = .success result := by
  obtain ⟨images, hi⟩ := reconstruct_complete (fun v => reify_complete
    (propagate_positive _ _ _ v) (propagate_supported _ _ _ v)
    (propagate_all_true _ _ _ v) (propagate_nonzero hb hl he v))
  exact ⟨⟨propagate basis.length program.edges program.lower, images,
    residual program (propagate basis.length program.edges program.lower)⟩,
    by simp only [reduce, hi]⟩

/-- The normalized modal-leaf compiler always reconstructs actual finite images,
even when the remaining mode obligation is inconsistent. -/
theorem compile_reduce_complete {basis : List CompareTy} {action : ModExpr → Action}
    (theory : CNF) (bounds : List (Bound count)) (hsize : 0 < basis.length)
    (ha : ∀ m σ, ZeroOn basis.length σ → ¬CNFHolds σ (action m).lower)
    (hb : ∀ b ∈ bounds, b.left.leaf.Nonzero basis.length) :
    ∃ result, reduce basis (compile basis.length action theory bounds) = .success result := by
  have hn := compile_nonzero theory bounds ha hb
  exact reduce_complete hsize hn.1 hn.2

theorem reduce_polynomial {basis : List CompareTy} {program : Program count}
    {result : Reduction count} (h : reduce basis program = .success result) :
    result.store.Polynomial basis.length := by
  obtain ⟨hs, hi, _⟩ := reduce_correct h
  refine ⟨?_, ?_, ?_, fun v => reify_nonzero (hi v)⟩
  · rw [hs]; exact propagate_positive _ _ _
  · rw [hs]; exact propagate_supported _ _ _
  · rw [hs]; exact propagate_all_true _ _ _

theorem reduce_closed {basis : List CompareTy} {program : Program count}
    {result : Reduction count} (h : reduce basis program = .success result) :
    program.Closed result.store := by
  rw [(reduce_correct h).1]
  exact propagate_closed _ _

/-- Reduction followed by universal validation of the residual is exact for
finite positive lattice polynomials over the explicit basis. -/
theorem reduce_solves_iff (basis : List CompareTy) (program : Program count) :
    (∃ result, reduce basis program = .success result ∧
      ∀ σ, CNFHolds σ result.obligation) ↔
    ∃ store, store.Polynomial basis.length ∧ program.Valid store := by
  constructor
  · rintro ⟨result, hr, ho⟩
    refine ⟨result.store, reduce_polynomial hr, reduce_closed hr, ?_⟩
    intro σ
    rw [← (reduce_correct hr).2.2]
    exact ho σ
  · rintro ⟨store, hp, hc, ho⟩
    have hl := propagate_least_closed hp.1 hp.2.1 hp.2.2.1 hc
    have hn : (propagate basis.length program.edges program.lower).Nonzero :=
      fun v h => hp.2.2.2 v (hl v _ h)
    obtain ⟨images, hi⟩ := reconstruct_complete (fun v => reify_complete
      (propagate_positive _ _ _ v) (propagate_supported _ _ _ v)
      (propagate_all_true _ _ _ v) (hn v))
    let result : Reduction count := ⟨propagate basis.length program.edges program.lower,
      images, residual program (propagate basis.length program.edges program.lower)⟩
    refine ⟨result, ?_, ?_⟩
    · simp only [reduce, hi, result]
    · intro σ
      apply (residual_correct _ _ _).mpr
      obtain ⟨hcheck, hupper⟩ := (residual_correct _ _ _).mp (ho σ)
      exact ⟨hcheck, fun v h => hupper v (hl v σ h)⟩

end ModalityInference.ComparisonPropagation
