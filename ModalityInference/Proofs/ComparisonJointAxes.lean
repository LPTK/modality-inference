import ModalityInference.ComparisonJointAxes
import ModalityInference.Proofs.ModalSynthesis

/-! A coordinate clause has one constant choice between its own-axis component
and an opposite-axis scalar component. The choice is shared by all valuations. -/
namespace ModalityInference.ComparisonJointAxes

abbrev State (count : Nat) := (Nat → Bool) → (Nat → Bool) → Fin count → Bool

/-- Coordinate states may depend on head observations and their own input axis. -/
def StateUniform (side : Nat → Bool) (component : Bool) (state : State count) : Prop :=
  ∀ heads ρ τ, (∀ v, side v = component → ρ v = τ v) →
    ∀ i, state heads ρ i = state heads τ i

/-- Every synthesized scalar output depends on inputs from its own axis. -/
def ModeUniform (side : Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool) : Prop :=
  ∀ ρ τ v, (∀ w, side w = side v → ρ w = τ w) → strategy ρ v = strategy τ v

def valuation (heads : Nat) (state : State count)
    (strategy : (Nat → Bool) → Nat → Bool) (headWorld inputWorld : Nat → Bool)
    (v : Nat) : Bool :=
  if hv : v < count then state headWorld inputWorld ⟨v, hv⟩
  else if v < count + heads then headWorld (v - count)
  else strategy inputWorld (v - (count + heads))

@[simp] theorem encode_even (choice inputs : Nat → Bool) (v : Nat) :
    encode choice inputs (2 * v) = inputs v := by simp [encode]

@[simp] theorem encode_odd (choice inputs : Nat → Bool) (v : Nat) :
    encode choice inputs (2 * v + 1) = choice v := by
  simp [encode, show (2 * v + 1) / 2 = v by omega]

theorem encoded_clause (choice inputs : Nat → Bool) (index : Nat) (polarity : Bool)
    (clause : Clause) :
    ClauseHolds (encode choice inputs)
      ((2 * index + 1, polarity) :: clause.map (fun literal => (2 * literal.1, literal.2))) ↔
      choice index = polarity ∨ ClauseHolds inputs clause := by
  rw [clauseHolds_cons]
  simp [ClauseHolds, List.mem_map, Prod.exists]

theorem ownClauses_holds (side : Nat → Bool) (component : Bool) (count heads : Nat)
    (clauses : CNF) (choice inputs : Nat → Bool) :
    CNFHolds (encode choice inputs) (ownClauses side component count heads clauses) ↔
      ∀ i (hi : i < clauses.length), choice i = false ∨
        ClauseHolds inputs (ownPart side component count heads clauses[i]) := by
  simp only [CNFHolds, ownClauses, List.forall_mem_map, List.forall_mem_zipIdx', encoded_clause]

theorem otherClauses_holds (side : Nat → Bool) (component : Bool) (count heads : Nat)
    (clauses : CNF) (choice inputs : Nat → Bool) :
    CNFHolds (encode choice inputs) (otherClauses side component count heads clauses) ↔
      ∀ i (hi : i < clauses.length), choice i = true ∨
        ClauseHolds inputs (otherPart side component count heads clauses[i]) := by
  simp only [CNFHolds, otherClauses, List.forall_mem_map, List.forall_mem_zipIdx', encoded_clause]

theorem valuation_uniform {side : Nat → Bool} {component : Bool} {heads : Nat}
    {state : State count} {strategy : (Nat → Bool) → Nat → Bool}
    (hs : StateUniform side component state) (hm : ModeUniform side strategy)
    (headWorld : Nat → Bool) {ρ τ : Nat → Bool}
    (hρ : ∀ v, side v = component → ρ v = τ v) {v : Nat}
    (hv : own side component count heads v = true) :
    valuation heads state strategy headWorld ρ v =
      valuation heads state strategy headWorld τ v := by
  unfold valuation
  split
  · exact hs headWorld ρ τ hρ _
  · split
    · rfl
    · rename_i htail
      have hside : side (v - (count + heads)) = component := by
        simpa [own, htail] using hv
      exact hm ρ τ _ (fun w hw => hρ w (hw.trans hside))

theorem valuation_other {side : Nat → Bool} {component : Bool} {heads : Nat}
    (state : State count) (strategy : (Nat → Bool) → Nat → Bool)
    (headWorld inputWorld : Nat → Bool) {v : Nat}
    (hv : own side component count heads v = false) :
    valuation heads state strategy headWorld inputWorld v =
      strategy inputWorld (v - (count + heads)) := by
  have ht : ¬v < count + heads := by
    simpa only [own, Bool.or_eq_false_iff, decide_eq_false_iff_not] using
      (Bool.or_eq_false_iff.mp hv).1
  have hn : ¬v < count := by omega
  simp [valuation, hn, ht]

theorem clause_parts (side : Nat → Bool) (component : Bool) (heads : Nat)
    (state : State count) (strategy : (Nat → Bool) → Nat → Bool)
    (headWorld inputWorld : Nat → Bool) (clause : Clause) :
    ClauseHolds (valuation heads state strategy headWorld inputWorld) clause ↔
      ClauseHolds (valuation heads state strategy headWorld inputWorld)
        (ownPart side component count heads clause) ∨
      ClauseHolds (strategy inputWorld) (otherPart side component count heads clause) := by
  constructor
  · rintro ⟨v, b, hv, he⟩
    cases how : own side component count heads v with
    | true => exact .inl ⟨v, b, List.mem_filter.mpr ⟨hv, how⟩, he⟩
    | false =>
      refine .inr ⟨v - (count + heads), b, ?_, ?_⟩
      · exact List.mem_map.mpr ⟨(v, b), List.mem_filter.mpr ⟨hv, by simp [how]⟩, rfl⟩
      · exact (valuation_other state strategy headWorld inputWorld how).symm.trans he
  · rintro (⟨v, b, hv, he⟩ | ⟨v, b, hv, he⟩)
    · exact ⟨v, b, (List.mem_filter.mp hv).1, he⟩
    · obtain ⟨⟨w, c⟩, hw, heq⟩ := List.mem_map.mp hv
      cases heq
      obtain ⟨hw, ho⟩ := List.mem_filter.mp hw
      have ho : own side component count heads w = false := by simpa using ho
      exact ⟨w, c, hw, (valuation_other state strategy headWorld inputWorld ho).trans he⟩

theorem clause_factor {side : Nat → Bool} {component : Bool} {heads : Nat}
    {state : State count} {strategy : (Nat → Bool) → Nat → Bool}
    (hs : StateUniform side component state) (hm : ModeUniform side strategy)
    {clause : Clause}
    (h : ∀ headWorld inputWorld, ClauseHolds (valuation heads state strategy headWorld inputWorld) clause) :
    (∀ headWorld inputWorld,
      ClauseHolds (valuation heads state strategy headWorld inputWorld)
        (ownPart side component count heads clause)) ∨
    (∀ inputWorld, ClauseHolds (strategy inputWorld)
      (otherPart side component count heads clause)) := by
  classical
  by_cases ho : ∀ headWorld inputWorld,
      ClauseHolds (valuation heads state strategy headWorld inputWorld)
        (ownPart side component count heads clause)
  · exact .inl ho
  · right
    intro τ
    by_contra ht
    obtain ⟨headWorld, hh⟩ := not_forall.mp ho
    obtain ⟨ρ, hρ⟩ := not_forall.mp hh
    let mixed : Nat → Bool := fun v => if side v = component then ρ v else τ v
    obtain ⟨v, b, hv, he⟩ := h headWorld mixed
    cases how : own side component count heads v with
    | false =>
      have hparts : ¬v < count + heads ∧ side (v - (count + heads)) ≠ component := by
        simpa [own] using how
      have hvn : ¬v < count := by omega
      have he : strategy mixed (v - (count + heads)) = b := by
        simpa [valuation, hvn, hparts.1] using he
      have heq := hm mixed τ (v - (count + heads)) (fun w hw => by
        have hwc : side w ≠ component := fun hc => hparts.2 (hw.symm.trans hc)
        simp [mixed, hwc])
      apply ht
      refine ⟨v - (count + heads), b, ?_, heq.symm.trans he⟩
      exact List.mem_map.mpr ⟨(v, b), List.mem_filter.mpr ⟨hv, by simp [how]⟩, rfl⟩
    | true =>
      have heq := valuation_uniform hs hm headWorld
        (ρ := mixed) (τ := ρ) (fun w hw => by simp [mixed, hw]) how
      exact hρ ⟨v, b, List.mem_filter.mpr ⟨hv, how⟩, heq.symm.trans he⟩

/-- Constant selectors are chosen once for the entire family of valuations. -/
theorem selectors_complete {side : Nat → Bool} {component : Bool} {heads : Nat}
    {state : State count} {strategy : (Nat → Bool) → Nat → Bool}
    (hs : StateUniform side component state) (hm : ModeUniform side strategy)
    {clauses : CNF}
    (h : ∀ headWorld inputWorld,
      CNFHolds (valuation heads state strategy headWorld inputWorld) clauses) :
    ∃ choice,
      (∀ headWorld inputWorld, CNFHolds
        (encode choice (valuation heads state strategy headWorld inputWorld))
        (ownClauses side component count heads clauses)) ∧
      (∀ inputWorld, CNFHolds (encode choice (strategy inputWorld))
        (otherClauses side component count heads clauses)) := by
  classical
  let choice : Nat → Bool := fun i => decide (∀ headWorld inputWorld,
    ClauseHolds (valuation heads state strategy headWorld inputWorld)
      (ownPart side component count heads ((clauses[i]?).getD [])))
  have choice_eq (i : Nat) (hi : i < clauses.length) : choice i = decide
      (∀ headWorld inputWorld,
        ClauseHolds (valuation heads state strategy headWorld inputWorld)
          (ownPart side component count heads clauses[i])) := by
    simp [choice, List.getElem?_eq_getElem hi]
  refine ⟨choice, ?_, ?_⟩
  · intro headWorld inputWorld
    rw [ownClauses_holds]
    intro i hi
    by_cases ho : ∀ headWorld inputWorld,
        ClauseHolds (valuation heads state strategy headWorld inputWorld)
          (ownPart side component count heads clauses[i])
    · exact .inr (ho headWorld inputWorld)
    · exact .inl ((choice_eq i hi).trans (decide_eq_false ho))
  · intro inputWorld
    rw [otherClauses_holds]
    intro i hi
    by_cases ho : ∀ headWorld inputWorld,
        ClauseHolds (valuation heads state strategy headWorld inputWorld)
          (ownPart side component count heads clauses[i])
    · exact .inl ((choice_eq i hi).trans (decide_eq_true ho))
    · exact .inr ((clause_factor hs hm
        (fun headWorld inputWorld => h headWorld inputWorld _ (List.getElem_mem hi))).resolve_left ho inputWorld)

theorem selectors_sound {side : Nat → Bool} {component : Bool} {heads : Nat}
    {state : State count} {strategy : (Nat → Bool) → Nat → Bool}
    {clauses : CNF} {choice : Nat → Bool}
    (ho : ∀ headWorld inputWorld, CNFHolds
      (encode choice (valuation heads state strategy headWorld inputWorld))
      (ownClauses side component count heads clauses))
    (ht : ∀ inputWorld, CNFHolds (encode choice (strategy inputWorld))
      (otherClauses side component count heads clauses)) :
    ∀ headWorld inputWorld,
      CNFHolds (valuation heads state strategy headWorld inputWorld) clauses := by
  intro headWorld inputWorld clause hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hown := (ownClauses_holds side component count heads clauses choice _).mp
    (ho headWorld inputWorld) i hi
  have hother := (otherClauses_holds side component count heads clauses choice _).mp
    (ht inputWorld) i hi
  apply (clause_parts side component heads state strategy headWorld inputWorld clauses[i]).mpr
  cases hchoice : choice i with
  | false => exact .inr (hother.resolve_left (by simp [hchoice]))
  | true => exact .inl (hown.resolve_left (by simp [hchoice]))

/-- Exact axis separation under the permitted state and scalar dependencies.
The same existential selector assignment serves every head and scalar input. -/
theorem uniform_iff {side : Nat → Bool} {component : Bool} {heads : Nat}
    {state : State count} {strategy : (Nat → Bool) → Nat → Bool}
    (hs : StateUniform side component state) (hm : ModeUniform side strategy)
    (clauses : CNF) :
    (∀ headWorld inputWorld,
      CNFHolds (valuation heads state strategy headWorld inputWorld) clauses) ↔
    ∃ choice,
      (∀ headWorld inputWorld, CNFHolds
        (encode choice (valuation heads state strategy headWorld inputWorld))
        (ownClauses side component count heads clauses)) ∧
      (∀ inputWorld, CNFHolds (encode choice (strategy inputWorld))
        (otherClauses side component count heads clauses)) :=
  ⟨selectors_complete hs hm, fun ⟨_, ho, ht⟩ => selectors_sound ho ht⟩

end ModalityInference.ComparisonJointAxes
