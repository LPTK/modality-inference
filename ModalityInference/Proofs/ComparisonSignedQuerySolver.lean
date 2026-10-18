import ModalityInference.ComparisonSignedQuerySolver
import ModalityInference.Proofs.ComparisonSignedQueries

namespace ModalityInference.ComparisonSignedQuerySolver
open ComparisonPropagation ComparisonSignedSynthesis ComparisonSignedQueries ComparisonSignedRelations

theorem parameter_value (p : Nat → Bool) :
    ComparisonSignedPolynomials.substValue parameter p=value p (fun _=>false) (fun _=>false) := by
  funext i
  have hi : i%3<3 := Nat.mod_lt _ (by omega)
  rcases (by omega : i%3=0 ∨ i%3=1 ∨ i%3=2) with h|h|h
  all_goals simp [ComparisonSignedPolynomials.substValue,parameter,value,h]

theorem condition_correct (input : Input) (r scalar : CNF) (p : Nat → Bool) :
    CNFHolds p (condition input r scalar) ↔
      Holds p (input.consistent r) (fun _=>false) (fun _=>false) ∧ CNFHolds p scalar := by
  rw [condition,cnfHolds_append,ComparisonSignedPolynomials.specialize_correct,parameter_value]
  rfl

theorem run_spec {fuel : Nat} {input : Input} {queries : List Query} {scalar : CNF}
    {result : Solution} (h : run fuel input queries scalar=.success result) :
    ∃r,ComparisonSignedQueries.compile input queries=some r ∧
      CNFPropagation.solve fuel (condition input r scalar)=.success result.selectors ∧
      input.reconstruct r (CNFPropagation.valuation result.selectors)=some result.images := by
  cases hc : ComparisonSignedQueries.compile input queries <;>
    simp [run,hc,bind,RunResult.bind] at h
  rename_i r
  cases hs : CNFPropagation.solve fuel (condition input r scalar) <;>
    simp [hs] at h
  rename_i selectors
  cases hi : input.reconstruct r (CNFPropagation.valuation selectors) <;> simp [hi,pure] at h
  subst result
  exact ⟨r,rfl,hs,hi⟩

/-- Every returned image comes from the same canonical model and selector
valuation; this valuation also satisfies the supplied common scalar query. -/
theorem run_sound {fuel : Nat} {input : Input} {queries : List Query} {scalar : CNF}
    (ha : ∀q∈queries,q.Allowed input.keys)
    {result : Solution} (h : run fuel input queries scalar=.success result) :
    ∃r,ComparisonSignedQueries.compile input queries=some r ∧
      input.reconstruct r (CNFPropagation.valuation result.selectors)=some result.images ∧
      CNFHolds (CNFPropagation.valuation result.selectors) scalar ∧
      result.images.map Prod.fst=input.keys ∧
      Family input (input.imageValue r (CNFPropagation.valuation result.selectors)) ∧
      ∀q∈queries,q.Valid (CNFPropagation.valuation result.selectors)
        (input.imageValue r (CNFPropagation.valuation result.selectors)) := by
  obtain ⟨r,hr,hs,hi⟩ := run_spec h
  obtain ⟨hcons,hscalar⟩ := (condition_correct input r scalar _).mp (CNFPropagation.solve_sound hs)
  obtain ⟨hf,hv⟩ := imageValue_valid hr ha _ hcons
  exact ⟨r,hr,hi,hscalar,(input.reconstruct_spec hi).1,hf,hv⟩

/-- A single family and selector valuation satisfying all nominal and scalar
queries suffice for actual successful execution at all sufficiently large fuel. -/
theorem run_complete (input : Input) (queries : List Query) (scalar : CNF)
    (hb : ∀q∈queries,∀c∈q.clauses,c.literals.length≤2)
    (ha : ∀q∈queries,q.Allowed input.keys)
    {p : Nat → Bool} {images : Nat → (Nat → Bool) → Bool}
    (hf : Family input images) (hv : ∀q∈queries,q.Valid p images)
    (hs : CNFHolds p scalar) :
    ∃threshold,∀fuel≥threshold,∃result,run fuel input queries scalar=.success result := by
  obtain ⟨r,hr⟩ := ComparisonSignedQueries.compile_complete input queries hb
  have hc := (consistent_iff hr ha p).mpr ⟨images,hf,hv⟩
  obtain ⟨threshold,ht⟩ := CNFPropagation.solve_complete
    ((condition_correct input r scalar p).mpr ⟨hc,hs⟩)
  refine ⟨threshold,?_⟩
  intro fuel hfu
  obtain ⟨selectors,hselectors⟩ := ht fuel hfu
  have hc' := ((condition_correct input r scalar _).mp (CNFPropagation.solve_sound hselectors)).1
  obtain ⟨types,htypes⟩ := reconstruct_complete hr (CNFPropagation.valuation selectors) hc'
  exact ⟨⟨selectors,types⟩,by simp [run,hr,hselectors,htypes,bind,pure,RunResult.bind]⟩

theorem run_terminates (input : Input) (queries : List Query) (scalar : CNF) :
    ∃threshold,∀fuel≥threshold,run fuel input queries scalar≠.exhausted := by
  cases hc : ComparisonSignedQueries.compile input queries with
  | none => exact ⟨0,fun _ _=>by simp [run,hc,bind,RunResult.bind]⟩
  | some r =>
      obtain ⟨threshold,ht⟩ := CNFPropagation.solve_terminates (condition input r scalar)
      refine ⟨threshold,?_⟩
      intro fuel hf
      cases hs : CNFPropagation.solve fuel (condition input r scalar) with
      | exhausted => exact False.elim (ht fuel hf hs)
      | rejected message => simp [run,hc,hs,bind,RunResult.bind]
      | success selectors =>
          cases hi : input.reconstruct r (CNFPropagation.valuation selectors) <;>
            simp [run,hc,hs,hi,bind,pure,RunResult.bind]

theorem run_stable {n : Nat} {input : Input} {queries : List Query} {scalar : CNF}
    {result : RunResult Solution} (hne : result≠.exhausted)
    (h : run n input queries scalar=result) :
    ∀fuel≥n,run fuel input queries scalar=result := by
  intro fuel hf
  cases hc : ComparisonSignedQueries.compile input queries with
  | none => simpa [run,hc,bind,RunResult.bind] using h
  | some r =>
      have he : CNFPropagation.solve n (condition input r scalar)≠.exhausted := by
        intro hs
        apply hne
        simpa [run,hc,hs,bind,RunResult.bind] using h.symm
      have hs := CNFPropagation.solve_stable he rfl fuel hf
      simpa only [run,hc,bind,RunResult.bind,hs] using h

theorem run_complete_stable (input : Input) (queries : List Query) (scalar : CNF)
    (hb : ∀q∈queries,∀c∈q.clauses,c.literals.length≤2)
    (ha : ∀q∈queries,q.Allowed input.keys)
    {p : Nat → Bool} {images : Nat → (Nat → Bool) → Bool}
    (hf : Family input images) (hv : ∀q∈queries,q.Valid p images)
    (hs : CNFHolds p scalar) :
    ∃threshold result,∀fuel≥threshold,run fuel input queries scalar=.success result := by
  obtain ⟨threshold,ht⟩ := run_complete input queries scalar hb ha hf hv hs
  obtain ⟨result,hr⟩ := ht threshold le_rfl
  exact ⟨threshold,result,run_stable (by simp) hr⟩

theorem run_success_iff (input : Input) (queries : List Query) (scalar : CNF)
    (hb : ∀q∈queries,∀c∈q.clauses,c.literals.length≤2)
    (ha : ∀q∈queries,q.Allowed input.keys) :
    (∃fuel result,run fuel input queries scalar=.success result) ↔
      ∃p images,Family input images ∧ (∀q∈queries,q.Valid p images) ∧ CNFHolds p scalar := by
  constructor
  · rintro ⟨fuel,result,hr⟩
    obtain ⟨r,_,_,hs,_,hf,hv⟩ := run_sound ha hr
    exact ⟨CNFPropagation.valuation result.selectors,input.imageValue r _,hf,hv,hs⟩
  · rintro ⟨p,images,hf,hv,hs⟩
    obtain ⟨fuel,ht⟩ := run_complete input queries scalar hb ha hf hv hs
    obtain ⟨result,hr⟩ := ht fuel le_rfl
    exact ⟨fuel,result,hr⟩

end ModalityInference.ComparisonSignedQuerySolver
