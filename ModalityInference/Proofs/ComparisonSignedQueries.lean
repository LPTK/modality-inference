import ModalityInference.ComparisonSignedQueries
import ModalityInference.Proofs.ComparisonSignedFamily

namespace ModalityInference.ComparisonSignedQueries
open ComparisonPropagation ComparisonSignedRelations ComparisonSignedPolynomials
open ComparisonSignedEndpoints ComparisonSignedEdges ComparisonSignedCanonical ComparisonSignedSynthesis

def Query.Valid (query : Query) (p : Nat → Bool) (images : Nat → (Nat → Bool) → Bool) : Prop :=
  ∀w,CNFHolds (decoded query.decode p w) query.theory → ∀c∈query.clauses,
    c.Holds (decoded query.decode p w)
      (fun call=>images call.name (fun i=>decoded query.decode p w (query.payload call i)))

def Query.Allowed (query : Query) (keys : List Nat) : Prop :=
  ∀c∈query.clauses,∀literal∈c.literals,literal.1.name∈keys

theorem compile_complete (input : Input) (queries : List Query)
    (h : ∀q∈queries,∀c∈q.clauses,c.literals.length≤2) :
    ∃r,compile input queries=some r := by
  induction queries with
  | nil => exact ⟨_,rfl⟩
  | cons q qs ih =>
      obtain ⟨head,hh⟩ := ComparisonSignedEdges.compile_complete (payload:=q.payload)
        (width:=input.width) (key:=input.key) (size:=fun n=>(input.bases n).length)
        (decode:=q.decode) (theory:=q.theory) (h q List.mem_cons_self)
      obtain ⟨tail,ht⟩ := ih (fun q hq=>h q (List.mem_cons_of_mem _ hq))
      exact ⟨join head tail,by simp [compile,Query.compile,hh,ht]⟩

theorem compile_spec {input : Input} {queries : List Query} {r : CNF}
    (h : compile input queries=some r) : ∀q∈queries,∃rq,q.compile input=some rq := by
  induction queries generalizing r with
  | nil => simp
  | cons q qs ih =>
      cases hh : q.compile input <;> simp only [compile,hh,Option.bind_eq_bind] at h
      · simp at h
      rename_i head
      cases ht : compile input qs <;> simp [ht] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl|ha
      · exact ⟨head,hh⟩
      · exact ih ht a ha

theorem compile_correct {input : Input} {queries : List Query} {r : CNF}
    (h : compile input queries=some r) (p a b : Nat → Bool) :
    Holds p r a b ↔ ∃q∈queries,∃rq,q.compile input=some rq ∧ Holds p rq a b := by
  induction queries generalizing r with
  | nil =>
      simp only [compile,Option.some.injEq] at h
      subst r
      simp [Holds,CNFHolds,ClauseHolds]
  | cons q qs ih =>
      cases hh : q.compile input <;> simp only [compile,hh,Option.bind_eq_bind] at h
      · simp at h
      rename_i head
      cases ht : compile input qs <;> simp [ht] at h
      rename_i tail
      subst r
      change CNFHolds _ (join _ _) ↔ _
      rw [join_correct]
      change (Holds p head a b ∨ Holds p tail a b) ↔ _
      rw [ih ht]
      simp only [List.mem_cons,exists_eq_or_imp,hh,Option.some.injEq,exists_eq_left']

theorem compile_depends {input : Input} {queries : List Query} {r : CNF}
    (h : compile input queries=some r) : Depends input.width r := by
  intro p a b a' b' ha hb
  simp only [compile_correct h]
  apply exists_congr fun q=>and_congr_right fun _=>exists_congr fun rq=>and_congr_right fun hq=>?_
  exact ComparisonSignedEdges.compile_depends hq p a b a' b' ha hb

theorem compile_contrapose {input : Input} {queries : List Query} {r : CNF}
    (h : compile input queries=some r) (p : Nat → Bool) {a b : Nat → Bool}
    (hr : Holds p r a b) : Holds p r (toggle 0 b) (toggle 0 a) := by
  obtain ⟨q,hq,rq,hrq,he⟩ := (compile_correct h p a b).mp hr
  exact (compile_correct h p _ _).mpr
    ⟨q,hq,rq,hrq,ComparisonSignedEdges.compile_contrapose hrq p a b he⟩

theorem model_valid {input : Input} {queries : List Query} {r : CNF}
    (h : compile input queries=some r) (p : Nat → Bool)
    {model : Point input.width → Bool}
    (hm : (input.graph (compile_depends h) p (compile_contrapose h p)).Model model) :
    ∀q∈queries,q.Valid p (fun name a=>model (restrict input.width
      (tuple (input.key name) (input.bases name).length true a))) := by
  intro q hq
  obtain ⟨rq,hrq⟩ := compile_spec h q hq
  apply input.compiled_model_valid hrq p
  constructor
  · exact hm.complement
  · intro a b he
    apply hm.edge
    rcases (input.edges_correct rq p (expand a) (expand b)).mp he with he|he
    · exact (input.edges_correct r p _ _).mpr (.inl
        ((compile_correct h p _ _).mpr ⟨q,hq,rq,hrq,he⟩))
    · exact (input.edges_correct r p _ _).mpr (.inr he)

theorem consistent_iff {input : Input} {queries : List Query} {r : CNF}
    (h : compile input queries=some r) (ha : ∀q∈queries,q.Allowed input.keys)
    (p : Nat → Bool) :
    Holds p (input.consistent r) (fun _=>false) (fun _=>false) ↔
      ∃images,Family input images ∧ ∀q∈queries,q.Valid p images := by
  have hd := compile_depends h
  have hc : ∀{a b},Holds p r a b → Holds p r (toggle 0 b) (toggle 0 a) :=
    fun {_ _} he=>compile_contrapose h p he
  constructor
  · intro hcons
    obtain ⟨model,hm⟩ := (closure_consistent_iff ⟨0,input.width_pos⟩
      (input.edges_depends hd) p
        (fun {_ _} h=>finite_contrapose input.width_pos (input.edges_depends hd) p
          (input.edges_contrapose p hc) h) _ _).mp hcons
    exact ⟨_,input.graph_family hd p hc hm,model_valid h p hm⟩
  · rintro ⟨images,hf,hv⟩
    apply hf.consistent hd p hc
    intro a b he
    obtain ⟨q,hq,rq,hrq,he⟩ := (compile_correct h p a b).mp he
    apply (compile_valid_iff hrq p (input.readValue_complement images)
      (fun hs=>hf.readValue_congr hs)).mpr ?_ a b he
    intro w hw c hcm
    rcases hv q hq w hw c hcm with hg|⟨literal,hl,hvalue⟩
    · exact .inl hg
    · right
      refine ⟨literal,hl,?_⟩
      dsimp only
      rw [callValue_tuple,hf.readValue_tuple (ha q hq c hcm literal hl)]
      exact hvalue

/-- The same executable canonical family satisfies every query, even when
queries use unrelated local observer encodings. -/
theorem imageValue_valid {input : Input} {queries : List Query} {r : CNF}
    (h : compile input queries=some r) (ha : ∀q∈queries,q.Allowed input.keys)
    (p : Nat → Bool)
    (hcons : Holds p (input.consistent r) (fun _=>false) (fun _=>false)) :
    Family input (input.imageValue r p) ∧ ∀q∈queries,q.Valid p (input.imageValue r p) := by
  have hd := compile_depends h
  have hc : ∀{a b},Holds p r a b → Holds p r (toggle 0 b) (toggle 0 a) :=
    fun {_ _} he=>compile_contrapose h p he
  let g := input.graph hd p hc
  let model := @ComparisonSignedGraph.Graph.canonical _ inferInstance (pointOrder input.width) g
  have hg : g.Consistent :=
    (consistent_graph ⟨0,input.width_pos⟩ g (fun _=>rfl) p
      (input.reached r) (closure_correct (input.edges_depends hd) p) _ _).mp hcons
  have hm : g.Model model := @ComparisonSignedGraph.Graph.canonical_model _ inferInstance
    (pointOrder input.width) g hg
  have hf : ∀a,Holds p (input.assignment r) a (fun _=>false) ↔
      model (restrict input.width a)=true :=
    fun a=>assignment_canonical ⟨0,input.width_pos⟩ g (fun _=>rfl) p
      (input.reached r) (closure_correct (input.edges_depends hd) p) a (fun _=>false)
  have he (name : Nat) (hn : name∈input.keys) (a : Nat → Bool) :
      input.imageValue r p name a=model (restrict input.width
        (tuple (input.key name) (input.bases name).length true a)) := by
    apply Bool.eq_iff_iff.mpr
    exact (polynomialValue_correct _ _).trans (polynomial_model g p _ _ _
      (input.graph_polynomialEdges hd p hc hn) hm hf a)
  have hfamily := input.graph_family hd p hc hm
  constructor
  · constructor
    · intro name hn a b hab
      rw [he name hn a,he name hn b]
      exact hfamily.monotone name hn a b hab
    · intro name hn
      rw [he name hn]
      exact hfamily.zero name hn
    · intro name hn
      rw [he name hn]
      exact hfamily.one name hn
  · intro q hq w hw c hcm
    rcases model_valid h p hm q hq w hw c hcm with hg|⟨literal,hl,hvalue⟩
    · exact .inl hg
    · right
      refine ⟨literal,hl,?_⟩
      dsimp only
      rw [he literal.1.name (ha q hq c hcm literal hl)]
      exact hvalue

theorem reconstruct_complete {input : Input} {queries : List Query} {r : CNF}
    (h : compile input queries=some r) (p : Nat → Bool)
    (hcons : Holds p (input.consistent r) (fun _=>false) (fun _=>false)) :
    ∃images,input.reconstruct r p=some images :=
  input.reconstruct_complete (compile_depends h) p (compile_contrapose h p) hcons

end ModalityInference.ComparisonSignedQueries
