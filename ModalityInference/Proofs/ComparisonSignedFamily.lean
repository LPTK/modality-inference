import ModalityInference.Proofs.ComparisonSignedSynthesis
import ModalityInference.Proofs.ComparisonSignedEdges

namespace ModalityInference.ComparisonSignedSynthesis
open ComparisonPropagation ComparisonSignedRelations ComparisonSignedPolynomials
open ComparisonSignedEndpoints ComparisonSignedEdges ComparisonSignedCanonical

variable {payload : Call → Nat → Nat}

def Input.graph (input : Input) {r : CNF} (hd : Depends input.width r) (p : Nat → Bool)
    (hc : ∀{a b},Holds p r a b → Holds p r (toggle 0 b) (toggle 0 a)) :
    ComparisonSignedGraph.Graph (Point input.width) :=
  ComparisonSignedCanonical.graph ⟨0,input.width_pos⟩ p (input.edges r)
    (fun {_ _} h=>finite_contrapose input.width_pos (input.edges_depends hd) p
      (input.edges_contrapose p hc) h)

theorem Input.graph_polynomialEdges (input : Input) {r : CNF} (hd : Depends input.width r)
    (p : Nat → Bool) (hc : ∀{a b},Holds p r a b → Holds p r (toggle 0 b) (toggle 0 a))
    {name : Nat} (hn : name∈input.keys) (a b : Nat → Bool)
    (he : Holds p (ComparisonSignedPolynomials.edges (input.key name) (input.bases name).length) a b) :
    (input.graph hd p hc).edge (restrict input.width a) (restrict input.width b) := by
  exact (input.edges_depends hd p a b _ _ (expand_restrict input.width a)
    (expand_restrict input.width b)).mp ((input.edges_correct r p a b).mpr (.inr ⟨name,hn,he⟩))

theorem Input.graph_family (input : Input) {r : CNF} (hd : Depends input.width r)
    (p : Nat → Bool) (hc : ∀{a b},Holds p r a b → Holds p r (toggle 0 b) (toggle 0 a))
    {model : Point input.width → Bool} (hm : (input.graph hd p hc).Model model) :
    Family input (fun name a=>model (restrict input.width
      (tuple (input.key name) (input.bases name).length true a))) where
  monotone := by
    intro name hn a b hab
    exact model_monotone (input.graph hd p hc) p _ _
      (input.graph_polynomialEdges hd p hc hn) hm a b hab
  zero := by
    intro name hn
    exact model_boundary input.width_pos (input.graph hd p hc) (fun _=>rfl) p _ _
      (input.graph_polynomialEdges hd p hc hn) hm false
  one := by
    intro name hn
    exact model_boundary input.width_pos (input.graph hd p hc) (fun _=>rfl) p _ _
      (input.graph_polynomialEdges hd p hc hn) hm true

theorem Input.compiled_model_valid (input : Input) {decode theory clauses r}
    (hr : compileWith payload input.width input.key (fun n=>(input.bases n).length)
      decode theory clauses=some r) (p : Nat → Bool)
    {model : Point input.width → Bool}
    (hm : (input.graph (compile_depends hr) p
      (fun {_ _} h=>compile_contrapose hr p _ _ h)).Model model) :
    ∀w,CNFHolds (decoded decode p w) theory → ∀c∈clauses,
      c.Holds (decoded decode p w) (fun call=>model (restrict input.width
        (tuple (input.key call.name) (input.bases call.name).length true
          (fun i=>decoded decode p w (payload call i))))) := by
  let values : (Nat → Bool) → Bool := fun a=>model (restrict input.width a)
  have hn : ∀a,values (toggle 0 a)=!values a := by
    intro a
    change model (restrict input.width (toggle (⟨0,input.width_pos⟩ : Fin input.width) a))= _
    rw [restrict_toggle]
    exact hm.complement _
  have hs : ∀{a b},Same input.width a b → values a=values b := by
    intro a b hab
    apply congrArg model
    funext i
    exact hab i i.isLt
  have hv := (compile_valid_iff hr p hn hs).mp (fun a b he=>hm.edge
    ((input.edges_depends (compile_depends hr) p a b _ _ (expand_restrict input.width a)
      (expand_restrict input.width b)).mp ((input.edges_correct r p a b).mpr (.inl he))))
  simpa only [values,callValue_tuple] using hv

/-- The common normalized graph is feasible precisely when all original guarded
clauses admit one family of finite positive image polynomials. -/
theorem Input.compiled_consistent_iff (input : Input) {decode theory clauses r}
    (hr : compileWith payload input.width input.key (fun n=>(input.bases n).length)
      decode theory clauses=some r)
    (ha : ∀c∈clauses,∀literal∈c.literals,literal.1.name∈input.keys)
    (p : Nat → Bool) :
    Holds p (input.consistent r) (fun _=>false) (fun _=>false) ↔
      ∃images,Family input images ∧
        ∀w,CNFHolds (decoded decode p w) theory → ∀c∈clauses,
          c.Holds (decoded decode p w)
            (fun call=>images call.name (fun i=>decoded decode p w (payload call i))) := by
  have hd := compile_depends hr
  have hc : ∀{a b},Holds p r a b → Holds p r (toggle 0 b) (toggle 0 a) :=
    fun {_ _} h=>compile_contrapose hr p _ _ h
  constructor
  · intro h
    obtain ⟨model,hm⟩ := (closure_consistent_iff ⟨0,input.width_pos⟩
      (input.edges_depends hd) p
        (fun {_ _} h=>finite_contrapose input.width_pos (input.edges_depends hd) p
          (input.edges_contrapose p hc) h) _ _).mp h
    have hm : (input.graph hd p hc).Model model := hm
    refine ⟨fun name a=>model (restrict input.width
      (tuple (input.key name) (input.bases name).length true a)),input.graph_family hd p hc hm,?_⟩
    exact input.compiled_model_valid hr p hm
  · rintro ⟨images,hf,hv⟩
    apply hf.consistent hd p hc
    apply (compile_valid_iff hr p (input.readValue_complement images)
      (fun hs=>hf.readValue_congr hs)).mpr
    intro w hw c hcm
    rcases hv w hw c hcm with hg|⟨literal,hl,hvalue⟩
    · exact .inl hg
    · right
      refine ⟨literal,hl,?_⟩
      dsimp only
      rw [callValue_tuple,hf.readValue_tuple (ha c hcm literal hl)]
      exact hvalue

def Input.imageValue (input : Input) (r : CNF) (p : Nat → Bool)
    (name : Nat) : (Nat → Bool) → Bool :=
  polynomialValue (polynomial p (input.key name) (input.bases name).length (input.assignment r))

theorem Input.reconstruct_value (input : Input) {r : CNF} {p : Nat → Bool}
    {images : List (Nat × CompareTy)} (hr : input.reconstruct r p=some images)
    {image : Nat × CompareTy} (hi : image∈images)
    (value : CompareTy → Bool)
    (hj : ∀a b,value (.join a b)=(value a || value b))
    (hm : ∀a b,value (.meet a b)=(value a && value b)) :
    value image.2=input.imageValue r p image.1 (basisValue (input.bases image.1) value) := by
  apply Bool.eq_iff_iff.mpr
  exact (reify_correct ((input.reconstruct_spec hr).2 image hi) value hj hm).trans
    (polynomialValue_correct _ _).symm

/-- The actual canonical formulas, rather than a separately chosen model,
satisfy all guarded clauses and the positive finite-polynomial laws. -/
theorem Input.compiled_imageValue (input : Input) {decode theory clauses r}
    (hr : compileWith payload input.width input.key (fun n=>(input.bases n).length)
      decode theory clauses=some r)
    (ha : ∀c∈clauses,∀literal∈c.literals,literal.1.name∈input.keys)
    (p : Nat → Bool)
    (h : Holds p (input.consistent r) (fun _=>false) (fun _=>false)) :
    Family input (input.imageValue r p) ∧
      ∀w,CNFHolds (decoded decode p w) theory → ∀c∈clauses,
        c.Holds (decoded decode p w) (fun call=>input.imageValue r p call.name
          (fun i=>decoded decode p w (payload call i))) := by
  have hd := compile_depends hr
  have hc : ∀{a b},Holds p r a b → Holds p r (toggle 0 b) (toggle 0 a) :=
    fun {_ _} h=>compile_contrapose hr p _ _ h
  let g := input.graph hd p hc
  let model := @ComparisonSignedGraph.Graph.canonical _ inferInstance (pointOrder input.width) g
  have hcons : g.Consistent :=
    (consistent_graph ⟨0,input.width_pos⟩ g (fun _=>rfl) p
      (input.reached r) (closure_correct (input.edges_depends hd) p) _ _).mp h
  have hm : g.Model model := @ComparisonSignedGraph.Graph.canonical_model _ inferInstance
    (pointOrder input.width) g hcons
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
  · intro w hw c hcm
    rcases input.compiled_model_valid hr p hm w hw c hcm with hg|⟨literal,hl,hvalue⟩
    · exact .inl hg
    · right
      refine ⟨literal,hl,?_⟩
      dsimp only
      rw [he literal.1.name (ha c hcm literal hl)]
      exact hvalue

end ModalityInference.ComparisonSignedSynthesis
