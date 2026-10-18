import ModalityInference.Proofs.ComparisonSignedEdgeProjection
import ModalityInference.Proofs.ComparisonSignedPolynomials

/-! Exact compilation of guarded endpoint clauses into a common signed graph.
The same tuple assignment serves every occurrence, while existential observer
worlds remain coupled to their guard and endpoint payload equalities. -/
namespace ModalityInference.ComparisonSignedEdges
open ComparisonPropagation ComparisonSignedRelations ComparisonSignedEndpoints
open ComparisonSignedCanonical

variable {payload : Call → Nat → Nat}

def callValueWith (payload : Call → Nat → Nat) (key : Nat → List Bool) (size : Nat → Nat) (world : Nat → Bool)
    (call : Call) (sign : Bool) : Nat → Bool :=
  patternValue world (patternWith payload key size call sign)

/-- An edge instance keeps its endpoint values in the same observer world as
its active guard and declared-bound theory. -/
def ClauseEdgeWith (payload : Call → Nat → Nat) (width : Nat) (key : Nat → List Bool) (size : Nat → Nat)
    (world : Nat → Bool) (literals : List (Call × Bool)) (a b : Nat → Bool) : Prop :=
  match literals with
  | [] => Same width (toggle 0 a) b
  | [(x,p)] => Same width a (callValueWith payload key size world x (!p)) ∧
      Same width b (callValueWith payload key size world x p)
  | [(x,p),(y,q)] =>
      (Same width a (callValueWith payload key size world x (!p)) ∧
       Same width b (callValueWith payload key size world y q)) ∨
      (Same width a (callValueWith payload key size world y (!q)) ∧
       Same width b (callValueWith payload key size world x p))
  | _ => False

theorem clause_complete {width key size decode theory c}
    (hc : c.literals.length≤2) : ∃result,clauseWith payload width key size decode theory c=some result := by
  obtain ⟨guard,ls⟩ := c
  cases ls with
  | nil => exact ⟨_,rfl⟩
  | cons x xs =>
    rcases x with ⟨x,p⟩
    cases xs with
    | nil => exact ⟨_,rfl⟩
    | cons y ys =>
      rcases y with ⟨y,q⟩
      cases ys with
      | nil => exact ⟨_,rfl⟩
      | cons z zs => simp at hc

theorem clause_correct {width key size decode theory c result}
    (hc : clauseWith payload width key size decode theory c=some result) (p a b : Nat → Bool) :
    Holds p result a b ↔ ∃w,CNFHolds (decoded decode p w) theory ∧
      ¬ClauseHolds (decoded decode p w) c.guard ∧
      ClauseEdgeWith payload width key size (decoded decode p w) c.literals a b := by
  obtain ⟨guard,ls⟩ := c
  cases ls with
  | nil =>
    simp only [clauseWith,Option.some.injEq] at hc
    subst result
    rw [guarded_correct]
    apply exists_congr fun w=>and_congr_right fun _=>and_congr_right fun _=>?_
    rw [rename_correct]
    simp only [Function.comp_def,extended_tuple]
    change Holds p (flip 0 0 (diagonal width)) a b ↔ _
    rw [flip_input_correct,ComparisonSignedRelations.diagonal_correct]
    rfl
  | cons x xs =>
    rcases x with ⟨x,s⟩
    cases xs with
    | nil =>
      simp only [clauseWith,Option.some.injEq] at hc
      subst result
      rw [guarded_correct]
      apply exists_congr fun w=>and_congr_right fun _=>and_congr_right fun _=>?_
      exact directed_correct width decode _ _ p a b w
    | cons y ys =>
      rcases y with ⟨y,t⟩
      cases ys with
      | nil =>
        simp only [clauseWith,Option.some.injEq] at hc
        subst result
        change CNFHolds _ (join _ _) ↔ _
        rw [join_correct]
        change (Holds p (guarded _ _ _ _) a b ∨ Holds p (guarded _ _ _ _) a b) ↔ _
        simp only [guarded_correct,directed_correct,ClauseEdgeWith,callValueWith,
          and_or_left,exists_or]
      | cons z zs => simp [clauseWith] at hc

theorem compile_complete {width key size decode theory clauses}
    (hb : ∀c∈clauses,c.literals.length≤2) :
    ∃result,compileWith payload width key size decode theory clauses=some result := by
  induction clauses with
  | nil => exact ⟨_,rfl⟩
  | cons c cs ih =>
    obtain ⟨head,hh⟩ := clause_complete (payload:=payload) (width:=width) (key:=key) (size:=size)
      (decode:=decode) (theory:=theory) (hb c List.mem_cons_self)
    obtain ⟨tail,ht⟩ := ih (fun c hc=>hb c (List.mem_cons_of_mem _ hc))
    exact ⟨join head tail,by simp [compileWith,hh,ht]⟩

theorem compile_correct {width key size decode theory clauses result}
    (hc : compileWith payload width key size decode theory clauses=some result) (p a b : Nat → Bool) :
    Holds p result a b ↔ ∃c∈clauses,∃w,CNFHolds (decoded decode p w) theory ∧
      ¬ClauseHolds (decoded decode p w) c.guard ∧
      ClauseEdgeWith payload width key size (decoded decode p w) c.literals a b := by
  induction clauses generalizing result with
  | nil =>
    simp only [compileWith,Option.some.injEq] at hc
    subst result
    simp [Holds,CNFHolds,ClauseHolds]
  | cons c cs ih =>
    cases hh : clauseWith payload width key size decode theory c <;> simp only [compileWith,hh,Option.bind_eq_bind] at hc
    · simp at hc
    rename_i head
    cases ht : compileWith payload width key size decode theory cs <;> simp [ht] at hc
    rename_i tail
    subst result
    change CNFHolds _ (join _ _) ↔ _
    rw [join_correct]
    change (Holds p head a b ∨ Holds p tail a b) ↔ _
    rw [clause_correct hh,ih ht]
    simp only [List.mem_cons,exists_eq_or_imp]

theorem prepare_complete (width : Nat) (key : Nat → List Bool) (size : Nat → Nat)
    (decode : Nat → Sum Nat Nat) (theory : CNF) (keys : List Nat)
    (layout : ComparisonStructuralLayout.Layout) (modes : ModVar → ModExpr) (left right : Ty) :
    ∃threshold result,∀fuel≥threshold,
      prepareWith payload fuel width key size decode theory keys layout modes left right=.success result := by
  obtain ⟨threshold,clauses,hc⟩ := compileGuards_complete
    (ComparisonSignedEndpoints.compile keys (ComparisonSignedObservation.context layout modes) left right)
  obtain ⟨result,hr⟩ := compile_complete (payload:=payload) (width:=width) (key:=key) (size:=size)
    (decode:=decode) (theory:=theory) (fun c hm=>compiled_binary (hc threshold le_rfl) hm)
  refine ⟨threshold,result,?_⟩
  intro fuel hf
  simp [prepareWith,hc fuel hf,hr,bind,pure,RunResult.bind]


theorem callValue_flip (key : Nat → List Bool) (size : Nat → Nat)
    (world : Nat → Bool) (call : Call) (sign : Bool) :
    toggle 0 (callValueWith payload key size world call sign)=callValueWith payload key size world call (!sign) := by
  funext i
  cases i with
  | zero => simp [toggle,callValueWith,patternValue,patternWith]
  | succ i => simp [toggle,callValueWith,patternValue,patternWith]

private theorem same_refl (width : Nat) (a : Nat → Bool) : Same width a a := fun _ _=>rfl
private theorem same_symm {width a b} (h : Same width a b) : Same width b a := fun i hi=>(h i hi).symm
private theorem same_toggle {width a b} (h : Same width a b) :
    Same width (toggle 0 a) (toggle 0 b) := by
  intro i hi
  by_cases h0 : i=0
  · simpa only [toggle,if_pos h0] using congrArg Bool.not (h i hi)
  · simpa only [toggle,if_neg h0] using h i hi

private theorem same_congr {width a b a' b'} (ha : Same width a a') (hb : Same width b b') :
    Same width a b ↔ Same width a' b' := by
  apply forall_congr' fun i=>imp_congr_right fun hi=>?_
  rw [ha i hi,hb i hi]

theorem clauseEdge_contrapose {width key size world literals a b}
    (h : ClauseEdgeWith payload width key size world literals a b) :
    ClauseEdgeWith payload width key size world literals (toggle 0 b) (toggle 0 a) := by
  cases literals with
  | nil => simpa only [ClauseEdgeWith,toggle_toggle] using same_symm h
  | cons x xs =>
    rcases x with ⟨x,p⟩
    cases xs with
    | nil =>
      obtain ⟨ha,hb⟩ := h
      constructor
      · simpa only [callValue_flip] using same_toggle hb
      · simpa only [callValue_flip,Bool.not_not] using same_toggle ha
    | cons y ys =>
      rcases y with ⟨y,q⟩
      cases ys with
      | nil =>
        rcases h with ⟨ha,hb⟩|⟨ha,hb⟩
        · right
          exact ⟨by simpa only [callValue_flip] using same_toggle hb,
            by simpa only [callValue_flip,Bool.not_not] using same_toggle ha⟩
        · left
          exact ⟨by simpa only [callValue_flip] using same_toggle hb,
            by simpa only [callValue_flip,Bool.not_not] using same_toggle ha⟩
      | cons z zs => exact False.elim h

theorem clauseEdge_congr {width key size world literals a b a' b'}
    (ha : Same width a a') (hb : Same width b b') :
    ClauseEdgeWith payload width key size world literals a b ↔ ClauseEdgeWith payload width key size world literals a' b' := by
  have hi (x : Nat → Bool) := same_congr ha (same_refl width x)
  have ho (x : Nat → Bool) := same_congr hb (same_refl width x)
  cases literals with
  | nil => exact same_congr (same_toggle ha) hb
  | cons x xs =>
    rcases x with ⟨x,p⟩
    cases xs with
    | nil => exact and_congr (hi _) (ho _)
    | cons y ys =>
      rcases y with ⟨y,q⟩
      cases ys with
      | nil => exact or_congr (and_congr (hi _) (ho _)) (and_congr (hi _) (ho _))
      | cons z zs => rfl

theorem compile_depends {width key size decode theory clauses result}
    (h : compileWith payload width key size decode theory clauses=some result) : Depends width result := by
  intro p a b a' b' ha hb
  rw [compile_correct h,compile_correct h]
  apply exists_congr fun c=>and_congr_right fun _=>exists_congr fun w=>
    and_congr_right fun _=>and_congr_right fun _=>clauseEdge_congr ha hb

/-- Contraposition is guaranteed by the concrete signed-edge compiler. -/
theorem compile_contrapose {width key size decode theory clauses result}
    (h : compileWith payload width key size decode theory clauses=some result) (p a b : Nat → Bool)
    (hr : Holds p result a b) : Holds p result (toggle 0 b) (toggle 0 a) := by
  obtain ⟨c,hc,w,hw,hg,he⟩ := (compile_correct h p a b).mp hr
  exact (compile_correct h p _ _).mpr ⟨c,hc,w,hw,hg,clauseEdge_contrapose he⟩


theorem clause_binary {width key size decode theory c result}
    (hc : clauseWith payload width key size decode theory c=some result) : c.literals.length≤2 := by
  obtain ⟨guard,ls⟩ := c
  cases ls with
  | nil => simp
  | cons x xs =>
    rcases x with ⟨x,p⟩
    cases xs with
    | nil => simp
    | cons y ys =>
      rcases y with ⟨y,q⟩
      cases ys with
      | nil => simp
      | cons z zs => simp [clauseWith] at hc

theorem compile_binary {width key size decode theory clauses result}
    (h : compileWith payload width key size decode theory clauses=some result) :
    ∀c∈clauses,c.literals.length≤2 := by
  induction clauses generalizing result with
  | nil => simp
  | cons c cs ih =>
    cases hh : clauseWith payload width key size decode theory c <;> simp only [compileWith,hh,Option.bind_eq_bind] at h
    · simp at h
    rename_i head
    cases ht : compileWith payload width key size decode theory cs <;> simp [ht] at h
    intro d hd
    rcases List.mem_cons.mp hd with rfl|hd
    · exact clause_binary hh
    · exact ih ht d hd

theorem callValue_read {key size world call sign} {value : (Nat → Bool) → Bool}
    (hn : ∀a,value (toggle 0 a)=!value a) :
    value (callValueWith payload key size world call sign)=true ↔
      value (callValueWith payload key size world call true)=sign := by
  cases sign with
  | false =>
    have he := hn (callValueWith payload key size world call true)
    rw [callValue_flip] at he
    simp only [Bool.not_true] at he
    rw [he]
    simp
  | true => rfl

/-- A signed assignment satisfies a finite clause exactly when it respects all
of that clause's directed edges. -/
theorem clauseEdge_valid {width key size world literals} {value : (Nat → Bool) → Bool}
    (hn : ∀a,value (toggle 0 a)=!value a)
    (hb : literals.length≤2)
    (he : ∀a b,ClauseEdgeWith payload width key size world literals a b → value a≤value b) :
    ∃l∈literals,value (callValueWith payload key size world l.1 true)=l.2 := by
  cases literals with
  | nil =>
    let a : Nat → Bool := fun _=>false
    have h₁ := he a (toggle 0 a) (same_refl width _)
    have h₂ := he (toggle 0 a) a (by simpa only [ClauseEdgeWith,toggle_toggle] using same_refl width a)
    rw [hn] at h₁ h₂
    cases hv : value a <;> simp_all [Bool.le_iff_imp]
  | cons x xs =>
    rcases x with ⟨x,p⟩
    cases xs with
    | nil =>
      have hp := he (callValueWith payload key size world x (!p)) (callValueWith payload key size world x p)
        ⟨same_refl width _,same_refl width _⟩
      have hflip : value (callValueWith payload key size world x (!p))= !value (callValueWith payload key size world x p) := by
        rw [←callValue_flip,hn]
      rw [hflip] at hp
      have hx : value (callValueWith payload key size world x p)=true := by cases hv : value _ <;> simp_all [Bool.le_iff_imp]
      exact ⟨(x,p),List.mem_cons_self,(callValue_read hn).mp hx⟩
    | cons y ys =>
      rcases y with ⟨y,q⟩
      cases ys with
      | nil =>
        by_cases hx : value (callValueWith payload key size world x p)=true
        · exact ⟨(x,p),List.mem_cons_self,(callValue_read hn).mp hx⟩
        · have hne : value (callValueWith payload key size world x (!p))=true := by
            rw [←callValue_flip,hn,Bool.eq_false_iff.mpr hx]
            rfl
          have hy := Bool.le_iff_imp.mp (he (callValueWith payload key size world x (!p))
            (callValueWith payload key size world y q) (.inl ⟨same_refl width _,same_refl width _⟩)) hne
          exact ⟨(y,q),by simp,(callValue_read hn).mp hy⟩
      | cons z zs => simp at hb

theorem clauseEdge_respects {width key size world literals} {value : (Nat → Bool) → Bool}
    (hn : ∀a,value (toggle 0 a)=!value a)
    (hs : ∀{a b},Same width a b → value a=value b)
    (hv : ∃l∈literals,value (callValueWith payload key size world l.1 true)=l.2)
    {a b} (he : ClauseEdgeWith payload width key size world literals a b) : value a≤value b := by
  have transfer {x p y q a b}
      (ha : Same width a (callValueWith payload key size world x (!p)))
      (hb : Same width b (callValueWith payload key size world y q))
      (hv : value (callValueWith payload key size world x true)=p ∨ value (callValueWith payload key size world y true)=q) :
      value a≤value b := by
    rw [hs ha,hs hb]
    rcases hv with hv|hv
    · have hp := (callValue_read hn).mpr hv
      have hf := hn (callValueWith payload key size world x p)
      rw [callValue_flip,hp] at hf
      rw [hf]
      exact Bool.false_le _
    · have hq := (callValue_read hn).mpr hv
      rw [hq]
      exact Bool.le_true _
  cases literals with
  | nil => simp at hv
  | cons x xs =>
    rcases x with ⟨x,p⟩
    cases xs with
    | nil =>
      obtain ⟨l,hl,hv⟩ := hv
      have hl : l=(x,p) := by simpa using hl
      subst l
      exact transfer he.1 he.2 (.inl hv)
    | cons y ys =>
      rcases y with ⟨y,q⟩
      cases ys with
      | nil =>
        have hv : value (callValueWith payload key size world x true)=p ∨ value (callValueWith payload key size world y true)=q := by
          obtain ⟨l,hl,hv⟩ := hv
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
          rcases hl with rfl|rfl
          · exact .inl hv
          · exact .inr hv
        rcases he with ⟨ha,hb⟩|⟨ha,hb⟩
        · exact transfer ha hb hv
        · exact transfer ha hb hv.symm
      | cons z zs => exact False.elim he

theorem compile_valid_iff {width key size decode theory clauses result}
    (h : compileWith payload width key size decode theory clauses=some result) (p : Nat → Bool)
    {value : (Nat → Bool) → Bool}
    (hn : ∀a,value (toggle 0 a)=!value a)
    (hs : ∀{a b},Same width a b → value a=value b) :
    (∀a b,Holds p result a b → value a≤value b) ↔
      ∀w,CNFHolds (decoded decode p w) theory → ∀c∈clauses,
        c.Holds (decoded decode p w) (fun call=>value (callValueWith payload key size (decoded decode p w) call true)) := by
  constructor
  · intro hv w hw c hc
    by_cases hg : ClauseHolds (decoded decode p w) c.guard
    · exact .inl hg
    · right
      exact clauseEdge_valid hn (compile_binary h c hc) (fun a b he=>
        hv a b ((compile_correct h p a b).mpr ⟨c,hc,w,hw,hg,he⟩))
  · intro hv a b he
    obtain ⟨c,hc,w,hw,hg,he⟩ := (compile_correct h p a b).mp he
    exact clauseEdge_respects hn hs ((hv w hw c hc).resolve_left hg) he


theorem compile_finite_contrapose {width key size decode theory clauses result}
    (hw : 0<width) (h : compileWith payload width key size decode theory clauses=some result)
    (p : Nat → Bool) {a b : Point width} (he : relation width p result a b) :
    relation width p result (complement ⟨0,hw⟩ b) (complement ⟨0,hw⟩ a) := by
  have he := compile_contrapose h p (expand a) (expand b) he
  apply (compile_depends h p _ _ _ _ ?_ ?_).mp he
  all_goals intro i hi
  all_goals simp [toggle,expand,hi,complement,Fin.ext_iff]

/-- The graph is obtained from the actual compiled relation. Its complement law
is a derived property of symmetric clause-edge generation. -/
def compiledGraph {width key size decode theory clauses result}
    (hw : 0<width) (h : compileWith payload width key size decode theory clauses=some result)
    (p : Nat → Bool) : ComparisonSignedGraph.Graph (Point width) :=
  ComparisonSignedCanonical.graph ⟨0,hw⟩ p result (compile_finite_contrapose hw h p)

private theorem restrict_same {width a b} (h : Same width a b) :
    restrict width a=restrict width b := by
  funext i
  exact h i i.isLt

theorem compiledGraph_model_iff {width key size decode theory clauses result}
    (hw : 0<width) (h : compileWith payload width key size decode theory clauses=some result)
    (p : Nat → Bool) (value : Point width → Bool) :
    (compiledGraph hw h p).Model value ↔
      (∀a,value (complement ⟨0,hw⟩ a)=!value a) ∧
      ∀w,CNFHolds (decoded decode p w) theory → ∀c∈clauses,
        c.Holds (decoded decode p w) (fun call=>
          value (restrict width (callValueWith payload key size (decoded decode p w) call true))) := by
  let values := fun a=>value (restrict width a)
  have hs : ∀{a b},Same width a b → values a=values b :=
    fun h=>congrArg value (restrict_same h)
  constructor
  · intro hm
    have hn : ∀a,values (toggle 0 a)=!values a := by
      intro a
      change value (restrict width (toggle (⟨0,hw⟩ : Fin width) a))= !value (restrict width a)
      rw [restrict_toggle]
      exact hm.complement (restrict width a)
    refine ⟨hm.complement,(compile_valid_iff h p hn hs).mp ?_⟩
    intro a b he
    apply hm.edge
    exact (compile_depends h p a b (expand (restrict width a)) (expand (restrict width b))
      (expand_restrict width a) (expand_restrict width b)).mp he
  · rintro ⟨hn,hv⟩
    have hnv : ∀a,values (toggle 0 a)=!values a := by
      intro a
      change value (restrict width (toggle (⟨0,hw⟩ : Fin width) a))= !value (restrict width a)
      rw [restrict_toggle]
      exact hn (restrict width a)
    refine ⟨hn,?_⟩
    intro a b he
    have hh := (compile_valid_iff h p hnv hs).mpr hv (expand a) (expand b) he
    simpa only [values,restrict_expand] using hh

/-- Feasibility of the compiled signed closure is equivalent to one assignment
for all endpoint occurrences and all admissible observer worlds. -/
theorem compile_feasible_iff {width key size decode theory clauses result}
    (hw : 0<width) (h : compileWith payload width key size decode theory clauses=some result)
    (p a b : Nat → Bool) :
    Holds p (consistent 0 (closure width result)) a b ↔
      ∃value : Point width → Bool,
        (∀a,value (complement ⟨0,hw⟩ a)=!value a) ∧
        ∀w,CNFHolds (decoded decode p w) theory → ∀c∈clauses,
          c.Holds (decoded decode p w) (fun call=>
            value (restrict width (callValueWith payload key size (decoded decode p w) call true))) := by
  rw [consistent_iff_model ⟨0,hw⟩ (compiledGraph hw h p) (fun _=>rfl) p
    (closure width result) (closure_correct (compile_depends h) p)]
  exact exists_congr fun value=>compiledGraph_model_iff hw h p value


theorem prepare_spec {fuel width key size decode theory keys layout modes left right result}
    (h : prepareWith payload fuel width key size decode theory keys layout modes left right=.success result) :
    ∃clauses,
      compileGuards fuel (ComparisonSignedEndpoints.compile keys
        (ComparisonSignedObservation.context layout modes) left right)=.success clauses ∧
      compileWith payload width key size decode theory clauses=some result := by
  cases hc : compileGuards fuel (ComparisonSignedEndpoints.compile keys
    (ComparisonSignedObservation.context layout modes) left right) <;>
    simp [prepareWith,hc,bind,RunResult.bind] at h
  rename_i clauses
  cases hr : compileWith payload width key size decode theory clauses <;> simp [hr,pure] at h
  subst result
  exact ⟨clauses,rfl,hr⟩

/-- The concrete relation compiler is exact for the original public endpoint
syntax and one common modality substitution, before algebraic interpretation. -/
theorem prepare_valid_iff {fuel width key size decode theory keys layout modes left right result}
    (h : prepareWith payload fuel width key size decode theory keys layout modes left right=.success result)
    (p : Nat → Bool) {value : (Nat → Bool) → Bool}
    (hn : ∀a,value (toggle 0 a)=!value a)
    (hs : ∀{a b},Same width a b → value a=value b) :
    (∀a b,Holds p result a b → value a≤value b) ↔
      ∀w,CNFHolds (decoded decode p w) theory →
        interpret keys (ComparisonSignedObservation.context layout modes) (decoded decode p w)
          (fun call=>value (callValueWith payload key size (decoded decode p w) call true)) [] left=true →
        interpret keys (ComparisonSignedObservation.context layout modes) (decoded decode p w)
          (fun call=>value (callValueWith payload key size (decoded decode p w) call true)) [] right=true := by
  obtain ⟨clauses,hc,hr⟩ := prepare_spec h
  rw [compile_valid_iff hr p hn hs]
  apply forall_congr' fun w=>imp_congr_right fun _=>?_
  rw [compileGuards_correct hc,ComparisonSignedEndpoints.compile_correct]


/-- Endpoint calls use exactly the tuple convention of polynomial reconstruction. -/
theorem callValue_tuple (key : Nat → List Bool) (size : Nat → Nat)
    (world : Nat → Bool) (call : Call) (sign : Bool) :
    callValueWith payload key size world call sign=
      ComparisonSignedPolynomials.tuple (key call.name) (size call.name) sign
        (fun i=>world (payload call i)) := by
  funext i
  by_cases hk : i<(key call.name).length+1
  · have hk' : i<(sign::key call.name).length := hk
    simp only [callValueWith,patternValue,patternWith,ComparisonSignedPolynomials.tuple,
      List.getElem?_append,List.length_map,List.length_cons,hk,if_true,List.getElem?_map,
      List.getElem?_eq_getElem hk',Option.map_some,Option.getD_some]
  · by_cases hi : i<(key call.name).length+1+size call.name
    · have hr : i-((key call.name).length+1)<size call.name := by omega
      simp only [callValueWith,patternValue,patternWith,ComparisonSignedPolynomials.tuple,
        List.getElem?_append,List.length_map,List.length_cons,hk,if_false,hi,if_true,
        List.getElem?_map,List.getElem?_range hr,Option.map_some,Option.getD_some]
    · have hr : (List.range (size call.name)).length≤i-((key call.name).length+1) := by
        simp only [List.length_range]
        omega
      simp only [callValueWith,patternValue,patternWith,ComparisonSignedPolynomials.tuple,
        List.getElem?_append,List.length_map,List.length_cons,hk,if_false,hi,
        List.getElem?_map,List.getElem?_eq_none hr,Option.map_none,Option.getD_none]

abbrev callValue := callValueWith routePayload
abbrev ClauseEdge := ClauseEdgeWith routePayload

end ModalityInference.ComparisonSignedEdges
