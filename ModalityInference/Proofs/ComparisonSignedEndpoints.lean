import ModalityInference.ComparisonSignedEndpoints
import ModalityInference.Proofs.CompactCNF

/-! Exact signed binary clauses for public endpoint syntax. Constructor choices
and modality actions are fixed together in one observation context; all image
calls retain their original binder and route. Guard conversion preserves these
calls and introduces no occurrence-specific type images. -/

namespace ModalityInference.ComparisonSignedEndpoints

def Data.eval (world : Nat → Bool) (images : Call → Bool) : Data → Bool
  | .fixed e => e.eval world
  | .image c positive => images c == positive

def View.eval (world : Nat → Bool) (images : Call → Bool) (v : View) : Bool :=
  if v.data.eval world images then v.upper.eval world else v.lower.eval world

def Clause.Holds (world : Nat → Bool) (images : Call → Bool) (c : Clause) : Prop :=
  c.guard.eval world=true ∨ ∃l∈c.literals, images l.1=l.2

@[simp] theorem neg_eval (e : BoolExpr) (world : Nat → Bool) :
    (neg e).eval world= !e.eval world := by simp [neg,BoolExpr.eval]

@[simp] theorem Data.flip_eval (data : Data) (world : Nat → Bool) (images : Call → Bool) :
    data.flip.eval world images= !data.eval world images := by
  cases data with
  | fixed e => exact neg_eval e world
  | image c p => cases p <;> cases hi : images c <;> simp [Data.flip,Data.eval,hi]

@[simp] theorem View.base_eval (data : Data) (world : Nat → Bool) (images : Call → Bool) :
    (View.base data).eval world images=data.eval world images := by
  simp [View.eval,View.base,BoolExpr.eval]

@[simp] theorem View.dual_eval (v : View) (world : Nat → Bool) (images : Call → Bool) :
    v.dual.eval world images= !v.eval world images := by
  cases hd : v.data.eval world images <;> simp [View.eval,View.dual,hd]

@[simp] theorem View.act_eval (v : View) (lower upper : BoolExpr)
    (world : Nat → Bool) (images : Call → Bool) :
    (v.act lower upper).eval world images=
      ((v.eval world images || lower.eval world) && upper.eval world) := by
  cases hd : v.data.eval world images <;> simp [View.eval,View.act,BoolExpr.eval,hd]

private theorem any_eval_true (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any es).eval world=true ↔ ∃e∈es,e.eval world=true := by
  induction es <;> simp_all [BoolExpr.any,BoolExpr.eval]

theorem makeClause_holds (guard : BoolExpr) (data : List Data)
    (world : Nat → Bool) (images : Call → Bool) :
    (makeClause guard data).Holds world images ↔
      guard.eval world=true ∨ ∃d∈data, d.eval world images=true := by
  simp only [makeClause,Clause.Holds,BoolExpr.eval,Bool.or_eq_true,any_eval_true,
    List.mem_filterMap]
  constructor
  · rintro ((hg|⟨e,⟨d,hd,he⟩,hv⟩)|⟨l,⟨d,hd,he⟩,hv⟩)
    · exact Or.inl hg
    · right
      cases d <;> simp only [Option.some.injEq,reduceCtorEq] at he
      subst e
      exact ⟨_,hd,hv⟩
    · right
      cases d <;> simp only [Option.some.injEq,reduceCtorEq] at he
      subst l
      exact ⟨_,hd,by simpa [Data.eval] using hv⟩
  · rintro (hg|⟨d,hd,hv⟩)
    · exact Or.inl (Or.inl hg)
    · cases d with
      | fixed e => exact Or.inl (Or.inr ⟨e,⟨_,hd,rfl⟩,hv⟩)
      | image c p => exact Or.inr ⟨(c,p),⟨_,hd,rfl⟩,by simpa [Data.eval] using hv⟩

theorem compare_correct (active : BoolExpr) (left right : View)
    (world : Nat → Bool) (images : Call → Bool) :
    (∀c∈compare active left right, c.Holds world images) ↔
      active.eval world=true → left.eval world images=true → right.eval world images=true := by
  simp [compare,makeClause_holds,BoolExpr.any,BoolExpr.eval,View.eval]
  cases hl : left.data.eval world images <;> cases hr : right.data.eval world images <;>
    simp_all [Bool.eq_false_iff, -Bool.not_eq_true] <;> tauto

theorem makeClause_length (guard : BoolExpr) (data : List Data) :
    (makeClause guard data).literals.length≤data.length := List.length_filterMap_le _ _

theorem compare_binary {active : BoolExpr} {left right : View} {clause : Clause}
    (h : clause∈compare active left right) : clause.literals.length≤2 := by
  simp only [compare,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl|rfl <;> exact makeClause_length _ _

def interpret (keys : List Nat) (ctx : Context) (world : Nat → Bool)
    (images : Call → Bool) (route : Route) : Ty → Bool
  | .var v => (reference keys ctx route v).eval world images
  | .unit => (ctx.fixed route .unit).eval world
  | .credit => (ctx.fixed route .credit).eval world
  | .prod a b | .sum a b =>
      if (ctx.choose route).eval world then interpret keys ctx world images (route++[false]) a
      else interpret keys ctx world images (route++[true]) b
  | .fn a b =>
      if (ctx.choose route).eval world then !interpret keys ctx world images (route++[false]) a
      else interpret keys ctx world images (route++[true]) b
  | .modal a m => ((interpret keys ctx world images route a ||
      (ctx.action route m).1.eval world) && (ctx.action route m).2.eval world)

def Represents (world : Nat → Bool) (images : Call → Bool)
    (branches : List Branch) (value : Bool) : Prop :=
  (∃b∈branches,b.guard.eval world=true) ∧
    ∀b∈branches,b.guard.eval world=true → b.view.eval world images=value

theorem Represents.base (world : Nat → Bool) (images : Call → Bool) (data : Data) :
    Represents world images [⟨.const true,.base data⟩] (data.eval world images) := by
  simp [Represents,BoolExpr.eval]

theorem Represents.choice {world : Nat → Bool} {images : Call → Bool}
    {left right : List Branch} {a b : Bool} (hl : Represents world images left a)
    (hr : Represents world images right b) (test : BoolExpr) :
    Represents world images (left.map (Branch.guarded test) ++ right.map (Branch.guarded (neg test)))
      (if test.eval world then a else b) := by
  constructor
  · cases ht : test.eval world with
    | false =>
      obtain ⟨branch,hbranch,hactive⟩ := hr.1
      exact ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨branch,hbranch,rfl⟩),
        by simp [Branch.guarded,BoolExpr.eval,ht,hactive]⟩
    | true =>
      obtain ⟨branch,hbranch,hactive⟩ := hl.1
      exact ⟨_,List.mem_append_left _ (List.mem_map.mpr ⟨branch,hbranch,rfl⟩),
        by simp [Branch.guarded,BoolExpr.eval,ht,hactive]⟩
  · intro branch hb hactive
    rcases List.mem_append.mp hb with hb|hb
    · obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hb
      have hh : test.eval world=true ∧ original.guard.eval world=true := by
        simpa [Branch.guarded,BoolExpr.eval] using hactive
      obtain ⟨ht,hactive⟩ := hh
      simpa [Branch.guarded,ht] using hl.2 original ho hactive
    · obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hb
      have hh : test.eval world=false ∧ original.guard.eval world=true := by
        simpa [Branch.guarded,BoolExpr.eval] using hactive
      obtain ⟨ht,hactive⟩ := hh
      have ht' : test.eval world=false := by simpa using ht
      simpa [Branch.guarded,ht'] using hr.2 original ho hactive

theorem Represents.dual {world : Nat → Bool} {images : Call → Bool}
    {branches : List Branch} {a : Bool} (h : Represents world images branches a) :
    Represents world images (branches.map fun b=>⟨b.guard,b.view.dual⟩) (!a) := by
  constructor
  · obtain ⟨b,hb,ha⟩ := h.1
    exact ⟨_,List.mem_map.mpr ⟨b,hb,rfl⟩,ha⟩
  · intro b hb ha
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hb
    simpa using congrArg Bool.not (h.2 original ho ha)

theorem Represents.act {world : Nat → Bool} {images : Call → Bool}
    {branches : List Branch} {a : Bool} (h : Represents world images branches a)
    (lower upper : BoolExpr) :
    Represents world images (branches.map fun b=>⟨b.guard,b.view.act lower upper⟩)
      ((a || lower.eval world) && upper.eval world) := by
  constructor
  · obtain ⟨b,hb,ha⟩ := h.1
    exact ⟨_,List.mem_map.mpr ⟨b,hb,rfl⟩,ha⟩
  · intro b hb ha
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hb
    simpa using congrArg (fun x=>(x || lower.eval world) && upper.eval world) (h.2 original ho ha)

theorem observe_correct (keys : List Nat) (ctx : Context) (world : Nat → Bool)
    (images : Call → Bool) (route : Route) (a : Ty) :
    Represents world images (observe keys ctx route a) (interpret keys ctx world images route a) := by
  induction a generalizing route with
  | var v => exact Represents.base world images _
  | unit => exact Represents.base world images _
  | credit => exact Represents.base world images _
  | prod a b iha ihb | sum a b iha ihb =>
    exact Represents.choice (iha _) (ihb _) _
  | fn a b iha ihb =>
    simpa only [observe,interpret,List.map_map,Function.comp_def] using
      Represents.choice (iha _).dual (ihb _) (ctx.choose route)
  | modal a m ih => exact (ih route).act _ _

theorem compile_correct (keys : List Nat) (ctx : Context) (left right : Ty)
    (world : Nat → Bool) (images : Call → Bool) :
    (∀clause∈compile keys ctx left right,clause.Holds world images) ↔
      interpret keys ctx world images [] left=true → interpret keys ctx world images [] right=true := by
  simp only [compile,List.forall_mem_flatMap,compare_correct,BoolExpr.eval,Bool.and_eq_true]
  have hl := observe_correct keys ctx world images [] left
  have hr := observe_correct keys ctx world images [] right
  constructor
  · intro h hleft
    obtain ⟨l,hll,hla⟩ := hl.1
    obtain ⟨r,hrr,hra⟩ := hr.1
    have hh := h l hll r hrr ⟨hla,hra⟩
    rw [hl.2 l hll hla,hr.2 r hrr hra] at hh
    exact hh hleft
  · intro h l hll r hrr ha
    rw [hl.2 l hll ha.1,hr.2 r hrr ha.2]
    exact h

theorem compile_binary {keys : List Nat} {ctx : Context} {left right : Ty} {clause : Clause}
    (h : clause∈compile keys ctx left right) : clause.literals.length≤2 := by
  obtain ⟨l,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨r,_,h⟩ := List.mem_flatMap.mp h
  exact compare_binary h

/-- Every occurrence of an image is evaluated by the same original family;
only the observer argument changes along constructor paths. -/
def shared (family : Nat → (Nat → Bool) → Bool) (worlds : Route → Nat → Bool) (call : Call) : Bool :=
  family call.name (worlds call.route)

theorem compile_shared (keys : List Nat) (ctx : Context) (left right : Ty)
    (world : Nat → Bool) (family : Nat → (Nat → Bool) → Bool) (worlds : Route → Nat → Bool) :
    (∀clause∈compile keys ctx left right,clause.Holds world (shared family worlds)) ↔
      interpret keys ctx world (shared family worlds) [] left=true →
      interpret keys ctx world (shared family worlds) [] right=true :=
  compile_correct keys ctx left right world (shared family worlds)

def CompiledClause.Holds (world : Nat → Bool) (images : Call → Bool) (c : CompiledClause) : Prop :=
  ClauseHolds world c.guard ∨ ∃l∈c.literals,images l.1=l.2

private theorem compileGuard_holds {fuel : Nat} {clause : Clause} {guards : CNF}
    (h : CompactCNF.toCNF fuel true clause.guard=.success guards)
    (world : Nat → Bool) (images : Call → Bool) :
    (∀guard∈guards,(CompiledClause.mk guard clause.literals).Holds world images) ↔
      clause.Holds world images := by
  classical
  by_cases hl : ∃l∈clause.literals,images l.1=l.2
  · simp [CompiledClause.Holds,Clause.Holds,hl]
  · simpa only [CompiledClause.Holds,Clause.Holds,hl,or_false] using CompactCNF.toCNF_correct h world

theorem compileGuards_correct {fuel : Nat} {clauses : List Clause} {output : List CompiledClause}
    (h : compileGuards fuel clauses=.success output) (world : Nat → Bool) (images : Call → Bool) :
    (∀clause∈output,clause.Holds world images) ↔ ∀clause∈clauses,clause.Holds world images := by
  induction clauses generalizing output with
  | nil => simp [compileGuards] at h; subst output; simp
  | cons clause rest ih =>
    cases hg : CompactCNF.toCNF fuel true clause.guard <;> simp [compileGuards,hg,bind,RunResult.bind] at h
    rename_i guards
    cases ht : compileGuards fuel rest <;> simp [ht,pure] at h
    rename_i tail
    subst output
    simp only [List.forall_mem_append,List.forall_mem_map,List.forall_mem_cons,
      compileGuard_holds hg,ih ht]

theorem compileGuards_complete (clauses : List Clause) :
    ∃threshold output,∀fuel≥threshold,compileGuards fuel clauses=.success output := by
  induction clauses with
  | nil => exact ⟨0,[],by intro fuel _;rfl⟩
  | cons clause rest ih =>
    obtain ⟨n,guards,hg⟩ := CompactCNF.toCNF_complete clause.guard true
    obtain ⟨k,tail,ht⟩ := ih
    refine ⟨max n k,guards.map (fun guard=>⟨guard,clause.literals⟩)++tail,?_⟩
    intro fuel hf
    simp [compileGuards,hg fuel ((le_max_left _ _).trans hf),
      ht fuel ((le_max_right _ _).trans hf),bind,pure,RunResult.bind]

theorem compileGuards_origin {fuel : Nat} {clauses : List Clause} {output : List CompiledClause}
    (h : compileGuards fuel clauses=.success output) {result : CompiledClause} (hr : result∈output) :
    ∃original∈clauses,result.literals=original.literals := by
  induction clauses generalizing output with
  | nil => simp [compileGuards] at h; subst output; cases hr
  | cons clause rest ih =>
    cases hg : CompactCNF.toCNF fuel true clause.guard <;> simp [compileGuards,hg,bind,RunResult.bind] at h
    rename_i guards
    cases ht : compileGuards fuel rest <;> simp [ht,pure] at h
    rename_i tail
    subst output
    rcases List.mem_append.mp hr with hr|hr
    · obtain ⟨guard,_,rfl⟩ := List.mem_map.mp hr
      exact ⟨clause,List.mem_cons_self,rfl⟩
    · obtain ⟨original,ho,he⟩ := ih ht hr
      exact ⟨original,List.mem_cons_of_mem _ ho,he⟩

theorem compiled_binary {fuel : Nat} {keys : List Nat} {ctx : Context} {left right : Ty}
    {output : List CompiledClause} (h : compileGuards fuel (compile keys ctx left right)=.success output)
    {clause : CompiledClause} (hc : clause∈output) : clause.literals.length≤2 := by
  obtain ⟨original,ho,he⟩ := compileGuards_origin h hc
  rw [he]
  exact compile_binary ho

theorem compiled_correct {fuel : Nat} {keys : List Nat} {ctx : Context} {left right : Ty}
    {output : List CompiledClause} (h : compileGuards fuel (compile keys ctx left right)=.success output)
    (world : Nat → Bool) (family : Nat → (Nat → Bool) → Bool) (worlds : Route → Nat → Bool) :
    (∀clause∈output,clause.Holds world (shared family worlds)) ↔
      interpret keys ctx world (shared family worlds) [] left=true →
      interpret keys ctx world (shared family worlds) [] right=true :=
  (compileGuards_correct h world (shared family worlds)).trans
    (compile_shared keys ctx left right world family worlds)

def Data.Allowed (keys : List Nat) : Data → Prop
  | .fixed _ => True
  | .image call _ => call.name∈keys

theorem Data.flip_allowed {keys : List Nat} {data : Data} (h : data.Allowed keys) :
    data.flip.Allowed keys := by cases data <;> exact h

theorem reference_allowed (keys : List Nat) (ctx : Context) (route : Route) (v : TypeVar) :
    (reference keys ctx route v).Allowed keys := by
  cases v <;> simp only [reference]
  · split
    · simpa only [Data.Allowed,List.contains_iff_mem] using ‹keys.contains _=true›
    · trivial
  · trivial

theorem observe_allowed {keys : List Nat} {ctx : Context} {route : Route} {a : Ty} {branch : Branch}
    (h : branch∈observe keys ctx route a) : branch.view.data.Allowed keys := by
  induction a generalizing route branch with
  | var v => cases List.mem_singleton.mp h;exact reference_allowed _ _ _ _
  | unit => cases List.mem_singleton.mp h;trivial
  | credit => cases List.mem_singleton.mp h;trivial
  | prod a b iha ihb | sum a b iha ihb =>
    rcases List.mem_append.mp h with h|h
    · obtain ⟨original,ho,rfl⟩ := List.mem_map.mp h
      exact iha (branch := original) ho
    · obtain ⟨original,ho,rfl⟩ := List.mem_map.mp h
      exact ihb (branch := original) ho
  | fn a b iha ihb =>
    rcases List.mem_append.mp h with h|h
    · obtain ⟨original,ho,rfl⟩ := List.mem_map.mp h
      exact Data.flip_allowed (iha (branch := original) ho)
    · obtain ⟨original,ho,rfl⟩ := List.mem_map.mp h
      exact ihb (branch := original) ho
  | modal a m ih =>
    obtain ⟨original,ho,rfl⟩ := List.mem_map.mp h
    exact ih (branch := original) ho

theorem makeClause_allowed {keys : List Nat} {data : List Data}
    (h : ∀d∈data,d.Allowed keys) (guard : BoolExpr) {literal : Call × Bool}
    (hl : literal∈(makeClause guard data).literals) : literal.1.name∈keys := by
  obtain ⟨d,hd,he⟩ := List.mem_filterMap.mp hl
  cases d <;> simp only [Option.some.injEq,reduceCtorEq] at he
  cases he
  exact h _ hd

theorem compare_allowed {keys : List Nat} {active : BoolExpr} {left right : View}
    (hl : left.data.Allowed keys) (hr : right.data.Allowed keys) {clause : Clause}
    (h : clause∈compare active left right) {literal : Call × Bool} (hc : literal∈clause.literals) :
    literal.1.name∈keys := by
  simp only [compare,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  all_goals
    apply makeClause_allowed _ _ hc
    simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  · exact ⟨hl,hr⟩
  · exact ⟨hl,Data.flip_allowed hr⟩
  · exact ⟨Data.flip_allowed hl,hr⟩
  · exact ⟨Data.flip_allowed hl,Data.flip_allowed hr⟩

theorem compile_allowed {keys : List Nat} {ctx : Context} {left right : Ty} {clause : Clause}
    (h : clause∈compile keys ctx left right) {literal : Call × Bool} (hc : literal∈clause.literals) :
    literal.1.name∈keys := by
  obtain ⟨l,hl,h⟩ := List.mem_flatMap.mp h
  obtain ⟨r,hr,h⟩ := List.mem_flatMap.mp h
  exact compare_allowed (observe_allowed hl) (observe_allowed hr) h hc

theorem compiled_allowed {fuel : Nat} {keys : List Nat} {ctx : Context} {left right : Ty}
    {output : List CompiledClause} (h : compileGuards fuel (compile keys ctx left right)=.success output)
    {clause : CompiledClause} (hc : clause∈output) {literal : Call × Bool}
    (hl : literal∈clause.literals) : literal.1.name∈keys := by
  obtain ⟨original,ho,he⟩ := compileGuards_origin h hc
  exact compile_allowed ho (he ▸ hl)

end ModalityInference.ComparisonSignedEndpoints
