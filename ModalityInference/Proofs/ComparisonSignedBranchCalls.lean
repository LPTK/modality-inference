import ModalityInference.ComparisonSignedBranchCalls
import ModalityInference.Proofs.ComparisonSignedBranchImages
import ModalityInference.Proofs.ComparisonSignedEndpoints

namespace ModalityInference.ComparisonSignedBranchCalls
open ComparisonSignedEndpoints ComparisonSignedBranchImages ComparisonSignedObservation

theorem resolve_spec {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {call result : Call} (h : resolve table layout call=some result) :
    result.route=call.route ∧ result.name∈(input table).keys ∧
      ∃node,nodeAt layout call.route=some node ∧ locate call.name node.shape table=some result.name := by
  cases hn : nodeAt layout call.route <;> simp [resolve,hn] at h
  rename_i node
  cases hk : locate call.name node.shape table <;> simp [hk] at h
  subst result
  exact ⟨rfl,locate_key hk,node,rfl,hk⟩

def pullback (table : List Entry) (layout : ComparisonStructuralLayout.Layout)
    (images : Call → Bool) (call : Call) : Bool :=
  ((resolve table layout call).map images).getD false

private theorem mapM_relation {α β : Type} (f : α → Option β)
    {xs : List α} {ys : List β} (h : xs.mapM f=some ys) :
    List.Forall₂ (fun x y=>f x=some y) xs ys := by
  induction xs generalizing ys with
  | nil =>
      have he : ys=[] := by simpa using h.symm
      subst ys
      exact .nil
  | cons x xs ih =>
      simp only [List.mapM_cons,Option.bind_eq_some_iff,bind,pure,Option.some.injEq] at h
      obtain ⟨y,hy,rest,hr,rfl⟩ := h
      exact .cons hy (ih hr)

private theorem mapM_exists {α β : Type} (f : α → Option β) (xs : List α)
    (h : ∀x∈xs,∃y,f x=some y) : ∃ys,xs.mapM f=some ys := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
      obtain ⟨y,hy⟩ := h x List.mem_cons_self
      obtain ⟨ys,hys⟩ := ih (fun z hz=>h z (List.mem_cons_of_mem _ hz))
      exact ⟨y::ys,by simp [hy,hys]⟩

theorem clause_spec {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {source result : CompiledClause} (h : clause table layout source=some result) :
    result.guard=source.guard ∧ List.Forall₂
      (fun old new=>resolve table layout old.1=some new.1 ∧ new.2=old.2)
      source.literals result.literals := by
  simp only [clause,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at h
  obtain ⟨literals,hl,rfl⟩ := h
  refine ⟨rfl,?_⟩
  apply List.Forall₂.imp ?_ (mapM_relation _ hl)
  intro old new hh
  rcases old with ⟨call,sign⟩
  cases hc : resolve table layout call <;> simp [hc] at hh
  subst new
  exact ⟨rfl,rfl⟩

private theorem literal_values {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {left right : List (Call × Bool)}
    (h : List.Forall₂ (fun old new=>resolve table layout old.1=some new.1 ∧ new.2=old.2) left right)
    (images : Call → Bool) :
    (∃literal∈right,images literal.1=literal.2) ↔
      ∃literal∈left,pullback table layout images literal.1=literal.2 := by
  induction h with
  | nil => simp
  | @cons old new left right h ht ih =>
      simp only [List.mem_cons,exists_eq_or_imp,ih,pullback,h.1,Option.map_some,Option.getD_some,h.2]

theorem clause_correct {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {source result : CompiledClause} (h : clause table layout source=some result)
    (world : Nat → Bool) (images : Call → Bool) :
    result.Holds world images ↔ source.Holds world (pullback table layout images) := by
  obtain ⟨hg,hl⟩ := clause_spec h
  exact or_congr (by rw [hg]) (literal_values hl images)

theorem clause_binary {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {source result : CompiledClause} (h : clause table layout source=some result) :
    result.literals.length=source.literals.length := (clause_spec h).2.length_eq.symm

private theorem resolved_allowed {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {left right : List (Call × Bool)}
    (h : List.Forall₂ (fun old new=>resolve table layout old.1=some new.1 ∧ new.2=old.2) left right) :
    ∀literal∈right,literal.1.name∈(input table).keys := by
  induction h with
  | nil => simp
  | cons hab ht ih =>
      intro literal hm
      rcases List.mem_cons.mp hm with rfl|hm
      · exact (resolve_spec hab.1).2.1
      · exact ih _ hm

theorem clause_allowed {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {source result : CompiledClause} (h : clause table layout source=some result) :
    ∀literal∈result.literals,literal.1.name∈(input table).keys :=
  resolved_allowed (clause_spec h).2

theorem clause_complete {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    (source : CompiledClause)
    (h : ∀literal∈source.literals,∃call,resolve table layout literal.1=some call) :
    ∃result,clause table layout source=some result := by
  obtain ⟨literals,hl⟩ := mapM_exists (fun (literal : Call × Bool)=>do
    return (←resolve table layout literal.1,literal.2)) source.literals (by
      intro literal hm
      obtain ⟨call,hcall⟩ := h literal hm
      exact ⟨(call,literal.2),by simp [hcall]⟩)
  refine ⟨⟨source.guard,literals⟩,?_⟩
  change (source.literals.mapM (fun (literal : Call × Bool)=>do return (←resolve table layout literal.1,literal.2))).bind
    (fun ls=>some (CompiledClause.mk source.guard ls))=some (CompiledClause.mk source.guard literals)
  rw [hl]
  rfl

theorem compile_complete {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    (sources : List CompiledClause)
    (h : ∀source∈sources,∀literal∈source.literals,∃call,resolve table layout literal.1=some call) :
    ∃results,compile table layout sources=some results :=
  mapM_exists _ _ (fun source hs=>clause_complete source (h source hs))

private theorem related_origin {α β : Type} {R : α → β → Prop}
    {left : List α} {right : List β} (h : List.Forall₂ R left right) :
    ∀y∈right,∃x∈left,R x y := by
  induction h with
  | nil => simp
  | @cons a b left right hab ht ih =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact ⟨a,List.mem_cons_self,hab⟩
      · obtain ⟨x,hx,hxy⟩ := ih y hy
        exact ⟨x,List.mem_cons_of_mem _ hx,hxy⟩

theorem compile_origin {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {sources results : List CompiledClause} (h : compile table layout sources=some results) :
    ∀result∈results,∃source∈sources,clause table layout source=some result :=
  related_origin (mapM_relation _ h)

theorem compile_correct {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {sources results : List CompiledClause} (h : compile table layout sources=some results)
    (world : Nat → Bool) (images : Call → Bool) :
    (∀result∈results,result.Holds world images) ↔
      ∀source∈sources,source.Holds world (pullback table layout images) := by
  have hr := mapM_relation _ h
  clear h
  induction hr with
  | nil => simp
  | @cons source result sources results hc ht ih =>
      simp only [List.forall_mem_cons,clause_correct hc,ih]

theorem compile_binary {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {sources results : List CompiledClause} (h : compile table layout sources=some results)
    (hb : ∀source∈sources,source.literals.length≤2) :
    ∀result∈results,result.literals.length≤2 := by
  intro result hm
  obtain ⟨source,hs,hc⟩ := compile_origin h result hm
  rw [clause_binary hc]
  exact hb source hs

theorem compile_allowed {table : List Entry} {layout : ComparisonStructuralLayout.Layout}
    {sources results : List CompiledClause} (h : compile table layout sources=some results) :
    ∀result∈results,∀literal∈result.literals,literal.1.name∈(input table).keys := by
  intro result hm
  obtain ⟨source,_,hc⟩ := compile_origin h result hm
  exact clause_allowed hc

end ModalityInference.ComparisonSignedBranchCalls
