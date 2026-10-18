import ModalityInference.Proofs.ComparisonSignedBranchAlignment
import ModalityInference.Proofs.ComparisonSignedBranchCalls

namespace ModalityInference.ComparisonSignedCallCoverage
open ComparisonSignedEndpoints ComparisonSignedObservation ComparisonStructuralLayout ComparisonAlgebra ComparisonControls

 theorem nodeAt_append (layout : Layout) (route suffix : Route) :
    nodeAt layout (route++suffix)=(nodeAt layout route).bind (fun node=>nodeAt node suffix) := by
  induction route generalizing layout with
  | nil => simp only [List.nil_append,nodeAt_nil,Option.bind_some]
  | cons side route ih =>
    cases layout <;> cases side <;> simp only [List.cons_append,nodeAt,Option.bind_none,ih]

def Data.Calls (P : Call→Prop) : Data→Prop
  | .fixed _ => True
  | .image call _ => P call

theorem Data.flip_calls {P : Call→Prop} {d : Data} (h : Data.Calls P d) : Data.Calls P d.flip := by
  cases d <;> exact h

def Site (Δ : Bounds) (keys : List Nat) (σ : CompareSubstitution) (layout : Layout) (call : Call) : Prop :=
  ∃node,nodeAt layout call.route=some node ∧ call.name∈keys ∧
    Representable Δ node.shape (σ.type (.flex call.name))

theorem observe_sites {Δ labels keys σ node a} (he : Endpoint Δ labels keys σ node a)
    (ctx : ComparisonSignedEndpoints.Context) {layout : Layout} {route : Route} (hroute : nodeAt layout route=some node)
    {branch : Branch} (hb : branch∈observe keys ctx route a) :
    Data.Calls (Site Δ keys σ layout) branch.view.data := by
  induction he generalizing route branch with
  | @image node n hn hrep =>
    obtain rfl:=List.mem_singleton.mp hb
    simp only [View.base,reference,List.contains_iff_mem,hn,if_true,Data.Calls]
    exact ⟨node,hroute,hn,hrep⟩
  | @fixed node v hn hf hm =>
    obtain rfl:=List.mem_singleton.mp hb
    cases v with
    | rigid => trivial
    | flex n =>
      have hnot : n∉keys:=fun hk=>hn n hk rfl
      simp only [View.base,reference,List.contains_iff_mem,hnot,if_false,Data.Calls]
  | unit hm => obtain rfl:=List.mem_singleton.mp hb;trivial
  | credit hm => obtain rfl:=List.mem_singleton.mp hb;trivial
  | @node k basis left right a b hl hr ihl ihr =>
    have hleft : nodeAt layout (route++[false])=some left := by rw [nodeAt_append,hroute];simp [nodeAt]
    have hright : nodeAt layout (route++[true])=some right := by rw [nodeAt_append,hroute];simp [nodeAt]
    cases k <;> simp only [publicOp,observe] at hb
    all_goals rcases List.mem_append.mp hb with hb|hb
    all_goals obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hb
    · exact ihl (branch := original) hleft ho
    · exact ihr (branch := original) hright ho
    · exact ihl (branch := original) hleft ho
    · exact ihr (branch := original) hright ho
    · exact Data.flip_calls (ihl (branch := original) hleft ho)
    · exact ihr (branch := original) hright ho
  | modal hi hm ih =>
    obtain ⟨original,ho,rfl⟩:=List.mem_map.mp hb
    exact ih (branch := original) hroute ho

theorem makeClause_calls {P : Call→Prop} {data : List Data}
    (h : ∀d∈data,Data.Calls P d) (guard : BoolExpr) {literal : Call×Bool}
    (hl : literal∈(makeClause guard data).literals) : P literal.1 := by
  obtain ⟨d,hd,he⟩:=List.mem_filterMap.mp hl
  cases d <;> simp only [Option.some.injEq,reduceCtorEq] at he
  cases he
  exact h _ hd

theorem compare_calls {P : Call→Prop} {active : BoolExpr} {left right : View}
    (hl : Data.Calls P left.data) (hr : Data.Calls P right.data) {clause : ComparisonSignedEndpoints.Clause}
    (h : clause∈ComparisonSignedEndpoints.compare active left right) {literal : Call×Bool} (hc : literal∈clause.literals) :
    P literal.1 := by
  simp only [ComparisonSignedEndpoints.compare,List.mem_cons,List.mem_nil_iff,or_false] at h
  rcases h with rfl|rfl|rfl|rfl
  all_goals
    apply makeClause_calls _ _ hc
    simp only [List.forall_mem_cons,List.not_mem_nil,false_implies,implies_true,and_true]
  · exact ⟨hl,hr⟩
  · exact ⟨hl,Data.flip_calls hr⟩
  · exact ⟨Data.flip_calls hl,hr⟩
  · exact ⟨Data.flip_calls hl,Data.flip_calls hr⟩

theorem compile_sites {Δ labels keys σ layout left right}
    (hl : Endpoint Δ labels keys σ layout left) (hr : Endpoint Δ labels keys σ layout right)
    {ctx : ComparisonSignedEndpoints.Context} {clause : ComparisonSignedEndpoints.Clause} (h : clause∈ComparisonSignedEndpoints.compile keys ctx left right)
    {literal : Call×Bool} (hc : literal∈clause.literals) : Site Δ keys σ layout literal.1 := by
  obtain ⟨l,hleft,h⟩:=List.mem_flatMap.mp h
  obtain ⟨r,hright,h⟩:=List.mem_flatMap.mp h
  exact compare_calls (observe_sites hl ctx (nodeAt_nil layout) hleft)
    (observe_sites hr ctx (nodeAt_nil layout) hright) h hc

theorem compiled_sites {Δ labels keys σ layout left right}
    (hl : Endpoint Δ labels keys σ layout left) (hr : Endpoint Δ labels keys σ layout right)
    {fuel : Nat} {ctx : ComparisonSignedEndpoints.Context} {clauses : List CompiledClause}
    (hc : compileGuards fuel (ComparisonSignedEndpoints.compile keys ctx left right)=.success clauses)
    {clause : CompiledClause} (hm : clause∈clauses) {literal : Call×Bool} (hlit : literal∈clause.literals) :
    Site Δ keys σ layout literal.1 := by
  obtain ⟨original,ho,he⟩:=compileGuards_origin hc hm
  exact compile_sites hl hr ho (he ▸ hlit)


open ComparisonSignedBranchImages ComparisonSelectedBases

theorem select_lookup {first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world : Nat→Bool}
    {images : List (Nat×CompareTy)} {modes : List (Nat×ModExpr)} {result : CompareSubstitution}
    (h : select first p solved world images modes=some result)
    {name : Nat} (hn : name∈inputTypeKeys p) :
    ∃raw,pick first p solved world images name=some raw ∧
      result.type (.flex name)=raw.subst CompareTy.var result.mode := by
  have hk : name∈result.types.map Prod.fst := (select_spec h).2.1 ▸ hn
  cases hl : result.types.lookup name with
  | none =>
    obtain ⟨entry,he,hkey⟩:=List.mem_map.mp hk
    have hne:=List.lookup_eq_none_iff.mp hl entry he
    simp [hkey] at hne
  | some a =>
    have hmem : (name,a)∈result.types := by
      obtain ⟨l,r,he,_⟩:=List.lookup_eq_some_iff.mp hl
      simp [he]
    obtain ⟨raw,hraw,he⟩ := (select_spec h).2.2 (name,a) hmem
    exact ⟨raw,hraw,by simpa only [CompareSubstitution.type,hl,Option.getD_some,select_mode h] using he⟩

theorem selected_site {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : (ComparisonSelectedBases.layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result)
    {layout : Layout} (hf : layout.shape.subst solved.fixedShapes=layout.shape)
    {call : Call} (hc : Site p.assumptions (inputTypeKeys p) result layout call) :
    ∃node raw branch key,nodeAt layout call.route=some node ∧
      result.type (.flex call.name)=raw.subst CompareTy.var result.mode ∧
      enabled world (prepared first p solved (.flex call.name))=some branch ∧
      locate call.name branch.shape (entries first p solved)=some key ∧
      images.lookup key=some raw ∧ node.shape=branch.shape := by
  obtain ⟨node,hn,hkey,hrep⟩:=hc
  obtain ⟨raw,hraw,he⟩:=select_lookup h hkey
  obtain ⟨branch,key,hbranch,hkey,himage⟩:=pick_spec hraw
  refine ⟨node,raw,branch,key,hn,he,hbranch,hkey,himage,?_⟩
  have hvar := (mem_inputTypeKeys p call.name).mp ‹call.name∈inputTypeKeys p› |>.1
  have hshape := (prepared_sound hw hvar (enabled_spec hbranch).1 (enabled_spec hbranch).2).1
  obtain ⟨k,_,hreify⟩:=pick_reifyImage hr hraw
  have hrawrep := ComparisonObserverModePullback.representable hm
    (reifyImage_representable hs hw hvar hreify)
  have hmodel := ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hs).1
  have hnode := hrep.2.2 solved.fixedShapes hmodel
  have hrawshape := hrawrep.2.2 solved.fixedShapes hmodel
  rw [he,select_mode h] at hnode
  rw [nodeAt_fixed hf hn] at hnode
  rw [ComparisonShapeRetraction.fixedShapes_idempotent hs] at hrawshape
  exact hnode.symm.trans (hrawshape.trans hshape.symm)


theorem resolve_complete {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : (ComparisonSelectedBases.layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result)
    {layout : Layout} (hf : layout.shape.subst solved.fixedShapes=layout.shape)
    {call : Call} (hc : Site p.assumptions (inputTypeKeys p) result layout call) :
    ∃resolved,ComparisonSignedBranchCalls.resolve (entries first p solved) layout call=some resolved := by
  obtain ⟨node,raw,branch,key,hn,_,_,hk,_,he⟩:=selected_site hs hw hr hm h hf hc
  exact ⟨⟨key,call.route⟩,by simp [ComparisonSignedBranchCalls.resolve,hn,he,hk]⟩

theorem compile_complete {shapeFuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {world parameters : Nat→Bool}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hw : (ComparisonSelectedBases.layout first p solved).theory.eval world=true)
    {r : CNF} {images : List (Nat×CompareTy)}
    (hr : (input (entries first p solved)).reconstruct r parameters=some images)
    {modes : List (Nat×ModExpr)}
    (hm : ComparisonModeRestriction.Fixed p.assumptions ({modes:=modes}:CompareSubstitution).mode)
    {result : CompareSubstitution} (h : select first p solved world images modes=some result)
    {layout : Layout} (hf : layout.shape.subst solved.fixedShapes=layout.shape)
    {labels : List (GuardedMode p.assumptions)} {left right : Ty}
    (hl : Endpoint p.assumptions labels (inputTypeKeys p) result layout left)
    (hrr : Endpoint p.assumptions labels (inputTypeKeys p) result layout right)
    {fuel : Nat} {ctx : ComparisonSignedEndpoints.Context} {clauses : List CompiledClause}
    (hc : compileGuards fuel (ComparisonSignedEndpoints.compile (inputTypeKeys p) ctx left right)=.success clauses) :
    ∃output,ComparisonSignedBranchCalls.compile (entries first p solved) layout clauses=some output := by
  apply ComparisonSignedBranchCalls.compile_complete
  intro clause hcl literal hli
  exact resolve_complete hs hw hr hm h hf (compiled_sites hl hrr hc hcl hli)

end ModalityInference.ComparisonSignedCallCoverage
