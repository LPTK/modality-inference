import ModalityInference.ComparisonPreparedQueries
import ModalityInference.Proofs.ComparisonSignedBranchCalls
import ModalityInference.Proofs.ComparisonSelectedPlan
import ModalityInference.Proofs.ComparisonGuardedEndpointQueries

namespace ModalityInference.ComparisonPreparedQueries

theorem branch_spec {fuel first activation : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoint : Ty × Ty} {b : ComparisonSelectedBases.Branch} {a : Alternative}
    (h : branch fuel first activation p solved declared endpoint b=.success (some a)) :
    a.activation=activation ∧ a.branch=b ∧ a.endpoint=endpoint ∧
    ComparisonStructuralLayout.selected (ComparisonSelectedBases.inputNames p)
      (ComparisonSelectedBases.inputModes p) solved.fixedShapes b=some a.layout ∧
    ComparisonStructuralCoherence.run fuel p.assumptions
      (ComparisonStructuralEndpoints.atShape declared) a.layout=.success a.theory ∧
    ComparisonSignedEndpoints.compileGuards fuel
      (ComparisonSignedEndpoints.compile (ComparisonSelectedBases.inputTypeKeys p)
        (ComparisonSignedObservation.context a.layout ModExpr.var) endpoint.1 endpoint.2)=.success a.original ∧
    ComparisonSignedBranchCalls.compile (ComparisonSignedBranchImages.entries first p solved)
      a.layout a.original=some a.clauses := by
  cases hl : ComparisonStructuralLayout.selected (ComparisonSelectedBases.inputNames p)
    (ComparisonSelectedBases.inputModes p) solved.fixedShapes b with
  | none => simp [branch,hl] at h
  | some layout =>
      cases ht : ComparisonStructuralCoherence.run fuel p.assumptions
        (ComparisonStructuralEndpoints.atShape declared) layout with
      | exhausted => simp [branch,hl,ht] at h
      | rejected reason => simp [branch,hl,ht] at h
      | success theory =>
          cases hc : ComparisonSignedEndpoints.compileGuards fuel
            (ComparisonSignedEndpoints.compile (ComparisonSelectedBases.inputTypeKeys p)
              (ComparisonSignedObservation.context layout ModExpr.var) endpoint.1 endpoint.2) with
          | exhausted => simp [branch,hl,ht,hc,bind,RunResult.bind] at h
          | rejected reason => simp [branch,hl,ht,hc,bind,RunResult.bind] at h
          | success original =>
              cases hr : ComparisonSignedBranchCalls.compile
                (ComparisonSignedBranchImages.entries first p solved) layout original with
              | none => simp [branch,hl,ht,hc,hr,bind,pure,RunResult.bind] at h
              | some clauses =>
                  have he : a=⟨activation,b,endpoint,layout,theory,original,clauses⟩ := by
                    simpa [branch,hl,ht,hc,hr,bind,pure,RunResult.bind] using h.symm
                  subst a
                  exact ⟨rfl,rfl,rfl,rfl,ht,hc,hr⟩

theorem branch_binary {fuel first activation : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoint : Ty × Ty} {b : ComparisonSelectedBases.Branch} {a : Alternative}
    (h : branch fuel first activation p solved declared endpoint b=.success (some a)) :
    ∀c∈a.clauses,c.literals.length≤2 := by
  obtain ⟨_,_,_,_,_,hc,hr⟩ := branch_spec h
  exact ComparisonSignedBranchCalls.compile_binary hr
    (fun _ hm=>ComparisonSignedEndpoints.compiled_binary hc hm)

theorem branch_allowed {fuel first activation : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoint : Ty × Ty} {b : ComparisonSelectedBases.Branch} {a : Alternative}
    (h : branch fuel first activation p solved declared endpoint b=.success (some a)) :
    ∀c∈a.clauses,∀lit∈c.literals,
      lit.1.name∈(ComparisonSignedBranchImages.input
        (ComparisonSignedBranchImages.entries first p solved)).keys := by
  obtain ⟨_,_,_,_,_,_,hr⟩ := branch_spec h
  exact ComparisonSignedBranchCalls.compile_allowed hr

private theorem bind_success {α β : Type} {r : RunResult α} {f : α → RunResult β} {b : β}
    (h : r.bind f=.success b) : ∃a,r=.success a ∧ f a=.success b := by
  cases r <;> simp_all [RunResult.bind]

private theorem any_map_eval {α : Type} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.any (xs.map f)).eval world=true ↔ ∃x∈xs,(f x).eval world=true := by
  induction xs <;> simp_all [BoolExpr.any,BoolExpr.eval]

private theorem all_map_eval {α : Type} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all (xs.map f)).eval world=true ↔ ∀x∈xs,(f x).eval world=true := by
  induction xs <;> simp_all [BoolExpr.all,BoolExpr.eval]

theorem alternatives_origin {fuel first next : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoint : Ty × Ty} {bs : List ComparisonSelectedBases.Branch} {output : List Alternative}
    (h : alternatives fuel first p solved declared endpoint next bs=.success output) :
    ∀a∈output,∃activation b,b∈bs ∧
      branch fuel first activation p solved declared endpoint b=.success (some a) := by
  induction bs generalizing next output with
  | nil => have he : output=[] := by simpa [alternatives] using h.symm
           subst output; simp
  | cons b bs ih =>
      obtain ⟨head,hh,hrest⟩ := bind_success h
      obtain ⟨tail,ht,he⟩ := bind_success hrest
      have he' : output=head.toList++tail := by simpa [pure] using he.symm
      subst output
      intro a ha
      rcases List.mem_append.mp ha with ha|ha
      · cases head with
        | none => cases ha
        | some x =>
            have hx : a=x := by simpa using ha
            subst a
            exact ⟨next,b,List.mem_cons_self,hh⟩
      · obtain ⟨activation,c,hc,hr⟩ := ih ht a ha
        exact ⟨activation,c,List.mem_cons_of_mem _ hc,hr⟩

theorem groups_spec {fuel first next : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoints : List (Ty × Ty)} {output : List Group}
    (h : groups fuel first p solved declared next endpoints=.success output) :
    output.map Group.endpoint=endpoints ∧
      ∀g∈output,∀a∈g.alternatives,∃activation b,b∈branches first p solved g.endpoint ∧
        branch fuel first activation p solved declared g.endpoint b=.success (some a) := by
  induction endpoints generalizing next output with
  | nil => have he : output=[] := by simpa [groups] using h.symm
           subst output; simp
  | cons pair rest ih =>
      obtain ⟨choices,hc,hrest⟩ := bind_success h
      obtain ⟨tail,ht,he⟩ := bind_success hrest
      have he' : output=⟨pair,choices⟩::tail := by simpa [pure] using he.symm
      subst output
      obtain ⟨hkeys,hrest⟩ := ih ht
      refine ⟨by simp [hkeys],?_⟩
      intro g hg a ha
      rcases List.mem_cons.mp hg with rfl|hg
      · exact alternatives_origin hc a ha
      · exact hrest g hg a ha

theorem compile_spec {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program}
    (h : compile fuel first p solved=.success program) :
    ComparisonStructuralEndpoints.normalizeList fuel p solved
      (ComparisonStructuralEndpoints.declared p)=.success program.declared ∧
    groups fuel first p solved program.declared (ComparisonSelectedBases.layout first p solved).next
      (ComparisonSignedObservation.sourceEndpoints p)=.success program.groups ∧
    CompactCNF.toCNF fuel true
      (.and (ComparisonSelectedBases.selectorFormula first p solved)
        (.all (program.groups.map Group.formula)))=.success program.condition := by
  obtain ⟨declared,hd,ha⟩ := bind_success h
  obtain ⟨gs,hg,hb⟩ := bind_success ha
  obtain ⟨condition,hc,he⟩ := bind_success hb
  have he' : program=⟨declared,gs,condition⟩ := by simpa [pure] using he.symm
  subst program
  exact ⟨hd,hg,hc⟩

theorem compile_binary {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program}
    (h : compile fuel first p solved=.success program) :
    ∀source∈program.sources,source.Binary := by
  intro source hs
  obtain ⟨g,hg,hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
  obtain ⟨activation,b,_,hb⟩ := (groups_spec (compile_spec h).2.1).2 g hg a ha
  exact branch_binary hb

theorem compile_allowed {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program}
    (h : compile fuel first p solved=.success program) :
    ∀source∈program.sources,source.Allowed
      (ComparisonSignedBranchImages.input (ComparisonSignedBranchImages.entries first p solved)).keys := by
  intro source hs
  obtain ⟨g,hg,hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hs
  obtain ⟨activation,b,_,hb⟩ := (groups_spec (compile_spec h).2.1).2 g hg a ha
  exact branch_allowed hb

theorem compile_condition {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program}
    (h : compile fuel first p solved=.success program) (world : Nat → Bool) :
    CNFHolds world program.condition ↔
      (ComparisonSelectedBases.selectorFormula first p solved).eval world=true ∧
      (∀g∈program.groups, (∃a∈g.alternatives,world a.activation=true) ∧
        ∀a∈g.alternatives,world a.activation=true → a.branch.guard.eval world=true) := by
  rw [CompactCNF.toCNF_correct (compile_spec h).2.2]
  simp only [BoolExpr.eval,Bool.and_eq_true,all_map_eval,Group.formula,any_map_eval,
    Alternative.condition,Bool.or_eq_true]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro g
  apply forall_congr'
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro a
  apply forall_congr'
  intro _
  cases world a.activation <;> simp

theorem Alternative.active_iff (a : Alternative) (world : Nat → Bool) :
    ¬ClauseHolds world a.source.guard ↔ world a.activation=true := by
  simp [Alternative.source,ClauseHolds]

theorem compile_active_endpoint {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program}
    (h : compile fuel first p solved=.success program) {world : Nat → Bool}
    (hw : CNFHolds world program.condition) {pair : Ty × Ty}
    (hp : pair∈ComparisonSignedObservation.sourceEndpoints p) :
    ∃a,a.source∈program.sources ∧ a.endpoint=pair ∧ world a.activation=true ∧
      a.branch.guard.eval world=true ∧ a.branch∈branches first p solved pair ∧
      branch fuel first a.activation p solved program.declared pair a.branch=.success (some a) := by
  have hg:=groups_spec (compile_spec h).2.1
  have hmem : pair∈program.groups.map Group.endpoint := hg.1 ▸ hp
  obtain ⟨g,hgmem,hpair⟩ := List.mem_map.mp hmem
  obtain ⟨a,ha,hactive⟩ := ((compile_condition h world).mp hw).2 g hgmem |>.1
  have hguard:=((compile_condition h world).mp hw).2 g hgmem |>.2 a ha hactive
  obtain ⟨activation,b,hb,hbranch⟩ := hg.2 g hgmem a ha
  obtain ⟨heact,heb,hepair,_⟩ := branch_spec hbranch
  refine ⟨a,?_,hepair.trans hpair,hactive,hguard,?_,?_⟩
  · exact List.mem_flatMap.mpr ⟨g,hgmem,List.mem_map.mpr ⟨a,ha,rfl⟩⟩
  · simpa only [heb,←hpair] using hb
  · simpa only [heact,heb,←hpair] using hbranch

theorem branch_observation {fuel first activation : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoint : Ty × Ty} {b : ComparisonSelectedBases.Branch} {a : Alternative}
    (h : branch fuel first activation p solved declared endpoint b=.success (some a))
    (world : Nat → Bool) (images : ComparisonSignedEndpoints.Call → Bool) :
    (∀c∈a.clauses,c.Holds world images) ↔
      ComparisonSignedEndpoints.interpret (ComparisonSelectedBases.inputTypeKeys p)
        (ComparisonSignedObservation.context a.layout ModExpr.var) world
        (ComparisonSignedBranchCalls.pullback (ComparisonSignedBranchImages.entries first p solved)
          a.layout images) [] endpoint.1=true →
      ComparisonSignedEndpoints.interpret (ComparisonSelectedBases.inputTypeKeys p)
        (ComparisonSignedObservation.context a.layout ModExpr.var) world
        (ComparisonSignedBranchCalls.pullback (ComparisonSignedBranchImages.entries first p solved)
          a.layout images) [] endpoint.2=true := by
  obtain ⟨_,_,_,_,_,hc,hr⟩ := branch_spec h
  exact (ComparisonSignedBranchCalls.compile_correct hr world images).trans
    ((ComparisonSignedEndpoints.compileGuards_correct hc world _).trans
      (ComparisonSignedEndpoints.compile_correct _ _ _ _ _ _))

end ModalityInference.ComparisonPreparedQueries
