import ModalityInference.Proofs.ComparisonPreparedQueries
import ModalityInference.Proofs.ComparisonShapeSelectorPrefix

namespace ModalityInference.ComparisonPreparedQueries

def Separated (choices : List Alternative) (lo hi : Nat) : Prop :=
  (∀a∈choices,lo≤a.activation ∧ a.activation<hi) ∧
    ∀a∈choices,∀b∈choices,a.activation=b.activation → a=b

theorem Separated.weaken {choices : List Alternative} {lo hi lo' hi' : Nat}
    (h : Separated choices lo hi) (hl : lo'≤lo) (hh : hi≤hi') :
    Separated choices lo' hi' :=
  ⟨fun a ha=>⟨hl.trans (h.1 a ha).1,(h.1 a ha).2.trans_le hh⟩,h.2⟩

theorem Separated.append {left right : List Alternative} {lo mid hi : Nat}
    (hl : Separated left lo mid) (hr : Separated right mid hi) (hlo : lo≤mid) (hhi : mid≤hi) :
    Separated (left++right) lo hi := by
  constructor
  · intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact ⟨(hl.1 a ha).1,(hl.1 a ha).2.trans_le hhi⟩
    · exact ⟨hlo.trans (hr.1 a ha).1,(hr.1 a ha).2⟩
  · intro a ha b hb he
    rcases List.mem_append.mp ha with ha|ha <;> rcases List.mem_append.mp hb with hb|hb
    · exact hl.2 a ha b hb he
    · have ha':=(hl.1 a ha).2
      have hb':=(hr.1 b hb).1
      omega
    · have ha':=(hr.1 a ha).1
      have hb':=(hl.1 b hb).2
      omega
    · exact hr.2 a ha b hb he

private theorem bind_success {α β : Type} {r : RunResult α} {f : α → RunResult β} {b : β}
    (h : r.bind f=.success b) : ∃a,r=.success a ∧ f a=.success b := by
  cases r <;> simp_all [RunResult.bind]

theorem alternatives_separated {fuel first next : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoint : Ty × Ty} {bs : List ComparisonSelectedBases.Branch} {output : List Alternative}
    (h : alternatives fuel first p solved declared endpoint next bs=.success output) :
    Separated output next (next+bs.length) := by
  induction bs generalizing next output with
  | nil => have he : output=[] := by simpa [alternatives] using h.symm
           subst output; simp [Separated]
  | cons b bs ih =>
      obtain ⟨head,hh,hrest⟩ := bind_success h
      obtain ⟨tail,ht,he⟩ := bind_success hrest
      have he' : output=head.toList++tail := by simpa [pure] using he.symm
      subst output
      have htail:=ih ht
      cases head with
      | none =>
          simpa only [Option.toList_none,List.nil_append,List.length_cons,Nat.add_assoc] using
            htail.weaken (Nat.le_succ next) (by omega)
      | some a =>
          have ha : a.activation=next := (branch_spec hh).1
          have hhead : Separated [a] next (next+1) := by
            simp [Separated,ha]
          simpa only [Option.toList_some,List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
            hhead.append htail (by omega) (by omega)

def endpointWidth (first : Nat) (p : SchemePreparation.Prepared)
    (solved : ComparisonShapeSolver.Solved) (endpoints : List (Ty × Ty)) : Nat :=
  (endpoints.map fun endpoint=>(branches first p solved endpoint).length).sum

theorem groups_separated {fuel first next : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {declared : List ComparisonStructuralEndpoints.Pair}
    {endpoints : List (Ty × Ty)} {output : List Group}
    (h : groups fuel first p solved declared next endpoints=.success output) :
    Separated (output.flatMap Group.alternatives) next
      (next+endpointWidth first p solved endpoints) := by
  induction endpoints generalizing next output with
  | nil => have he : output=[] := by simpa [groups] using h.symm
           subst output; simp [Separated]
  | cons pair rest ih =>
      obtain ⟨choices,hc,hrest⟩ := bind_success h
      obtain ⟨tail,ht,he⟩ := bind_success hrest
      have he' : output=⟨pair,choices⟩::tail := by simpa [pure] using he.symm
      subst output
      simpa only [List.flatMap_cons,endpointWidth,List.map_cons,List.sum_cons,Nat.add_assoc] using
        (alternatives_separated hc).append (ih ht) (by omega) (by omega)

def activate (first : Nat) (base : Nat → Bool) (groups : List Group) (n : Nat) : Bool :=
  if n<first then base n else
    (groups.flatMap Group.alternatives).any fun a=>a.activation==n && a.branch.guard.eval base

theorem activate_prefix {first n : Nat} (base : Nat → Bool) (groups : List Group) (hn : n<first) :
    activate first base groups n=base n := by simp [activate,hn]

theorem activate_value {first last : Nat} {base : Nat → Bool} {groups : List Group}
    (h : Separated (groups.flatMap Group.alternatives) first last)
    {a : Alternative} (ha : a∈groups.flatMap Group.alternatives) :
    activate first base groups a.activation=a.branch.guard.eval base := by
  have hn : ¬a.activation<first := by have hh:=(h.1 a ha).1; omega
  simp only [activate,hn,ite_false]
  have he : ((groups.flatMap Group.alternatives).any
      fun b=>b.activation==a.activation && b.branch.guard.eval base)=true ↔ a.branch.guard.eval base=true := by
    simp only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq]
    constructor
    · rintro ⟨b,hb,hkey,hguard⟩
      have hb':=h.2 b hb a ha hkey
      simpa only [hb'] using hguard
    · exact fun hg=>⟨a,ha,rfl,hg⟩
  cases hx : (groups.flatMap Group.alternatives).any
      (fun b=>b.activation==a.activation && b.branch.guard.eval base) <;>
    cases hy : a.branch.guard.eval base <;> simp_all only [Bool.false_eq_true, iff_false, iff_true, not_true_eq_false]


theorem compile_activated_of_congr {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program} {base : Nat → Bool}
    (h : compile fuel first p solved=.success program)
    (hbase : (ComparisonSelectedBases.selectorFormula first p solved).eval base=true)
    (hcovered : ∀g∈program.groups,∃a∈g.alternatives,a.branch.guard.eval base=true)
    (hformula : (ComparisonSelectedBases.selectorFormula first p solved).eval
        (activate (ComparisonSelectedBases.layout first p solved).next base program.groups)=
      (ComparisonSelectedBases.selectorFormula first p solved).eval base)
    (hguards : ∀g∈program.groups,∀a∈g.alternatives,a.branch.guard.eval
        (activate (ComparisonSelectedBases.layout first p solved).next base program.groups)=
      a.branch.guard.eval base) :
    let shape:=activate (ComparisonSelectedBases.layout first p solved).next base program.groups
    CNFHolds shape program.condition ∧
      ∀g∈program.groups,∀a∈g.alternatives,shape a.activation=true →
        a.branch.guard.eval base=true := by
  have hsep:=groups_separated (compile_spec h).2.1
  have hv : ∀g∈program.groups,∀a∈g.alternatives,
      activate (ComparisonSelectedBases.layout first p solved).next base program.groups a.activation=
        a.branch.guard.eval base := by
    intro g hg a ha
    exact activate_value hsep (List.mem_flatMap.mpr ⟨g,hg,ha⟩)
  constructor
  · apply (compile_condition h _).mpr
    refine ⟨hformula.trans hbase,?_⟩
    intro g hg
    constructor
    · obtain ⟨a,ha,hguard⟩:=hcovered g hg
      exact ⟨a,ha,(hv g hg a ha).trans hguard⟩
    · intro a ha hactive
      exact (hguards g hg a ha).trans ((hv g hg a ha).symm.trans hactive)
  · intro g hg a ha hactive
    exact (hv g hg a ha).symm.trans hactive


/-- Every covered endpoint can be activated without changing the shared shape
selection. The activation choices are constants beyond the selector prefix. -/
theorem compile_activated {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program} {base : Nat → Bool}
    (h : compile fuel first p solved=.success program)
    (hbase : (ComparisonSelectedBases.selectorFormula first p solved).eval base=true)
    (hcovered : ∀g∈program.groups,∃a∈g.alternatives,a.branch.guard.eval base=true) :
    let shape:=activate (ComparisonSelectedBases.layout first p solved).next base program.groups
    CNFHolds shape program.condition ∧
      ∀g∈program.groups,∀a∈g.alternatives,shape a.activation=true →
        a.branch.guard.eval base=true := by
  have hprefix : ∀n<(ComparisonSelectedBases.layout first p solved).next,
      activate (ComparisonSelectedBases.layout first p solved).next base program.groups n=base n :=
    fun _ hn=>activate_prefix base program.groups hn
  apply compile_activated_of_congr h hbase hcovered
    (ComparisonSelectedBases.selectorFormula_prefix hprefix)
  intro g hg a ha
  have hgroups:=groups_spec (compile_spec h).2.1
  have hge : g.endpoint∈ComparisonSignedObservation.sourceEndpoints p :=
    hgroups.1 ▸ List.mem_map.mpr ⟨g,hg,rfl⟩
  obtain ⟨activation,b,hb,hbranch⟩:=hgroups.2 g hg a ha
  have he:=(branch_spec hbranch).2.1
  rw [he]
  exact source_branches_guard_prefix hge hb hprefix

theorem compile_activation {fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {program : Program} {base : Nat → Bool}
    (h : compile fuel first p solved=.success program)
    (hbase : (ComparisonSelectedBases.selectorFormula first p solved).eval base=true)
    (hcovered : ∀g∈program.groups,∃a∈g.alternatives,a.branch.guard.eval base=true) :
    ∃shape,CNFHolds shape program.condition ∧
      ∀g∈program.groups,∀a∈g.alternatives,shape a.activation=true →
        a.branch.guard.eval base=true :=
  ⟨_,compile_activated h hbase hcovered⟩

end ModalityInference.ComparisonPreparedQueries
