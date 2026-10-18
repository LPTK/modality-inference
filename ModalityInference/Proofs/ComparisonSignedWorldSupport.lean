import ModalityInference.Proofs.ComparisonWorldModeSupport

/-! Scalar atom provenance is preserved through nominal point abstraction and
world separation. Constant selectors and nominal point names do not enter
reconstructed modality expressions. -/
namespace ModalityInference.ComparisonSignedWorldSupport
open ComparisonPropagation ComparisonWorldClauses ComparisonSignedEndpoints

private theorem join_atoms {left right : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (join left right)) :
    v∈CNFPropagation.atoms left ∨ v∈CNFPropagation.atoms right := by
  have hs := join_supported (domain:=CNFPropagation.atoms left++CNFPropagation.atoms right)
    (left:=left) (right:=right)
    (fun v hv=>List.mem_append_left _ hv) (fun v hv=>List.mem_append_right _ hv)
  exact List.mem_append.mp (hs v h)

private theorem negate_atoms {cs : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (negate cs)) : v∈CNFPropagation.atoms cs := by
  induction cs with
  | nil => simp [negate,CNFPropagation.atoms] at h
  | cons c cs ih =>
    rcases join_atoms h with hl|hr
    · obtain ⟨d,hd,p,hp⟩ := CNFPropagation.mem_atoms.mp hl
      obtain ⟨⟨w,q⟩,hw,rfl⟩ := List.mem_map.mp hd
      have he : (v,p)=(w,!q) := by simpa only [List.mem_singleton] using hp
      cases he
      exact CNFPropagation.mem_atoms.mpr ⟨c,List.mem_cons_self,q,hw⟩
    · obtain ⟨d,hd,p,hp⟩ := CNFPropagation.mem_atoms.mp (ih hr)
      exact CNFPropagation.mem_atoms.mpr ⟨d,List.mem_cons_of_mem _ hd,p,hp⟩

private theorem implies_atoms {left right : CNF} {v : Nat}
    (h : v∈CNFPropagation.atoms (implies left right)) :
    v∈CNFPropagation.atoms left ∨ v∈CNFPropagation.atoms right :=
  (join_atoms h).elim (fun h=>Or.inl (negate_atoms h)) Or.inr

/-- Only nonnominal blocks require scalar input support. -/
def RawSupported (P : Nat→Prop) (decode : Nat→Nat×Nat) (cs : CNF) : Prop :=
  ∀v∈CNFPropagation.atoms cs, (decode v).1≠0 → P (decode v).2

theorem query_supported {P : Nat→Prop} {decode : Nat→Nat×Nat}
    {theory : CNF} {clauses : List CompiledClause}
    (ht : RawSupported P decode theory)
    (hc : ∀c∈clauses, RawSupported P decode [c.guard]) :
    ComparisonWorldModes.Supported P (ComparisonSignedWorlds.query decode theory clauses) := by
  intro result hr b v polarity hb hl
  obtain ⟨c,hc',hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨guard,hguard,rfl⟩ := List.mem_map.mp hr
  rcases List.mem_append.mp hl with hl|hl
  · obtain ⟨⟨u,q⟩,hu,he⟩ := List.mem_map.mp hl
    have hu' : u∈CNFPropagation.atoms (implies theory [c.guard]) :=
      CNFPropagation.mem_atoms.mpr ⟨guard,hguard,q,hu⟩
    have he1 : (ComparisonSignedWorlds.rawAtom decode u).1=b := congrArg Prod.fst he
    have he2 : (ComparisonSignedWorlds.rawAtom decode u).2=v := congrArg (Prod.fst ∘ Prod.snd) he
    have hd : (decode u).1≠0 := by
      intro hd
      simp [ComparisonSignedWorlds.rawAtom,hd] at he1
      exact hb he1.symm
    have hv : (decode u).2=v := by simpa [ComparisonSignedWorlds.rawAtom,hd] using he2
    rw [←hv]
    exact (implies_atoms hu').elim (fun h=>ht u h hd) (fun h=>hc c hc' u h hd)
  · obtain ⟨⟨call,q⟩,_,he⟩ := List.mem_map.mp hl
    exact (hb (congrArg Prod.fst he).symm).elim


private theorem source_decode {P : Nat→Prop} {decode : Nat→Nat×Nat} {u : Nat}
    (h : (decode u).1≠0 → P (decode u).2)
    (hn : (ComparisonSignedPoints.decode decode (ComparisonSignedPoints.sourceAtom u)).1≠0) :
    P (ComparisonSignedPoints.decode decode (ComparisonSignedPoints.sourceAtom u)).2 := by
  by_cases h0 : (decode u).1=0
  · simp [ComparisonSignedPoints.decode,ComparisonSignedPoints.sourceAtom,h0] at hn
  · simpa [ComparisonSignedPoints.decode,ComparisonSignedPoints.sourceAtom,h0] using h h0

theorem rename_source_supported {P : Nat→Prop} {decode : Nat→Nat×Nat} {cs : CNF}
    (h : RawSupported P decode cs) :
    RawSupported P (ComparisonSignedPoints.decode decode)
      (rename ComparisonSignedPoints.sourceAtom cs) := by
  intro v hv hn
  obtain ⟨c,hc,polarity,hp⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  obtain ⟨⟨u,q⟩,hu,he⟩ := List.mem_map.mp hp
  cases he
  exact source_decode (h u (CNFPropagation.mem_atoms.mpr ⟨d,hd,q,hu⟩)) hn

theorem pointClauses_supported {P : Nat→Prop} {decode : Nat→Nat×Nat}
    {names : List Call} {size : Nat→Nat}
    (h : ∀call∈names, ∀i<size call.name,
      (decode (ComparisonSignedObservation.routeAtom call.route
        (ComparisonStructuralLayout.basisAtom i))).1=0) :
    RawSupported P (ComparisonSignedPoints.decode decode)
      (ComparisonSignedPoints.pointClauses names size) := by
  intro v hv hn
  obtain ⟨c,hc,polarity,hp⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨call,hcall,hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' : i<size call.name := List.mem_range.mp hi
  have h0 := h call hcall i hi'
  have ho : (ComparisonSignedPoints.decode decode
      (ComparisonSignedPoints.pointAtom names call i)).1=0 := by
    simp [ComparisonSignedPoints.decode,ComparisonSignedPoints.pointAtom]
  have he : (ComparisonSignedPoints.decode decode (ComparisonSignedPoints.sourceAtom
      (ComparisonSignedObservation.routeAtom call.route (ComparisonStructuralLayout.basisAtom i)))).1=0 := by
    simp [ComparisonSignedPoints.decode,ComparisonSignedPoints.sourceAtom,h0]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hp
  all_goals rcases hp with ⟨rfl,_⟩|⟨rfl,_⟩
  all_goals exact (hn (by first | exact ho | exact he)).elim

theorem worlds_supported {P : Nat→Prop} {decode : Nat→Nat×Nat}
    {theory : CNF} {clauses : List CompiledClause} {size : Nat→Nat}
    (ht : RawSupported P decode theory)
    (hc : ∀c∈clauses, RawSupported P decode [c.guard])
    (hp : ∀call∈ComparisonSignedWorlds.calls clauses, ∀i<size call.name,
      (decode (ComparisonSignedObservation.routeAtom call.route
        (ComparisonStructuralLayout.basisAtom i))).1=0) :
    ComparisonWorldModes.Supported P
      (ComparisonSignedStrategySynthesis.worlds size decode theory clauses) := by
  apply query_supported
  · intro v hv hn
    have hv' : v∈CNFPropagation.atoms (rename ComparisonSignedPoints.sourceAtom theory) ∨
        v∈CNFPropagation.atoms
          (ComparisonSignedPoints.pointClauses (ComparisonSignedWorlds.calls clauses) size) := by
      simpa [ComparisonSignedPoints.theory,CNFPropagation.atoms] using hv
    exact hv'.elim (fun h=>rename_source_supported ht v h hn)
      (fun h=>pointClauses_supported hp v h hn)
  · intro c hcm
    obtain ⟨c,hc',rfl⟩ := List.mem_map.mp hcm
    exact rename_source_supported (hc c hc')

end ModalityInference.ComparisonSignedWorldSupport

namespace ModalityInference.ComparisonSignedEndpointQueries
open ComparisonSignedEndpoints ComparisonSignedWorldSupport

/-- A source's scalar coordinates and nominal point equations have exact
input provenance. Shape activation constants are outside this raw namespace. -/
structure Source.ScalarSupported (source : Source) (size : Nat→Nat) (P : Nat→Prop) : Prop where
  theory : RawSupported P source.decode source.theory
  guards : ∀c∈source.clauses, RawSupported P source.decode [c.guard]
  points : ∀call∈ComparisonSignedWorlds.calls source.clauses, ∀i<size call.name,
    (source.decode (ComparisonSignedObservation.routeAtom call.route
      (ComparisonStructuralLayout.basisAtom i))).1=0

theorem Source.worlds_supported {source : Source} {size : Nat→Nat} {P : Nat→Prop}
    (h : source.ScalarSupported size P) : ComparisonWorldModes.Supported P (source.worlds size) :=
  ComparisonSignedWorldSupport.worlds_supported h.theory h.guards h.points

end ModalityInference.ComparisonSignedEndpointQueries

namespace ModalityInference.ComparisonGuardedEndpointQueries

/-- Guarded sources share the same scalar atom names; activation introduces
only constant selector atoms, which are removed before mode reification. -/
theorem entries_supported {sources : List Source} {size : Nat→Nat} {P : Nat→Prop}
    (h : ∀source∈sources, source.source.ScalarSupported size P) :
    ComparisonWorldModes.Supported P (ComparisonGuardedWorldModes.clauses (entries size sources)) := by
  intro c hc b v polarity hb hl
  obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hc
  obtain ⟨source,hs,he⟩ := List.mem_flatMap.mp he
  obtain ⟨d,hd,heq⟩ := List.mem_map.mp he
  cases heq
  exact ComparisonSignedEndpointQueries.Source.worlds_supported (h source hs) d hd b v polarity hb hl

theorem assembled_mode_support {p : SchemePreparation.Prepared}
    {input : ComparisonSignedSynthesis.Input} {sources : List Source}
    {selectors : Nat→Bool} {action : Substitution} {P : ModVar→Prop}
    (ha : ComparisonPreparedScalar.assemble p
      (modes ModalSynthesis.locality (ComparisonPreparedScalar.flexibleAtoms p)
        input sources selectors)=some action)
    (hs : ∀source∈sources, source.source.ScalarSupported
      (fun n=>(input.bases n).length) (fun i=>P (SymbolicModes.atomVariable i)))
    {v w : ModVar} (hv : P v) (hw : w∈(action.mode v).vars) : P w :=
  ComparisonPreparedScalar.assemble_world_supported ha (entries_supported hs) hv hw

end ModalityInference.ComparisonGuardedEndpointQueries
