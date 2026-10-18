import ModalityInference.ComparisonSignedEdges
import ModalityInference.Proofs.ComparisonSignedCanonical
import ModalityInference.Proofs.ComparisonSignedEndpoints

/-! Observer projection and finite state-point equalities retain one shared
parameter world. The equalities stay inside the guarded relation. -/
namespace ModalityInference.ComparisonSignedEdges
open ComparisonPropagation ComparisonSignedRelations ComparisonSignedEndpoints

/-- One observer input varies; every retained parameter stays shared. -/
def decoded (decode : Nat → Sum Nat Nat) (parameters observer : Nat → Bool) (v : Nat) : Bool :=
  match decode v with
  | .inl p => parameters p
  | .inr w => observer w

def extended (parameters input output observer : Nat → Bool) (v : Nat) : Bool :=
  if v%4=0 then input (v/4) else if v%4=1 then output (v/4)
  else if v%4=2 then parameters (v/4) else observer (v/4)

@[simp] theorem extended_input (p a b w : Nat → Bool) (i : Nat) :
    extended p a b w (4*i)=a i := by simp [extended]

@[simp] theorem extended_output (p a b w : Nat → Bool) (i : Nat) :
    extended p a b w (4*i+1)=b i := by
  simp [extended]
  congr 1
  omega

@[simp] theorem extended_parameter (p a b w : Nat → Bool) (i : Nat) :
    extended p a b w (4*i+2)=p i := by
  simp [extended]
  congr 1
  omega

@[simp] theorem extended_observer (p a b w : Nat → Bool) (i : Nat) :
    extended p a b w (4*i+3)=w i := by
  simp [extended]
  congr 1
  omega

@[simp] theorem extended_world (decode : Nat → Sum Nat Nat) (p a b w : Nat → Bool) (v : Nat) :
    extended p a b w (worldAtom decode v)=decoded decode p w v := by
  cases hd : decode v <;> simp [worldAtom,decoded,hd]

@[simp] theorem extended_tuple (p a b w : Nat → Bool) (v : Nat) :
    extended p a b w (tupleAtom v)=ComparisonSignedRelations.value p a b v := by
  have hv : v%3<3 := Nat.mod_lt _ (by omega)
  rcases (by omega : v%3=0 ∨ v%3=1 ∨ v%3=2) with h|h|h
  all_goals simp [tupleAtom,ComparisonSignedRelations.value,h]

theorem extended_retained (p a b w : Nat → Bool) {v : Nat} (h : v%4≠3) :
    extended p a b w v=ComparisonSignedRelations.value p a b (retained v) := by
  have hv : v%4<4 := Nat.mod_lt _ (by omega)
  rcases (by omega : v%4=0 ∨ v%4=1 ∨ v%4=2) with h|h|h
  all_goals simp [retained,extended,ComparisonSignedRelations.value,h]
  all_goals congr 1
  all_goals omega

theorem projectObservers_correct (p a b : Nat → Bool) (cs : CNF) :
    Holds p (projectObservers cs) a b ↔ ∃w,CNFHolds (extended p a b w) cs := by
  rw [Holds,projectObservers,rename_correct,project_complete]
  constructor
  · rintro ⟨world,hw,hcs⟩
    let w := fun i=>world (4*i+3)
    have he : world=extended p a b w := by
      funext v
      by_cases hv : v%4=3
      · have he : 4*(v/4)+3=v := by omega
        simp only [extended,hv,show ¬3=0 by decide,show ¬3=1 by decide,
          show ¬3=2 by decide,if_false]
        exact (congrArg world he).symm
      · rw [extended_retained p a b w hv]
        exact hw v (by simp [observerAtoms,hv])
    exact ⟨w,by simpa only [he] using hcs⟩
  · rintro ⟨w,hw⟩
    let world := fun v => if v∈observerAtoms cs then extended p a b w v
      else ComparisonSignedRelations.value p a b (retained v)
    refine ⟨world,?_,?_⟩
    · intro v hv
      exact if_neg hv
    · apply (CNFPropagation.holds_congr (σ:=extended p a b w) (τ:=world) ?_).mp hw
      intro v hv
      by_cases ho : v%4=3
      · have hm : v∈observerAtoms cs := by simp [observerAtoms,hv,ho]
        simp only [world,if_pos hm]
      · have hm : v∉observerAtoms cs := by simp [observerAtoms,ho]
        simp only [world,if_neg hm]
        exact extended_retained p a b w ho

def patternValue (world : Nat → Bool) (values : List (Sum Bool Nat)) (i : Nat) : Bool :=
  match values[i]?.getD (.inl false) with
  | .inl b => b
  | .inr v => world v

theorem matchCoordinate_correct (decode : Nat → Sum Nat Nat) (v : Nat)
    (coordinate : Sum Bool Nat) (world : Nat → Bool) :
    CNFHolds world (matchCoordinate decode v coordinate) ↔
      world v=(match coordinate with | .inl b=>b | .inr w=>world (worldAtom decode w)) := by
  cases coordinate with
  | inl b => simp [matchCoordinate,CNFHolds,ClauseHolds]
  | inr w =>
    cases hv : world v <;> cases hw : world (worldAtom decode w) <;>
      simp [matchCoordinate,CNFHolds,ClauseHolds,exists_or,hv,hw]

theorem matchPattern_correct (width lane : Nat) (decode : Nat → Sum Nat Nat)
    (values : List (Sum Bool Nat)) (world : Nat → Bool) :
    CNFHolds world (matchPattern width lane decode values) ↔
      ∀i<width,world (4*i+lane)=patternValue (world∘worldAtom decode) values i := by
  simp only [matchPattern,CNFHolds,List.forall_mem_flatMap,List.mem_range]
  apply forall_congr' fun i=>imp_congr_right fun _=>?_
  exact matchCoordinate_correct decode (4*i+lane) _ world

theorem directed_correct (width : Nat) (decode : Nat → Sum Nat Nat)
    (left right : List (Sum Bool Nat)) (p a b w : Nat → Bool) :
    CNFHolds (extended p a b w) (directed width decode left right) ↔
      Same width a (patternValue (decoded decode p w) left) ∧
      Same width b (patternValue (decoded decode p w) right) := by
  rw [directed,cnfHolds_append,matchPattern_correct,matchPattern_correct]
  simp only [Nat.add_zero,extended_input,extended_output,Function.comp_def,extended_world,Same]

theorem guarded_correct (decode : Nat → Sum Nat Nat) (theory : CNF)
    (guard : ModalityInference.Clause) (body : CNF) (p a b : Nat → Bool) :
    Holds p (guarded decode theory guard body) a b ↔
      ∃w,CNFHolds (decoded decode p w) theory ∧ ¬ClauseHolds (decoded decode p w) guard ∧
        CNFHolds (extended p a b w) body := by
  rw [guarded,projectObservers_correct]
  apply exists_congr fun w=>?_
  rw [cnfHolds_append,rename_correct]
  simp only [Function.comp_def,extended_world,cnfHolds_append,negateClause_correct]
  tauto

end ModalityInference.ComparisonSignedEdges
