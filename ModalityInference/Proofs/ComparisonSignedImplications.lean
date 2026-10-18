import ModalityInference.Proofs.ComparisonSignedGraph
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Prod

/-! Guarded binary clauses have one shared assignment exactly when their
signed implication graph is consistent. Clause instances may quantify any
collection of input worlds. Their guards and image arguments are fixed together
when the graph is formed, so reachability never forgets a shared strategy. -/
namespace ModalityInference.ComparisonSignedImplications

open ComparisonSignedGraph

abbrev Literal (α : Type*) := α ×ₗ Bool

def complement {α} (v : Literal α) : Literal α := toLex ((ofLex v).1,!(ofLex v).2)

theorem complement_involutive {α} : Function.Involutive (@complement α) := by
  rintro ⟨a,p⟩
  change (a,!!p)=(a,p)
  simp

def read {α} (value : α → Bool) (v : Literal α) : Bool := value (ofLex v).1 == (ofLex v).2

theorem read_complement {α} (value : α → Bool) (v : Literal α) :
    read value (complement v)=!read value v := by
  cases hv : value (ofLex v).1 <;> cases hp : (ofLex v).2 <;> simp [read,complement,hv,hp]

structure System (α ι : Type*) where
  guard : ι → Prop
  left : ι → Literal α
  right : ι → Literal α

def System.Valid {α ι} (s : System α ι) (value : α → Bool) : Prop :=
  ∀i,s.guard i ∨ read value (s.left i)=true ∨ read value (s.right i)=true

def System.graph {α ι} (s : System α ι) : Graph (Literal α) where
  complement := complement
  involutive := complement_involutive
  edge a b := ∃i,¬s.guard i ∧
    ((a=complement (s.left i) ∧ b=s.right i) ∨ (a=complement (s.right i) ∧ b=s.left i))
  contrapose := by
    rintro a b ⟨i,hg,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
    · exact ⟨i,hg,Or.inr ⟨rfl,complement_involutive _⟩⟩
    · exact ⟨i,hg,Or.inl ⟨rfl,complement_involutive _⟩⟩

theorem System.Valid.model {α ι} {s : System α ι} {value} (hv : s.Valid value) :
    s.graph.Model (read value) where
  complement := read_complement value
  edge := by
    rintro a b ⟨i,hg,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
    all_goals
      apply Bool.le_iff_imp.mpr
      intro ha
      have hi := (hv i).resolve_left hg
      rw [read_complement] at ha
      rcases hi with hi|hi
      all_goals first | exact hi | (rw [hi] at ha; cases ha)

def System.assignment {α ι} (_s : System α ι) (value : Literal α → Bool) : α → Bool :=
  fun a => value (toLex (a,true))

theorem System.Model.read_assignment {α ι} {s : System α ι} {value}
    (hv : s.graph.Model value) (v : Literal α) :
    read (s.assignment value) v=value v := by
  obtain ⟨a,p⟩ := v
  cases p
  · have h := hv.complement (toLex (a,true))
    change value (toLex (a,false))= !value (toLex (a,true)) at h
    change (value (toLex (a,true)) == false)=value (toLex (a,false))
    rw [h]
    cases value (toLex (a,true)) <;> rfl
  · change (value (toLex (a,true)) == true)=value (toLex (a,true))
    cases value (toLex (a,true)) <;> rfl

theorem System.Model.valid {α ι} {s : System α ι} {value}
    (hv : s.graph.Model value) : s.Valid (s.assignment value) := by
  intro i
  classical
  by_cases hg : s.guard i
  · exact .inl hg
  right
  simp only [System.Model.read_assignment hv]
  by_cases hl : value (s.left i)=true
  · exact .inl hl
  right
  have hm := hv.edge (show s.graph.edge (complement (s.left i)) (s.right i) from
    ⟨i,hg,Or.inl ⟨rfl,rfl⟩⟩)
  apply Bool.le_iff_imp.mp hm
  simpa only [System.graph] using (hv.complement (s.left i)).trans
    (show (!value (s.left i))=true by simp [Bool.eq_false_iff.mpr hl])

theorem System.valid_iff {α ι} [Fintype α] [LinearOrder α] (s : System α ι) :
    (∃value,s.Valid value) ↔ s.graph.Consistent := by
  constructor
  · rintro ⟨value,hv⟩
    exact hv.model.consistent
  · intro hc
    exact ⟨s.assignment s.graph.canonical,System.Model.valid (s.graph.canonical_model hc)⟩

end ModalityInference.ComparisonSignedImplications
