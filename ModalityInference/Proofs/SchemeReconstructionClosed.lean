import ModalityInference.Proofs.SchemeReconstruction

/-! Closed quantified schemes can require an intermediate type that the current
type grammar cannot express. Modal wrappers do not remove this obstruction. -/
namespace ModalityInference.SchemeReconstructionClosed

inductive Shape where
  | var : TypeVar → Shape
  | unit : Shape
  | prod : Shape → Shape → Shape
  | sum : Shape → Shape → Shape
  | fn : Shape → Shape → Shape
  | credit : Shape

/-- Erase modalities and identify fresh target skolems with the four rigid vertices. -/
def erase : Ty → Shape
  | .var (.rigid n) => .var (.rigid (n - 4))
  | .var (.flex n) => .var (.flex n)
  | .unit => .unit
  | .prod a b => .prod (erase a) (erase b)
  | .sum a b => .sum (erase a) (erase b)
  | .fn a b => .fn (erase a) (erase b)
  | .credit => .credit
  | .modal a _ => erase a

def Rel : Shape → Shape → Prop
  | .var v, .var w => SchemeReconstruction.baseReachable (some v) (some w)
  | .unit, .unit | .credit, .credit => True
  | .prod a b, .prod c d | .sum a b, .sum c d => Rel a c ∧ Rel b d
  | .fn a b, .fn c d => Rel c a ∧ Rel b d
  | _, _ => False
termination_by a b => sizeOf a + sizeOf b
decreasing_by all_goals simp_wf; omega

theorem rel_refl (a : Shape) : Rel a a := by
  induction a <;> simp_all [Rel, SchemeReconstruction.baseReachable]

theorem rel_trans {a b c : Shape} (hab : Rel a b) (hbc : Rel b c) : Rel a c := by
  induction b generalizing a c
  all_goals cases a <;> cases c <;> simp only [Rel] at hab hbc ⊢
  all_goals first
    | exact SchemeReconstruction.baseReachable_trans hab hbc
    | trivial
    | rcases hab with ⟨h1, h2⟩; rcases hbc with ⟨h3, h4⟩
      constructor <;> solve_by_elim

def bounds : Bounds :=
  [.sub (.var (.rigid 4)) (.var (.rigid 6)),
   .sub (.var (.rigid 4)) (.var (.rigid 7)),
   .sub (.var (.rigid 5)) (.var (.rigid 6)),
   .sub (.var (.rigid 5)) (.var (.rigid 7))]

/-- Structural erasure validates every subtype rule, including transitivity. -/
theorem subtype_rel {a b} (h : Subtype bounds a b) : Rel (erase a) (erase b) := by
  induction h
  case refl => exact rel_refl _
  case trans _ _ _ _ _ ih ih' => exact rel_trans ih ih'
  case bound h =>
    simp [bounds] at h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals simp [erase, Rel, SchemeReconstruction.baseReachable]
  case congr _ _ ih => exact ih
  case prod _ _ ih ih' | sum _ _ ih ih' | fn _ _ _ ih ih' =>
    simpa only [erase, Rel] using And.intro ih ih'
  all_goals exact rel_refl _

theorem no_shape_interpolant (t : Shape)
    (ha : Rel (.var (.rigid 0)) t) (hb : Rel (.var (.rigid 1)) t)
    (hc : Rel t (.var (.rigid 2))) (hd : Rel t (.var (.rigid 3))) : False := by
  cases t <;> simp only [Rel] at ha hb hc hd
  rcases ha with he | ⟨_, he | he⟩
  · simp [SchemeReconstruction.baseReachable, ← he] at hb
  · simp [SchemeReconstruction.baseReachable, he] at hd
  · simp [SchemeReconstruction.baseReachable, he] at hc

def source : Scheme :=
  {typeParams := [0], body :=
    .fn (.var (.flex 0)) (.fn (.var (.flex 0)) (.prod (.var (.flex 0)) (.var (.flex 0))))}

def target : Scheme :=
  {typeParams := [0,1,2,3], bounds :=
    [.sub (.var (.flex 0)) (.var (.flex 2)), .sub (.var (.flex 0)) (.var (.flex 3)),
     .sub (.var (.flex 1)) (.var (.flex 2)), .sub (.var (.flex 1)) (.var (.flex 3))],
   body := .fn (.var (.flex 0)) (.fn (.var (.flex 1)) (.prod (.var (.flex 2)) (.var (.flex 3))))}

/-- Contravariant inputs and covariant outputs require one nonexistent interpolant. -/
theorem closed_no_subsumes : ¬ Subsumes [] source target := by
  rintro ⟨σ, _, _, ht⟩
  change Subtype bounds
    (.fn (σ.type (.flex 0)) (.fn (σ.type (.flex 0))
      (.prod (σ.type (.flex 0)) (σ.type (.flex 0)))))
    (.fn (.var (.rigid 4)) (.fn (.var (.rigid 5))
      (.prod (.var (.rigid 6)) (.var (.rigid 7))))) at ht
  have hh := subtype_rel ht
  simp only [erase, Rel, Nat.reduceSub] at hh
  exact no_shape_interpolant _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2

theorem closed_domains : source.freeTypes = ∅ ∧ source.freeModes = ∅ ∧
    target.freeTypes = ∅ ∧ target.freeModes = ∅ := by decide

end ModalityInference.SchemeReconstructionClosed
