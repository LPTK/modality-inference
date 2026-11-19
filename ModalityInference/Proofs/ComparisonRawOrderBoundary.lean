import ModalityInference.Proofs.ComparisonCyclicDeclaredWitness
import ModalityInference.Proofs.ComparisonObserverMachine
import ModalityInference.Proofs.ComparisonEliminationSoundness

/-! Two public schemes admit a constant-preserving Boolean assignment for every
observer. Two ordered observer states force opposite values of the same image,
which rules out every positive internal type. -/
namespace ModalityInference.ComparisonRawOrderBoundary

open ComparisonObserverMachine

def B : Ty := .var (.rigid 0)
def D : Ty := .var (.rigid 1)
def A : Ty := .var (.rigid 2)
def X : Ty := .var (.flex 0)
def P (a : Ty) : Ty := .prod a a
def S (a : Ty) : Ty := .sum a a

def source : Scheme :=
  { typeParams := [0], bounds := [.sub D (P X), .sub (S X) B], body := .unit }

def target : Scheme :=
  { bounds := [.sub D (P D), .sub (P A) (P B), .sub (S B) B, .sub (S D) (S A)],
    body := .unit }

def classifier (b d a : Bool) := b || (d && !a)

theorem classifier_constant (x : Bool) : classifier x x x = x := by cases x <;> rfl

theorem classifier_at_prod : ∀ b d a : Bool, a ≤ b → d ≤ classifier b d a := by decide
theorem classifier_at_sum : ∀ b d a : Bool, d ≤ a → classifier b d a ≤ b := by decide

def raw {State} (nodes : State → Node State) (i : State) : Bool :=
  classifier ((nodes i).atom (.rigid 0)) ((nodes i).atom (.rigid 1)) ((nodes i).atom (.rigid 2))

theorem raw_solves {State} (nodes : State → Node State)
    (h : BoundsHold target.bounds.assumptions nodes) (i : State) :
    (nodes i).atom (.rigid 1) ≤ raw nodes ((nodes i).branch .prod).next ∧
      raw nodes ((nodes i).branch .sum).next ≤ (nodes i).atom (.rigid 0) := by
  have hd := h i D (P D) (by decide)
  have hab := h i (P A) (P B) (by decide)
  have hb := h i (S B) B (by decide)
  have hda := h i (S D) (S A) (by decide)
  simp only [P, S, A, B, D, CompareTy.ofTy, value, ite_self] at hd hab hb hda
  exact ⟨hd.trans (classifier_at_prod _ _ _ hab), (classifier_at_sum _ _ _ hda).trans hb⟩

def nodes (i : Bool) : Node Bool where
  atom v := if v = .rigid 2 then i else decide (v = .rigid 1)
  unitValue := false
  creditValue := false
  action _ x := x
  branch k := ⟨false, decide (k = .sum)⟩
  range _ := true

theorem ordered (t : CompareTy) : value nodes t false ≤ value nodes t true := by
  induction t with
  | var v => by_cases h : v = .rigid 2 <;> simp [value, nodes, h]
  | unit | credit | prod | sum | fn => exact le_rfl
  | modal _ _ ih => exact ih
  | join _ _ hl hr => exact sup_le_sup hl hr
  | meet _ _ hl hr => exact inf_le_inf hl hr

theorem nodes_valid : Certified target.bounds.assumptions nodes := by
  constructor
  · constructor
    · exact fun _ _ _ => monotone_id
    · intros; rfl
    · intros; rfl
    · intros; simp [nodes]
    · intros; simp [nodes]
    · intros; exact le_rfl
  · constructor <;> intros <;> rfl
  · constructor
    · intros; rfl
    · intros; exact le_rfl
  · intro i a b hab
    change Constraint.sub a b ∈ [.sub D (P D), .sub (P A) (P B), .sub (S B) B, .sub (S D) (S A)] at hab
    simp only [List.mem_cons, List.not_mem_nil, or_false, Constraint.sub.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases i <;> decide

theorem not_admissible : ¬ AlgebraSubsumesUnder [] source target := by
  rintro ⟨σ, _, _, _, _, h, _⟩
  let t := σ.type (.flex 0)
  have hp : AlgebraEntails target.bounds.assumptions
      (.sub (.var (.rigid 1)) (.prod t t)) := h _ (List.mem_cons_self)
  have hs : AlgebraEntails target.bounds.assumptions
      (.sub (.sum t t) (.var (.rigid 0))) := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have leAt {a b : CompareTy} (hab : AlgebraEntails target.bounds.assumptions (.sub a b)) :=
    subtype_mono nodes_valid.modal nodes_valid.range nodes_valid.coherent nodes_valid.bounds
      (Bounds.assumptions_typeBoundsDefined _) hab.2.1 hab.2.2 hab.1 false
  have hp' : true ≤ value nodes t false := leAt hp
  have hs' : value nodes t true ≤ false := leAt hs
  exact (by decide : ¬ true ≤ false) (hp'.trans ((ordered t).trans hs'))

theorem no_finite_shape_model : ¬ ∃ ρ, ComparisonShape.Models target.bounds.assumptions ρ := by
  rintro ⟨ρ, hρ⟩
  have h := hρ (.var (.rigid 1), .prod (.var (.rigid 1)) (.var (.rigid 1))) (by decide)
  have hs := congrArg ComparisonShapeSolver.size h
  simp only [ComparisonShape.subst, ComparisonShapeSolver.size] at hs
  omega

end ModalityInference.ComparisonRawOrderBoundary
