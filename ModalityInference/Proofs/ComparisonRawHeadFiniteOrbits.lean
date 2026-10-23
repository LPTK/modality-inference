import ModalityInference.Proofs.ComparisonFiniteControls
import Mathlib.Data.Fintype.Prod

/-! A finite family of shaped raw anchors has a finite interface orbit under
the total controls. The order is the original comparison order, including
all comparisons through partial bounds. -/
namespace ModalityInference.ComparisonRawHeadFiniteOrbits

open ComparisonFiniteControls

noncomputable section

structure Boundary (Δ : Bounds) where
  heads : List CompareTy
  shaped : ∀ a ∈ heads, a.WellShaped Δ

def Boundary.ofRaw (Δ : Bounds) (heads : List Ty) : Boundary Δ where
  heads := heads.map CompareTy.ofTy
  shaped := by
    intro a ha
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp ha
    exact CompareTy.wellShaped_ofTy b Δ

structure Point {Δ : Bounds} (B : Boundary Δ) (names : List ModVar) where
  head : Fin B.heads.length
  control : Control Δ names

namespace Point

variable {Δ : Bounds} {B : Boundary Δ} {names : List ModVar}

@[ext] theorem ext {p q : Point B names} (hh : p.head = q.head) (hc : p.control = q.control) : p = q := by
  cases p; cases q; cases hh; cases hc; rfl

instance : Finite (Point B names) := by
  letI := Fintype.ofFinite (Control Δ names)
  exact Finite.of_injective (fun p : Point B names => (p.head,p.control))
    (fun _ _ h => ext (congrArg Prod.fst h) (congrArg Prod.snd h))

instance : Fintype (Point B names) := Fintype.ofFinite _

def term (p : Point B names) : CompareTy := .modal B.heads[p.head] (expression p.control)

theorem shaped (p : Point B names) : p.term.WellShaped Δ := by
  change B.heads[p.head].WellShaped Δ
  exact B.shaped _ (List.getElem_mem p.head.isLt)

instance : Preorder (Point B names) where
  le p q := AlgebraSubtype Δ p.term q.term
  le_refl p := .refl p.shaped
  le_trans _ _ _ := AlgebraSubtype.trans

theorem le_iff (p q : Point B names) : p ≤ q ↔ AlgebraSubtype Δ p.term q.term := Iff.rfl

def act (m : Control Δ names) (p : Point B names) : Point B names := ⟨p.head,p.control * m⟩

@[simp] theorem act_one (p : Point B names) : act 1 p = p := by
  apply Point.ext
  · rfl
  · exact mul_one _

theorem act_mul (m n : Control Δ names) (p : Point B names) :
    act m (act n p) = act (n * m) p := by
  apply Point.ext
  · rfl
  · exact mul_assoc _ _ _

/-- The action changes only the total trailing control. The head remains
literal, even when it contains partial annotations. -/
theorem term_act (m : Control Δ names) (p : Point B names) :
    AlgebraSubtype Δ (.modal p.term (expression m)) (act m p).term ∧
      AlgebraSubtype Δ (act m p).term (.modal p.term (expression m)) := by
  have hh := B.shaped B.heads[p.head] (List.getElem_mem p.head.isLt)
  have he := expression_mul p.control m
  exact ⟨(AlgebraSubtype.shaped (.compose hh)).trans ((AlgebraSubtype.refl hh).congr he.2),
    ((AlgebraSubtype.refl hh).congr he.1).trans (.shaped (.composeRev hh))⟩

theorem act_mono (m : Control Δ names) : Monotone (act m : Point B names → Point B names) := by
  intro p q hpq
  exact (term_act m p).2.trans
    ((hpq.congr (.refl (expression_defined m))).trans (term_act m q).1)

theorem act_index_mono (p : Point B names) : Monotone (fun m => act m p) := by
  intro m n hmn
  exact (AlgebraSubtype.refl (B.shaped B.heads[p.head] (List.getElem_mem p.head.isLt))).congr
    ((le_iff_submode (p.control * m) (p.control * n)).mp (mul_mono p.control hmn))

def action (m : Control Δ names) : Point B names →o Point B names := ⟨act m,act_mono m⟩

def base (B : Boundary Δ) (names : List ModVar) (i : Fin B.heads.length) : Point B names := ⟨i,1⟩

theorem base_equivalent (i : Fin B.heads.length) :
    AlgebraSubtype Δ (base B names i).term B.heads[i] ∧
      AlgebraSubtype Δ B.heads[i] (base B names i).term := by
  have hh := B.shaped B.heads[i] (List.getElem_mem i.isLt)
  exact ⟨((AlgebraSubtype.refl hh).congr expression_one.1).trans (.shaped (.identity hh)),
    (AlgebraSubtype.shaped (.identityRev hh)).trans ((AlgebraSubtype.refl hh).congr expression_one.2)⟩

theorem base_le_iff (i j : Fin B.heads.length) :
    base B names i ≤ base B names j ↔ AlgebraSubtype Δ B.heads[i] B.heads[j] := by
  constructor
  · intro h
    exact (base_equivalent (names := names) i).2.trans
      (AlgebraSubtype.trans h (base_equivalent (names := names) j).1)
  · intro h
    exact (base_equivalent (names := names) i).1.trans
      (h.trans (base_equivalent (names := names) j).2)

theorem encoded_equivalent (i : Fin B.heads.length) (m : ModExpr)
    (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names.toFinset) :
    let p : Point B names := ⟨i,encode m hm hs⟩
    AlgebraSubtype Δ p.term (.modal B.heads[i] m) ∧
      AlgebraSubtype Δ (.modal B.heads[i] m) p.term := by
  have hh := B.shaped B.heads[i] (List.getElem_mem i.isLt)
  exact ⟨(AlgebraSubtype.refl hh).congr (expression_encode m hm hs).1,
    (AlgebraSubtype.refl hh).congr (expression_encode m hm hs).2⟩

end Point
end
end ModalityInference.ComparisonRawHeadFiniteOrbits
