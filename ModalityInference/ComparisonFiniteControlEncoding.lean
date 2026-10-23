import ModalityInference.ComparisonControlForms
import ModalityInference.ScalarDecision
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Fintype.EquivFin

/-! A finite executable presentation of total scalar controls. Its reference
family is filtered by symbolic equivalence; scalar checks do not enumerate
valuations. This presentation supports finite certificates, not witness search. -/
namespace ModalityInference.ComparisonFiniteControlEncoding

def equivalent (Δ : Bounds) (m n : ModExpr) : Bool :=
  ScalarDecision.submode Δ m n && ScalarDecision.submode Δ n m

def labels (Δ : Bounds) (names : List ModVar) : List ModExpr :=
  (ComparisonControlForms.representatives names).pwFilter (fun m n => equivalent Δ m n = false)

private theorem truthForms_nonempty (is : List Nat) :
    ∃ f, f ∈ ComparisonControlForms.truthForms is := by
  induction is with
  | nil => exact ⟨.const false,by simp [ComparisonControlForms.truthForms]⟩
  | cons i is ih =>
    obtain ⟨f,hf⟩ := ih
    exact ⟨_,List.mem_flatMap.mpr ⟨f,hf,List.mem_map.mpr ⟨f,hf,rfl⟩⟩⟩

private theorem filter_nonempty {α : Type} (r : α → α → Prop) [DecidableRel r]
    {xs : List α} (hxs : xs ≠ []) : xs.pwFilter r ≠ [] := by
  cases xs with
  | nil => exact False.elim (hxs rfl)
  | cons a xs =>
    by_cases h : ∀ b ∈ xs.pwFilter r, r a b
    · rw [List.pwFilter_cons_of_pos h]
      exact List.cons_ne_nil _ _
    · rw [List.pwFilter_cons_of_neg h]
      intro he
      exact h (by simp [he])

theorem labels_nonempty (Δ : Bounds) (names : List ModVar) : labels Δ names ≠ [] := by
  obtain ⟨l,hl⟩ := truthForms_nonempty (ComparisonControlForms.channelAtoms .locality names)
  obtain ⟨a,ha⟩ := truthForms_nonempty (ComparisonControlForms.channelAtoms .affinity names)
  obtain ⟨u,hu⟩ := truthForms_nonempty (ComparisonControlForms.channelAtoms .lower names)
  exact filter_nonempty _ (List.ne_nil_of_mem (List.mem_flatMap.mpr
    ⟨l,hl,List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨u,hu,rfl⟩⟩⟩))

structure Code (Δ : Bounds) (names : List ModVar) where
  index : Fin (labels Δ names).length
  deriving DecidableEq, Repr

instance (Δ : Bounds) (names : List ModVar) : Fintype (Code Δ names) :=
  Fintype.ofEquiv (Fin (labels Δ names).length)
    ⟨Code.mk,Code.index,fun _ => rfl,fun x => by cases x; rfl⟩

def expression {Δ : Bounds} {names : List ModVar} (c : Code Δ names) : ModExpr :=
  (labels Δ names)[c.index]

/-- The first equivalent representative is used whenever one exists.
The fallback is unreachable for supported labels defined under `Δ`. -/
def lookup (Δ : Bounds) (names : List ModVar) (m : ModExpr) : Code Δ names :=
  let i := (labels Δ names).findIdx (equivalent Δ m)
  ⟨if hi : i < (labels Δ names).length then ⟨i,hi⟩
    else ⟨0,List.length_pos_iff.mpr (labels_nonempty Δ names)⟩⟩

def order {Δ : Bounds} {names : List ModVar} (m n : Code Δ names) : Bool :=
  ScalarDecision.submode Δ (expression m) (expression n)

instance {Δ : Bounds} {names : List ModVar} : LE (Code Δ names) :=
  ⟨fun m n => order m n = true⟩

instance {Δ : Bounds} {names : List ModVar} : DecidableLE (Code Δ names) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

instance {Δ : Bounds} {names : List ModVar} : One (Code Δ names) :=
  ⟨lookup Δ names .epsilon⟩

instance {Δ : Bounds} {names : List ModVar} : Mul (Code Δ names) :=
  ⟨fun m n => lookup Δ names (.compose (expression m) (expression n))⟩

def top (Δ : Bounds) (names : List ModVar) : Code Δ names := lookup Δ names .top

def restrict (names : List ModVar) (v : ModVar) : ModExpr :=
  if v ∈ names.toFinset then .var v else .epsilon

/-- Names outside the finite boundary are replaced by the identity label. -/
def project (Δ : Bounds) (names : List ModVar) (m : ModExpr) : Code Δ names :=
  lookup Δ names (m.subst (restrict names))

end ModalityInference.ComparisonFiniteControlEncoding
