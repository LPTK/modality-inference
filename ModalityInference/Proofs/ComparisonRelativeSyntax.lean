import ModalityInference.Proofs.ComparisonRelativeControlMap
import ModalityInference.Proofs.ComparisonRelativeCoordinates

/-! Finite-coordinate syntax interpretation. Partial prefixes remain exact
syntax, and products and sums always use their sparse table extensions.
Frozen lookup defaults to bottom only at leaves, functions, and lattice heads. -/
namespace ModalityInference.ComparisonRelativeSyntax

open ComparisonRelativeCoordinates ComparisonRelativeTables ComparisonRawCarrierSuffix

noncomputable section
attribute [local instance] Classical.propDecidable

structure Model (Δ : Bounds) (M A O : Type*) [PartialOrder M] [CommMonoid M]
    (embed : A → O → Bool) where
  mul_mono : ∀ m : M, Monotone (m * ·)
  prodTable : Option ModExpr → IndexedTable embed M false false
  prod_order : ∀ p {m n}, m ≤ n → (prodTable p).le m n
  sumTable : Option ModExpr → IndexedTable embed M false false
  sum_order : ∀ p {m n}, m ≤ n → (sumTable p).le m n
  fnTable : IndexedTable embed M true false
  fn_order : ∀ {m n}, m ≤ n → fnTable.le m n
  fn_post : ∀ {m n}, fnTable.le m n → ∀ r, fnTable.le (m * r) (n * r)
  controls : ControlMap Δ M fnTable.le
  atom : TypeVar → Coordinates M (O → Bool)
  unit : Coordinates M (O → Bool)
  credit : Coordinates M (O → Bool)
  frozen : List (CompareTy × Coordinates M (O → Bool))

namespace Model

variable {Δ : Bounds} {M A O : Type*} [PartialOrder M] [CommMonoid M]
  {embed : A → O → Bool} (S : Model Δ M A O embed)

def frozenValue (a : CompareTy) : Coordinates M (O → Bool) :=
  ((S.frozen.find? (fun row => decide (row.1 = a))).map Prod.snd).getD ⊥

theorem frozenValue_missing {a : CompareTy} (h : ∀ row ∈ S.frozen, row.1 ≠ a) :
    S.frozenValue a = ⊥ := by
  have hn : S.frozen.find? (fun row => decide (row.1 = a)) = none := by
    apply List.find?_eq_none.mpr
    intro row hr
    simpa only [Bool.not_eq_true, decide_eq_false_iff_not] using h row hr
  simp only [frozenValue, hn, Option.map_none, Option.getD_none]

def denote (S : Model Δ M A O embed) : CompareTy → Option ModExpr → Coordinates M (O → Bool)
  | .modal a m, none =>
      shift S.mul_mono (S.controls.toFun (normalize Δ m).control (control_total Δ m))
        (S.denote a (normalize Δ m).literal)
  | .modal a m, some p => S.denote a (some (.compose m p))
  | .prod a b, p => pair (S.prodTable p) (S.prod_order p) (S.denote a p) (S.denote b p)
  | .sum a b, p => pair (S.sumTable p) (S.sum_order p) (S.denote a p) (S.denote b p)
  | .fn a b, none => fn S.fnTable S.fn_order (S.denote a none) (S.denote b none)
  | .fn a b, some p => S.frozenValue (.modal (.fn a b) p)
  | .join a b, none => S.denote a none ⊔ S.denote b none
  | .join a b, some p => S.frozenValue (.modal (.join a b) p)
  | .meet a b, none => S.denote a none ⊓ S.denote b none
  | .meet a b, some p => S.frozenValue (.modal (.meet a b) p)
  | .var v, none => S.atom v
  | .unit, none => S.unit
  | .credit, none => S.credit
  | .var v, some p => S.frozenValue (.modal (.var v) p)
  | .unit, some p => S.frozenValue (.modal .unit p)
  | .credit, some p => S.frozenValue (.modal .credit p)

theorem denote_modal_total {a m} (hm : Entails Δ (.defined m)) :
    S.denote (.modal a m) none = shift S.mul_mono (S.controls.toFun m hm) (S.denote a none) := by
  simp only [denote, normalize_total hm]

theorem denote_identity (a : CompareTy) : S.denote (.modal a .epsilon) none = S.denote a none := by
  rw [S.denote_modal_total (m := .epsilon) (fun _ _ => rfl), S.controls.epsilon, shift_one]

theorem denote_compose (a : CompareTy) (m n : ModExpr) :
    S.denote (.modal (.modal a m) n) none = S.denote (.modal a (.compose m n)) none := by
  cases hn : (normalize Δ n).literal with
  | none =>
    simp only [denote, normalize_compose, Normalized.prepend, hn]
    rw [S.controls.compose, shift_mul]
  | some p => simp only [denote, normalize_compose, Normalized.prepend, hn]

def Related (a b : CompareTy) : Prop := S.denote a none ≤ S.denote b none

namespace Related

theorem refl (a : CompareTy) : S.Related a a := le_rfl

theorem trans {a b c} (h : S.Related a b) (h' : S.Related b c) : S.Related a c := le_trans h h'

theorem identity {a} : S.Related (.modal a .epsilon) a := le_of_eq (S.denote_identity a)

theorem identityRev {a} : S.Related a (.modal a .epsilon) := le_of_eq (S.denote_identity a).symm

theorem compose {a m n} : S.Related (.modal (.modal a m) n) (.modal a (.compose m n)) :=
  le_of_eq (S.denote_compose a m n)

theorem composeRev {a m n} : S.Related (.modal a (.compose m n)) (.modal (.modal a m) n) :=
  le_of_eq (S.denote_compose a m n).symm

theorem congr {a b m n} (h : S.Related a b) (hmn : Submode Δ m n) :
    S.Related (.modal a m) (.modal b n) := by
  unfold Related
  rw [S.denote_modal_total hmn.defined.1, S.denote_modal_total hmn.defined.2]
  exact (OrderHomClass.mono (shift S.mul_mono _) h).trans
    (shift_order S.mul_mono (S.controls.submode hmn) (S.denote b none))

theorem prod {a b c d m}
    (hac : S.Related (.modal a m) (.modal c m))
    (hbd : S.Related (.modal b m) (.modal d m)) :
    S.Related (.modal (.prod a b) m) (.modal (.prod c d) m) :=
  pair_inherited S.mul_mono (S.prodTable (normalize Δ m).literal)
    (S.prod_order (normalize Δ m).literal)
    (S.controls.toFun (normalize Δ m).control (control_total Δ m)) hac hbd

theorem sum {a b c d m}
    (hac : S.Related (.modal a m) (.modal c m))
    (hbd : S.Related (.modal b m) (.modal d m)) :
    S.Related (.modal (.sum a b) m) (.modal (.sum c d) m) :=
  pair_inherited S.mul_mono (S.sumTable (normalize Δ m).literal)
    (S.sum_order (normalize Δ m).literal)
    (S.controls.toFun (normalize Δ m).control (control_total Δ m)) hac hbd

theorem fn {a b c d m n} (hca : S.Related c a) (hbd : S.Related b d)
    (hmn : Submode Δ m (.compose n .top)) :
    S.Related (.modal (.fn a b) m) (.modal (.fn c d) n) := by
  unfold Related
  rw [S.denote_modal_total hmn.defined.1,
    S.denote_modal_total (Entails.defined_compose_iff.mp hmn.defined.2).1]
  exact fn_inherited S.mul_mono S.fnTable S.fn_order S.fn_post (S.controls.fnorder hmn) hca hbd

theorem joinLeft {a b} : S.Related a (.join a b) := le_sup_left

theorem joinRight {a b} : S.Related b (.join a b) := le_sup_right

theorem joinLeast {a b c} (h : S.Related a c) (h' : S.Related b c) :
    S.Related (.join a b) c := sup_le h h'

theorem meetLeft {a b} : S.Related (.meet a b) a := inf_le_left

theorem meetRight {a b} : S.Related (.meet a b) b := inf_le_right

theorem meetGreatest {a b c} (h : S.Related a b) (h' : S.Related a c) :
    S.Related a (.meet b c) := le_inf h h'

end Related

/-- Raw assumptions are a finite boundary check. All remaining shaped rules,
including arbitrary literal partial composition, follow from the construction. -/
theorem shaped_sound
    (hb : ∀ a b, Constraint.sub a b ∈ Δ → S.Related (.ofTy a) (.ofTy b))
    {a b} (h : ShapedSubtype Δ a b) : S.Related a b := by
  induction h with
  | refl _ => exact .refl S _
  | trans _ _ ih ih' => exact ih.trans S ih'
  | bound h => exact hb _ _ h
  | identity _ => exact .identity S
  | identityRev _ => exact .identityRev S
  | compose _ => exact .compose S
  | composeRev _ => exact .composeRev S
  | congr _ hm ih => exact ih.congr S hm
  | prod _ _ ih ih' => exact .prod S ih ih'
  | sum _ _ ih ih' => exact .sum S ih ih'
  | fn _ _ hm ih ih' => exact .fn S ih ih' hm
  | joinLeft _ => exact .joinLeft S
  | joinRight _ => exact .joinRight S
  | joinLeast _ _ ih ih' => exact .joinLeast S ih ih'
  | meetLeft _ => exact .meetLeft S
  | meetRight _ => exact .meetRight S
  | meetGreatest _ _ ih ih' => exact .meetGreatest S ih ih'

end Model
end
end ModalityInference.ComparisonRelativeSyntax
