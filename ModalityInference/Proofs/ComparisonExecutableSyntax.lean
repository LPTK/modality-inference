import ModalityInference.Proofs.ComparisonExecutableSuffix
import ModalityInference.Proofs.ComparisonRelativeSyntax

/-! Syntax evaluation over supplied executable finite operations. Neither the
evaluator nor its suffix normalizer decides a proposition classically. -/
namespace ModalityInference.ComparisonExecutableSyntax

open ComparisonRelativeCoordinates ComparisonRelativeSyntax

structure Data (M V : Type*) where
  total : ModExpr → Bool
  control : ModExpr → M
  shift : M → V → V
  prod : Option ModExpr → V → V → V
  sum : Option ModExpr → V → V → V
  fn : V → V → V
  join : V → V → V
  meet : V → V → V
  atom : TypeVar → V
  unit : V
  credit : V
  bottom : V
  frozen : List (CompareTy × V)

namespace Data

variable {M V : Type*} (E : Data M V)

def frozenValue (a : CompareTy) : V :=
  ((E.frozen.find? (fun row => decide (row.1 = a))).map Prod.snd).getD E.bottom

def eval (E : Data M V) : CompareTy → Option ModExpr → V
  | .modal a m, none =>
      let s := ComparisonExecutableSuffix.normalize E.total m
      E.shift (E.control s.control) (E.eval a s.literal)
  | .modal a m, some p => E.eval a (some (.compose m p))
  | .prod a b, p => E.prod p (E.eval a p) (E.eval b p)
  | .sum a b, p => E.sum p (E.eval a p) (E.eval b p)
  | .fn a b, none => E.fn (E.eval a none) (E.eval b none)
  | .fn a b, some p => E.frozenValue (.modal (.fn a b) p)
  | .join a b, none => E.join (E.eval a none) (E.eval b none)
  | .join a b, some p => E.frozenValue (.modal (.join a b) p)
  | .meet a b, none => E.meet (E.eval a none) (E.eval b none)
  | .meet a b, some p => E.frozenValue (.modal (.meet a b) p)
  | .var v, none => E.atom v
  | .unit, none => E.unit
  | .credit, none => E.credit
  | .var v, some p => E.frozenValue (.modal (.var v) p)
  | .unit, some p => E.frozenValue (.modal .unit p)
  | .credit, some p => E.frozenValue (.modal .credit p)

def evalRaw (a : Ty) : V := E.eval (.ofTy a) none

end Data

def annotations : CompareTy → List ModExpr
  | .var _ | .unit | .credit => []
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => annotations a ++ annotations b
  | .modal a m => m :: annotations a

def totalTests (a : CompareTy) : List ModExpr := annotations a |>.flatMap ComparisonExecutableSuffix.tests

def controlLabels (total : ModExpr → Bool) (a : CompareTy) : List ModExpr :=
  annotations a |>.map fun m => (ComparisonExecutableSuffix.normalize total m).control

variable {Δ : Bounds} {M V N A O : Type*} [PartialOrder N] [CommMonoid N]
  {embed : A → O → Bool} (E : Data M V) (S : Model Δ N A O embed)
  (decode : V → Coordinates N (O → Bool)) (controlMap : M → N)

/-- Primitive compatibility is supplied by the finite operation checker.
The supported label obligations are separate and finite. -/
structure Agreement : Prop where
  shift : ∀ m v, decode (E.shift m v) = ComparisonRelativeCoordinates.shift S.mul_mono (controlMap m) (decode v)
  prod : ∀ p x y, decode (E.prod p x y) = pair (S.prodTable p) (S.prod_order p) (decode x) (decode y)
  sum : ∀ p x y, decode (E.sum p x y) = pair (S.sumTable p) (S.sum_order p) (decode x) (decode y)
  fn : ∀ x y, decode (E.fn x y) = ComparisonRelativeCoordinates.fn S.fnTable S.fn_order (decode x) (decode y)
  join : ∀ x y, decode (E.join x y) = decode x ⊔ decode y
  meet : ∀ x y, decode (E.meet x y) = decode x ⊓ decode y
  atom : ∀ v, decode (E.atom v) = S.atom v
  unit : decode E.unit = S.unit
  credit : decode E.credit = S.credit
  bottom : decode E.bottom = ⊥
  frozen : E.frozen.map (fun row => (row.1,decode row.2)) = S.frozen

def LabelsAgree (labels : List ModExpr) : Prop := ∀ m ∈ labels,
  ComparisonExecutableSuffix.normalize E.total m = ComparisonRawCarrierSuffix.normalize Δ m ∧
    controlMap (E.control (ComparisonExecutableSuffix.normalize E.total m).control) =
      S.controls.toFun (ComparisonRawCarrierSuffix.normalize Δ m).control
        (ComparisonRawCarrierSuffix.control_total Δ m)

def ControlsCorrectOn (labels : List ModExpr) : Prop := ∀ m ∈ labels,
  ∀ hm : Entails Δ (.defined m), controlMap (E.control m) = S.controls.toFun m hm

theorem labelsAgree_of_correct {a : CompareTy}
    (ht : ComparisonExecutableSuffix.CorrectOn Δ E.total (totalTests a))
    (hc : ControlsCorrectOn E S controlMap (controlLabels E.total a)) :
    LabelsAgree E S controlMap (annotations a) := by
  intro m hm
  have ht' : ComparisonExecutableSuffix.CorrectOn Δ E.total
      (ComparisonExecutableSuffix.tests m) := by
    intro n hn
    exact ht n (List.mem_flatMap.mpr ⟨m, hm, hn⟩)
  have he := ComparisonExecutableSuffix.normalize_eq ht'
  refine ⟨he, ?_⟩
  have hh := hc _ (List.mem_map.mpr ⟨m, hm, rfl⟩)
    (ComparisonExecutableSuffix.control_total ht')
  simpa only [he] using hh

namespace Agreement

variable {E S decode controlMap}

theorem frozenValue (h : Agreement E S decode controlMap) (a : CompareTy) :
    decode (E.frozenValue a) = S.frozenValue a := by
  rw [Data.frozenValue, Model.frozenValue, ← h.frozen, List.find?_map]
  change decode (((E.frozen.find? (fun row => decide (row.1 = a))).map Prod.snd).getD E.bottom) =
    (((E.frozen.find? (fun row => decide (row.1 = a))).map
      (fun row => (row.1, decode row.2))).map Prod.snd).getD ⊥
  cases E.frozen.find? (fun row => decide (row.1 = a)) with
  | none => exact h.bottom
  | some row => rfl

theorem eval_eq_of_labels (h : Agreement E S decode controlMap) {a : CompareTy}
    (hl : LabelsAgree E S controlMap (annotations a)) (p : Option ModExpr) :
    decode (E.eval a p) = S.denote a p := by
  induction a generalizing p with
  | var v => cases p <;> first | exact h.atom v | exact h.frozenValue _
  | unit => cases p <;> first | exact h.unit | exact h.frozenValue _
  | credit => cases p <;> first | exact h.credit | exact h.frozenValue _
  | prod a b iha ihb =>
    have ha : LabelsAgree E S controlMap (annotations a) :=
      fun m hm => hl m (List.mem_append_left _ hm)
    have hb : LabelsAgree E S controlMap (annotations b) :=
      fun m hm => hl m (List.mem_append_right _ hm)
    exact (h.prod p _ _).trans (congrArg₂ _ (iha ha p) (ihb hb p))
  | sum a b iha ihb =>
    have ha : LabelsAgree E S controlMap (annotations a) :=
      fun m hm => hl m (List.mem_append_left _ hm)
    have hb : LabelsAgree E S controlMap (annotations b) :=
      fun m hm => hl m (List.mem_append_right _ hm)
    exact (h.sum p _ _).trans (congrArg₂ _ (iha ha p) (ihb hb p))
  | fn a b iha ihb =>
    cases p with
    | some p => exact h.frozenValue _
    | none =>
      have ha : LabelsAgree E S controlMap (annotations a) :=
        fun m hm => hl m (List.mem_append_left _ hm)
      have hb : LabelsAgree E S controlMap (annotations b) :=
        fun m hm => hl m (List.mem_append_right _ hm)
      exact (h.fn _ _).trans (congrArg₂ _ (iha ha none) (ihb hb none))
  | join a b iha ihb =>
    cases p with
    | some p => exact h.frozenValue _
    | none =>
      have ha : LabelsAgree E S controlMap (annotations a) :=
        fun m hm => hl m (List.mem_append_left _ hm)
      have hb : LabelsAgree E S controlMap (annotations b) :=
        fun m hm => hl m (List.mem_append_right _ hm)
      exact (h.join _ _).trans (congrArg₂ _ (iha ha none) (ihb hb none))
  | meet a b iha ihb =>
    cases p with
    | some p => exact h.frozenValue _
    | none =>
      have ha : LabelsAgree E S controlMap (annotations a) :=
        fun m hm => hl m (List.mem_append_left _ hm)
      have hb : LabelsAgree E S controlMap (annotations b) :=
        fun m hm => hl m (List.mem_append_right _ hm)
      exact (h.meet _ _).trans (congrArg₂ _ (iha ha none) (ihb hb none))
  | modal a m ih =>
    have ha : LabelsAgree E S controlMap (annotations a) :=
      fun n hn => hl n (List.mem_cons_of_mem _ hn)
    cases p with
    | some p => exact ih ha _
    | none =>
      obtain ⟨hn, hc⟩ := hl m (List.mem_cons_self ..)
      simp only [Data.eval, Model.denote]
      rw [h.shift, ih ha, hc, hn]

theorem eval_eq (h : Agreement E S decode controlMap) {a : CompareTy}
    (ht : ComparisonExecutableSuffix.CorrectOn Δ E.total (totalTests a))
    (hc : ControlsCorrectOn E S controlMap (controlLabels E.total a)) (p : Option ModExpr) :
    decode (E.eval a p) = S.denote a p :=
  h.eval_eq_of_labels (labelsAgree_of_correct E S controlMap ht hc) p

theorem evalRaw_eq (h : Agreement E S decode controlMap) {a : Ty}
    (ht : ComparisonExecutableSuffix.CorrectOn Δ E.total (totalTests (.ofTy a)))
    (hc : ControlsCorrectOn E S controlMap (controlLabels E.total (.ofTy a))) :
    decode (E.evalRaw a) = S.denote (.ofTy a) none := h.eval_eq ht hc none

end Agreement

end ModalityInference.ComparisonExecutableSyntax
