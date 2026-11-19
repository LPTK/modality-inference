import ModalityInference.Proofs.ComparisonRelativeSyntaxAgreement
import ModalityInference.Proofs.ComparisonRelativeSyntaxReflection
import ModalityInference.Proofs.ComparisonObserverShadowAnchorRows
import ModalityInference.Proofs.ComparisonObserverShadowConstructorTables
import ModalityInference.Proofs.ComparisonRawHeadPrefixRows
import ModalityInference.Proofs.ComparisonRawHeadTrace

/-! The finite syntax model combines defined constructor rows with recorded
raw heads. Literal prefix tables are boundary-only and frozen lookup is finite. -/
namespace ModalityInference.ComparisonObserverShadowModel

open ComparisonRelativeSyntax ComparisonRelativeCoordinates ComparisonRelativeTables
  ComparisonRawHeadFiniteOrbits ComparisonFiniteControls ComparisonFiniteControlProjection
  ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverShadowActions ComparisonObserverFiniteRange

noncomputable section

variable {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
  {B : Boundary Δ} {names : List ModVar} {base : Nat}
  {extra : List (RawRow hn (assign hn B names base))}
  (R : Realization hn B names base extra)

/-- The unprefixed constructor tables are finite mixed tables. Their entries
include the defined algebra and the recorded ordinary head rows. -/
structure Tables where
  prod : IndexedTable R.interval.embed (Control Δ names) false false
  sum : IndexedTable R.interval.embed (Control Δ names) false false
  fn : IndexedTable R.interval.embed (Control Δ names) true false
  prod_le : ∀ m n, prod.le m n ↔ m ≤ n
  sum_le : ∀ m n, sum.le m n ↔ m ≤ n
  fn_le : ∀ m n, fn.le m n ↔ FutureLe m n
  prod_defined : ∀ m x y, (prod.table m).entry (.inl x) (.inl y)
    (.inl (ComparisonFiniteControlRange.action R.modal R.range m (op R.range .prod x y)))
  sum_defined : ∀ m x y, (sum.table m).entry (.inl x) (.inl y)
    (.inl (ComparisonFiniteControlRange.action R.modal R.range m (op R.range .sum x y)))
  fn_defined : ∀ m x y, (fn.table m).entry (.inl x) (.inl y)
    (.inl (ComparisonFiniteControlRange.action R.modal R.range m (op R.range .fn x y)))
  prod_boundary : ∀ {m a b c}, ComparisonRawHeadFiniteRows.PairRow .prod m a b c →
    (prod.table m).entry (.inr a) (.inr b) (.inr c)
  sum_boundary : ∀ {m a b c}, ComparisonRawHeadFiniteRows.PairRow .sum m a b c →
    (sum.table m).entry (.inr a) (.inr b) (.inr c)
  fn_boundary : ∀ {m a b c}, ComparisonRawHeadFiniteRows.FnRow m a b c →
    (fn.table m).entry (.inr a) (.inr b) (.inr c)

def tables (hrows : ComparisonObserverShadowConstructorRows.rows hn B names base ⊆ extra) :
    Tables R where
  prod := ComparisonObserverShadowConstructorTables.pairTable R hrows (Or.inl rfl)
  sum := ComparisonObserverShadowConstructorTables.pairTable R hrows (Or.inr rfl)
  fn := ComparisonObserverShadowConstructorTables.fnTable R hrows
  prod_le _ _ := Iff.rfl
  sum_le _ _ := Iff.rfl
  fn_le _ _ := Iff.rfl
  prod_defined _ _ _ := .defined _ _
  sum_defined _ _ _ := .defined _ _
  fn_defined _ _ _ := .defined _ _
  prod_boundary h := .boundary h
  sum_boundary h := .boundary h
  fn_boundary h := .boundary h

namespace Tables

variable {R} (T : Tables R)

def prodTable : Option ModExpr → IndexedTable R.interval.embed (Control Δ names) false false
  | none => T.prod
  | some p => ComparisonRawHeadPrefixRows.indexedTable R.interval (Or.inl rfl) p

def sumTable : Option ModExpr → IndexedTable R.interval.embed (Control Δ names) false false
  | none => T.sum
  | some p => ComparisonRawHeadPrefixRows.indexedTable R.interval (Or.inr rfl) p

theorem prod_order (p : Option ModExpr) {m n : Control Δ names} (h : m ≤ n) :
    (T.prodTable p).le m n := by
  cases p with
  | none => exact (T.prod_le m n).mpr h
  | some _ => exact h

theorem sum_order (p : Option ModExpr) {m n : Control Δ names} (h : m ≤ n) :
    (T.sumTable p).le m n := by
  cases p with
  | none => exact (T.sum_le m n).mpr h
  | some _ => exact h

def controls (hnames : Δ.modVars ⊆ names.toFinset) : ControlMap Δ (Control Δ names) T.fn.le where
  toFun := project hnames
  epsilon := project_epsilon hnames _
  compose m n hm hn := project_compose hnames m n hm hn _
  submode h := project_submode hnames h
  fnorder h := (T.fn_le _ _).mpr (project_future hnames _ _ h)

def model (hnames : Δ.modVars ⊆ names.toFinset) (sites : List RawSite)
    (tag : RawSite → ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :
    ComparisonRelativeSyntax.Model Δ (Control Δ names) (ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) R.interval.Observation R.interval.embed where
  mul_mono := ComparisonFiniteControls.mul_mono
  prodTable := T.prodTable
  prod_order := T.prod_order
  sumTable := T.sumTable
  sum_order := T.sum_order
  fnTable := T.fn
  fn_order h := (T.fn_le _ _).mpr (h.trans (le_future_self _))
  fn_post h r := (T.fn_le _ _).mpr (((T.fn_le _ _).mp h).post r)
  controls := T.controls hnames
  atom v := definedOrbit R.interval R.modal R.range (atom R.range v)
  unit := definedOrbit R.interval R.modal R.range (unit R.range)
  credit := definedOrbit R.interval R.modal R.range (credit R.range)
  frozen := rawFrozen sites (fun s => R.orbit (tag s))

theorem agreement (hnames : Δ.modVars ⊆ names.toFinset) (sites : List RawSite)
    (tag : RawSite → ComparisonObserverFiniteRange.Value R.machine ⊕ Point B names) :
    DefinedAgreement (T.model hnames sites tag) R.modal R.range hnames
      (definedOrbit R.interval R.modal R.range) := by
  apply agreement_of_defined_rows R.interval R.modal R.range (T.model hnames sites tag)
    R.coherent hnames
  · intros; rfl
  · intros; rfl
  · rfl
  · rfl
  · exact T.prod_defined
  · exact T.sum_defined
  · exact T.fn_defined

end Tables
end
end ModalityInference.ComparisonObserverShadowModel
