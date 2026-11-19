import ModalityInference.Proofs.ComparisonObserverShadowAnchors
import ModalityInference.Proofs.ComparisonRawHeadFiniteOrbits

/-! The finite orbit's total-control action has a finite raw shadow diagram.
Rows are present exactly when the corresponding source cut is inhabited. -/
namespace ModalityInference.ComparisonObserverShadowActionRows

open ComparisonObserverShadowPresentation ComparisonObserverHeadCuts ComparisonObserverShadowRows
  ComparisonRawHeadFiniteOrbits ComparisonFiniteControls ComparisonObserverRangeProduct

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (B : Boundary Δ) (names : List ModVar) (base : Nat)

local instance : Fintype (Control Δ names) := Fintype.ofFinite _

def source : ComparisonRelativeIntervals.IntervalData (ComparisonObserverRangeProduct.Value Δ)
    (Point B names) := headIntervals Point.term Point.le_iff

def assign : TypeVar → ComparisonObserverRangeProduct.Value Δ :=
  shadowAssign (source B names) (originalAssign hn) base

def presentation : NamedIntervals (assign hn B names base) (Point B names) :=
  named (source B names) (originalAssign hn) base

theorem lower_name (p : Point B names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term) :
    assign hn B names base (shadowName base (p,false)) = lower hp :=
  named_head_lower Point.term Point.le_iff (originalAssign hn) base p hp

theorem upper_name (p : Point B names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term) :
    assign hn B names base (shadowName base (p,true)) = upper hp :=
  named_head_upper Point.term Point.le_iff (originalAssign hn) base p hp

omit hn base in
theorem lower_act (m : Control Δ names) (p : Point B names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term) :
    LowerInhabited (Δ := Δ) (shape := .unit) (Point.act m p).term := by
  obtain ⟨a,ha⟩ := hp
  exact ⟨a.modal (expression m) (expression_defined m),
    (ha.congr (.refl (expression_defined m))).trans (Point.term_act m p).1⟩

omit hn base in
theorem upper_act (m : Control Δ names) (p : Point B names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term) :
    UpperInhabited (Δ := Δ) (shape := .unit) (Point.act m p).term := by
  obtain ⟨a,ha⟩ := hp
  exact ⟨a.modal (expression m) (expression_defined m),
    (Point.term_act m p).2.trans (ha.congr (.refl (expression_defined m)))⟩

omit hn base in
theorem lower_action (m : Control Δ names) (p : Point B names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term) :
    modal (expression m) (expression_defined m) (lower hp) ≤ lower (lower_act B names m p hp) := by
  have hmid : LowerInhabited (Δ := Δ) (shape := .unit) (.modal p.term (expression m)) := by
    obtain ⟨a,ha⟩ := hp
    exact ⟨a.modal (expression m) (expression_defined m),ha.congr (.refl (expression_defined m))⟩
  exact (lower_modal hp _ _ hmid).trans
    (ComparisonObserverShadowRows.lower_mono hmid _ (Point.term_act m p).1)

omit hn base in
theorem upper_action (m : Control Δ names) (p : Point B names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term) :
    upper (upper_act B names m p hp) ≤ modal (expression m) (expression_defined m) (upper hp) := by
  have hmid : UpperInhabited (Δ := Δ) (shape := .unit) (.modal p.term (expression m)) := by
    obtain ⟨a,ha⟩ := hp
    exact ⟨a.modal (expression m) (expression_defined m),ha.congr (.refl (expression_defined m))⟩
  exact (ComparisonObserverShadowRows.upper_mono _ hmid (Point.term_act m p).2).trans
    (upper_modal hp _ _ hmid)

def lowerRow (m : Control Δ names) (p : Point B names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term) : RawRow hn (assign hn B names base) :=
  RawRow.modal_le hn _ (expression m) (expression_defined m)
    (shadowName base (p,false)) (shadowName base (Point.act m p,false)) (by
      rw [lower_name hn B names base p hp,
        lower_name hn B names base _ (lower_act B names m p hp)]
      exact lower_action B names m p hp)

def upperRow (m : Control Δ names) (p : Point B names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term) : RawRow hn (assign hn B names base) :=
  RawRow.le_modal hn _ (expression m) (expression_defined m)
    (shadowName base (Point.act m p,true)) (shadowName base (p,true)) (by
      rw [upper_name hn B names base _ (upper_act B names m p hp),upper_name hn B names base p hp]
      exact upper_action B names m p hp)

def rows : List (RawRow hn (assign hn B names base)) :=
  Finset.univ.toList.flatMap fun m : Control Δ names =>
    Finset.univ.toList.flatMap fun p : Point B names =>
      (if hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term then [lowerRow hn B names base m p hp] else []) ++
      (if hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term then [upperRow hn B names base m p hp] else [])

theorem lowerRow_mem (m : Control Δ names) (p : Point B names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) p.term) :
    lowerRow hn B names base m p hp ∈ rows hn B names base := by
  apply List.mem_flatMap.mpr
  refine ⟨m,Finset.mem_toList.mpr (Finset.mem_univ m),List.mem_flatMap.mpr ?_⟩
  refine ⟨p,Finset.mem_toList.mpr (Finset.mem_univ p),List.mem_append_left _ ?_⟩
  simp only [dif_pos hp,List.mem_singleton]

theorem upperRow_mem (m : Control Δ names) (p : Point B names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) p.term) :
    upperRow hn B names base m p hp ∈ rows hn B names base := by
  apply List.mem_flatMap.mpr
  refine ⟨m,Finset.mem_toList.mpr (Finset.mem_univ m),List.mem_flatMap.mpr ?_⟩
  refine ⟨p,Finset.mem_toList.mpr (Finset.mem_univ p),List.mem_append_right _ ?_⟩
  simp only [dif_pos hp,List.mem_singleton]

end
end ModalityInference.ComparisonObserverShadowActionRows
