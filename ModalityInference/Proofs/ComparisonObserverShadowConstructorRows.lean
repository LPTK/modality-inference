import ModalityInference.Proofs.ComparisonRawHeadFiniteRows
import ModalityInference.Proofs.ComparisonObserverShadowActionRows

/-! Each recorded constructor contributes shadow bounds only when the required
input cuts exist. All such bounds share the head-orbit shadow assignment. -/
namespace ModalityInference.ComparisonObserverShadowConstructorRows

open ComparisonRawHeadFiniteOrbits ComparisonRawHeadFiniteRows ComparisonFiniteControls
  ComparisonStructuralLayout ComparisonObserverHeadCuts ComparisonObserverShadowRows
  ComparisonObserverShadowPresentation ComparisonObserverShadowActionRows
  ComparisonObserverRangeProduct

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
  {B : Boundary Δ} {names : List ModVar}

include hn

omit hn in
private theorem pair_kind {k : Constructor} (hk : k = .prod ∨ k = .sum) :
    k.kind = .prod ∨ k.kind = .sum := hk.elim (fun h => h ▸ .inl rfl) (fun h => h ▸ .inr rfl)

theorem pair_lower_inhabited {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (r : HeadRow B k) (m : Control Δ names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term) :
    LowerInhabited (Δ := Δ) (shape := .unit) (r.atOutput m).term := by
  simpa only [HeadRow.atOutput,Point.term,r.equation,Constructor.kind_op] using
    (lower_pair_inhabited hn k.kind (pair_kind hk) (expression m) (expression_defined m) hp hq)

theorem pair_upper_inhabited {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (r : HeadRow B k) (m : Control Δ names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term) :
    UpperInhabited (Δ := Δ) (shape := .unit) (r.atOutput m).term := by
  simpa only [HeadRow.atOutput,Point.term,r.equation,Constructor.kind_op] using
    (upper_pair_inhabited hn k.kind (pair_kind hk) (expression m) (expression_defined m) hp hq)

theorem pair_lower {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (r : HeadRow B k) (m : Control Δ names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term) :
    modal (expression m) (expression_defined m) (op hn k.kind (lower hp) (lower hq)) ≤
      lower (pair_lower_inhabited hn hk r m hp hq) := by
  have hr := lower_pair_inhabited hn k.kind (pair_kind hk)
    (expression m) (expression_defined m) hp hq
  exact (lower_pair hn k.kind (pair_kind hk) (expression m) (expression_defined m) hp hq hr).trans
    (ComparisonObserverShadowRows.lower_mono _ _ (by
      simpa only [Constructor.kind_op,HeadRow.atOutput,Point.term,r.equation] using
        AlgebraSubtype.refl (r.atOutput m).shaped))

theorem pair_upper {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (r : HeadRow B k) (m : Control Δ names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term) :
    upper (pair_upper_inhabited hn hk r m hp hq) ≤
      modal (expression m) (expression_defined m) (op hn k.kind (upper hp) (upper hq)) := by
  have hr := upper_pair_inhabited hn k.kind (pair_kind hk)
    (expression m) (expression_defined m) hp hq
  exact (ComparisonObserverShadowRows.upper_mono _ hr (by
      simpa only [Constructor.kind_op,HeadRow.atOutput,Point.term,r.equation] using
        AlgebraSubtype.refl (r.atOutput m).shaped)).trans
    (upper_pair hn k.kind (pair_kind hk) (expression m) (expression_defined m) hp hq hr)

theorem fn_lower_inhabited (r : HeadRow B .fn) (m : Control Δ names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term) :
    LowerInhabited (Δ := Δ) (shape := .unit) (r.atOutput m).term :=
  (lower_fn_inhabited hn (expression m) (expression_defined m) hp hq).mono
    (r.fn_output_equivalent m).2

theorem fn_upper_inhabited (r : HeadRow B .fn) (m : Control Δ names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term) :
    UpperInhabited (Δ := Δ) (shape := .unit) (r.atOutput m).term :=
  (upper_fn_inhabited hn (expression m) (expression_defined m) hp hq).antitone
    (r.fn_output_equivalent m).1

theorem fn_lower (r : HeadRow B .fn) (m : Control Δ names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term) :
    modal (expression m) (expression_defined m) (op hn .fn (upper hp) (lower hq)) ≤
      lower (fn_lower_inhabited hn r m hp hq) :=
  (lower_fn hn (expression m) (expression_defined m) hp hq
      (lower_fn_inhabited hn (expression m) (expression_defined m) hp hq)).trans
    (ComparisonObserverShadowRows.lower_mono _ _ (r.fn_output_equivalent m).2)

theorem fn_upper (r : HeadRow B .fn) (m : Control Δ names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term) :
    upper (fn_upper_inhabited hn r m hp hq) ≤
      modal (expression m) (expression_defined m) (op hn .fn (lower hp) (upper hq)) :=
  (ComparisonObserverShadowRows.upper_mono _
      (upper_fn_inhabited hn (expression m) (expression_defined m) hp hq)
      (r.fn_output_equivalent m).1).trans
    (upper_fn hn (expression m) (expression_defined m) hp hq _)

variable (B names) (base : Nat)

def lowerPairRow {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (r : HeadRow B k) (m : Control Δ names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term) :
    RawRow hn (assign hn B names base) :=
  RawRow.op_le hn _ k.kind (expression m) (expression_defined m)
    (shadowName base (r.atLeft m,false)) (shadowName base (r.atRight m,false))
    (shadowName base (r.atOutput m,false)) (by
      rw [lower_name hn B names base _ hp,lower_name hn B names base _ hq,
        lower_name hn B names base _ (pair_lower_inhabited hn hk r m hp hq)]
      exact pair_lower hn hk r m hp hq)

def upperPairRow {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (r : HeadRow B k) (m : Control Δ names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term) :
    RawRow hn (assign hn B names base) :=
  RawRow.le_op hn _ k.kind (expression m) (expression_defined m)
    (shadowName base (r.atOutput m,true)) (shadowName base (r.atLeft m,true))
    (shadowName base (r.atRight m,true)) (by
      rw [upper_name hn B names base _ (pair_upper_inhabited hn hk r m hp hq),
        upper_name hn B names base _ hp,upper_name hn B names base _ hq]
      exact pair_upper hn hk r m hp hq)

def lowerFnRow (r : HeadRow B .fn) (m : Control Δ names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term) :
    RawRow hn (assign hn B names base) :=
  RawRow.op_le hn _ .fn (expression m) (expression_defined m)
    (shadowName base (Point.base B names r.left,true))
    (shadowName base (Point.base B names r.right,false))
    (shadowName base (r.atOutput m,false)) (by
      rw [upper_name hn B names base _ hp,lower_name hn B names base _ hq,
        lower_name hn B names base _ (fn_lower_inhabited hn r m hp hq)]
      exact fn_lower hn r m hp hq)

def upperFnRow (r : HeadRow B .fn) (m : Control Δ names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term) :
    RawRow hn (assign hn B names base) :=
  RawRow.le_op hn _ .fn (expression m) (expression_defined m)
    (shadowName base (r.atOutput m,true))
    (shadowName base (Point.base B names r.left,false))
    (shadowName base (Point.base B names r.right,true)) (by
      rw [upper_name hn B names base _ (fn_upper_inhabited hn r m hp hq),
        lower_name hn B names base _ hp,upper_name hn B names base _ hq]
      exact fn_upper hn r m hp hq)

local instance : Fintype (Control Δ names) := Fintype.ofFinite _

def pairRows {k : Constructor} (hk : k = .prod ∨ k = .sum) :
    List (RawRow hn (assign hn B names base)) :=
  Finset.univ.toList.flatMap fun m : Control Δ names =>
    Finset.univ.toList.flatMap fun r : HeadRow B k =>
      (if h : LowerInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term ∧
          LowerInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term
        then [lowerPairRow hn B names base hk r m h.1 h.2] else []) ++
      (if h : UpperInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term ∧
          UpperInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term
        then [upperPairRow hn B names base hk r m h.1 h.2] else [])

def fnRows : List (RawRow hn (assign hn B names base)) :=
  Finset.univ.toList.flatMap fun m : Control Δ names =>
    Finset.univ.toList.flatMap fun r : HeadRow B .fn =>
      (if h : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term ∧
          LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term
        then [lowerFnRow hn B names base r m h.1 h.2] else []) ++
      (if h : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term ∧
          UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term
        then [upperFnRow hn B names base r m h.1 h.2] else [])

def rows : List (RawRow hn (assign hn B names base)) :=
  pairRows hn B names base (Or.inl rfl) ++ pairRows hn B names base (Or.inr rfl) ++
    fnRows hn B names base

theorem lowerPairRow_mem {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (r : HeadRow B k) (m : Control Δ names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term) :
    lowerPairRow hn B names base hk r m hp hq ∈ pairRows hn B names base hk := by
  apply List.mem_flatMap.mpr
  refine ⟨m,Finset.mem_toList.mpr (Finset.mem_univ m),List.mem_flatMap.mpr ?_⟩
  refine ⟨r,Finset.mem_toList.mpr (Finset.mem_univ r),List.mem_append_left _ ?_⟩
  simp only [dif_pos (And.intro hp hq),List.mem_singleton]

theorem upperPairRow_mem {k : Constructor} (hk : k = .prod ∨ k = .sum)
    (r : HeadRow B k) (m : Control Δ names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (r.atLeft m).term)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (r.atRight m).term) :
    upperPairRow hn B names base hk r m hp hq ∈ pairRows hn B names base hk := by
  apply List.mem_flatMap.mpr
  refine ⟨m,Finset.mem_toList.mpr (Finset.mem_univ m),List.mem_flatMap.mpr ?_⟩
  refine ⟨r,Finset.mem_toList.mpr (Finset.mem_univ r),List.mem_append_right _ ?_⟩
  simp only [dif_pos (And.intro hp hq),List.mem_singleton]

theorem lowerFnRow_mem (r : HeadRow B .fn) (m : Control Δ names)
    (hp : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term)
    (hq : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term) :
    lowerFnRow hn B names base r m hp hq ∈ fnRows hn B names base := by
  apply List.mem_flatMap.mpr
  refine ⟨m,Finset.mem_toList.mpr (Finset.mem_univ m),List.mem_flatMap.mpr ?_⟩
  refine ⟨r,Finset.mem_toList.mpr (Finset.mem_univ r),List.mem_append_left _ ?_⟩
  simp only [dif_pos (And.intro hp hq),List.mem_singleton]

theorem upperFnRow_mem (r : HeadRow B .fn) (m : Control Δ names)
    (hp : LowerInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.left).term)
    (hq : UpperInhabited (Δ := Δ) (shape := .unit) (Point.base B names r.right).term) :
    upperFnRow hn B names base r m hp hq ∈ fnRows hn B names base := by
  apply List.mem_flatMap.mpr
  refine ⟨m,Finset.mem_toList.mpr (Finset.mem_univ m),List.mem_flatMap.mpr ?_⟩
  refine ⟨r,Finset.mem_toList.mpr (Finset.mem_univ r),List.mem_append_right _ ?_⟩
  simp only [dif_pos (And.intro hp hq),List.mem_singleton]

theorem pairRows_subset {k : Constructor} (hk : k = .prod ∨ k = .sum) :
    pairRows hn B names base hk ⊆ rows hn B names base := by
  rcases hk with rfl | rfl
  · exact fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
  · exact fun _ h => List.mem_append_left _ (List.mem_append_right _ h)

theorem fnRows_subset : fnRows hn B names base ⊆ rows hn B names base :=
  fun _ h => List.mem_append_right _ h

end
end ModalityInference.ComparisonObserverShadowConstructorRows
