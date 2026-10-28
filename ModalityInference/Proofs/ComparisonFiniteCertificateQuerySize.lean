import ModalityInference.Proofs.ComparisonFiniteCertificateQueries
import ModalityInference.Proofs.ComparisonFiniteCertificateDimensions
import ModalityInference.ComparisonFiniteCertificateBounds
import Mathlib.Algebra.Order.BigOperators.Group.List

/-! Syntactic size bounds for the shadow diagram used by finite comparison
certificates. Modality expressions contribute one node regardless of their
internal representation. Semantic cut filters can only decrease these bounds. -/
namespace ModalityInference.ComparisonFiniteCertificateQuerySize

open ComparisonObserverBoundary ComparisonObserverShadowPresentation
  ComparisonObserverShadowActionRows ComparisonObserverShadowActions
  ComparisonObserverRangeTransfer ComparisonRawHeadFiniteOrbits
  ComparisonFiniteControls ComparisonObserverShadowQueries

noncomputable section
attribute [local instance] Classical.propDecidable

def rawSize (a : Ty) : Nat := (subterms (.ofTy a)).length

def rowsSize (rows : List (Ty × Ty)) : Nat :=
  (rows.map fun p => rawSize p.1 + rawSize p.2).sum

theorem declaredTypes_shadow (Δ : Bounds) :
    declaredTypes (ComparisonBalancedProjection.shapeShadow Δ) = [] := by
  induction Δ with
  | nil => rfl
  | cons c Δ ih => cases c <;> simp_all [ComparisonBalancedProjection.shapeShadow, ComparisonBalancedProjection.shapeFact, declaredTypes]

theorem boundary_context_length (Δ : Bounds) (rs : List (Ty × Ty)) (queries : List CompareTy) :
    (ComparisonObserverBoundary.boundary (context Δ rs) queries).length =
      rowsSize rs + (closure queries).length := by
  simp only [ComparisonObserverBoundary.boundary, inputs, closure, List.flatMap_append, List.length_append]
  have hd : declaredTypes (context Δ rs) = rs.flatMap (fun p => [.ofTy p.1, .ofTy p.2]) := by
    simpa only [context, declaredTypes, List.flatMap_append, List.flatMap_map, List.append_nil] using
      congrArg (fun xs => rs.flatMap (fun p => [.ofTy p.1, .ofTy p.2]) ++ xs) (declaredTypes_shadow Δ)
  rw [hd]
  simp [List.flatMap_assoc, List.length_flatMap, rowsSize, rawSize]

@[simp] theorem rowsSize_append (xs ys : List (Ty × Ty)) :
    rowsSize (xs ++ ys) = rowsSize xs + rowsSize ys := by
  simp [rowsSize]

theorem rowsSize_flatMap_le {α : Type*} (xs : List α) (f : α → List (Ty × Ty))
    (k : Nat) (h : ∀ x ∈ xs, rowsSize (f x) ≤ k) :
    rowsSize (xs.flatMap f) ≤ xs.length * k := by
  induction xs with
  | nil => simp [rowsSize]
  | cons x xs ih =>
      simpa only [List.flatMap_cons, rowsSize_append, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
        using Nat.add_le_add (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

theorem orderRows_size {Δ : Bounds}
    (assign : TypeVar → ComparisonObserverRangeProduct.Value Δ) (vars : List TypeVar) :
    rowsSize (orderRows assign vars) ≤ vars.length * (vars.length * 2) := by
  apply rowsSize_flatMap_le
  intro x hx
  simpa [rowsSize, rawSize, List.map_map, subterms, CompareTy.ofTy, Function.comp_def] using
    Nat.mul_le_mul_right 2 (List.length_filter_le (fun w => decide (assign x ≤ assign w)) vars)

theorem length_flatMap_le {α β : Type*} (xs : List α) (f : α → List β)
    (k : Nat) (h : ∀ x ∈ xs, (f x).length ≤ k) :
    (xs.flatMap f).length ≤ xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simpa only [List.flatMap_cons, List.length_append, List.length_cons,
        Nat.add_mul, Nat.one_mul, Nat.add_comm] using
        Nat.add_le_add (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem x hy)))

theorem shadowVars_length {Δ : Bounds} {P : Type*} [Preorder P] [Fintype P]
    {assign : TypeVar → ComparisonObserverRangeProduct.Value Δ} (S : NamedIntervals assign P) :
    S.shadowVars.length ≤ Fintype.card P * 2 := by
  apply le_trans (length_flatMap_le Finset.univ.toList _ 2 ?_)
  · simp
  · intro x hx
    cases hl : S.lower x <;> cases hu : S.upper x <;> simp

variable {Δ : Bounds} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (B : Boundary Δ) (names : List ModVar) (base : Nat)

local instance : Fintype (Control Δ names) := Fintype.ofFinite _

theorem actionRows_size :
    rowsSize (RawRow.rows hn (assign hn B names base)
      (ComparisonObserverShadowActionRows.rows hn B names base)) ≤
      Fintype.card (Control Δ names) * (Fintype.card (Point B names) * 6) := by
  simp only [RawRow.rows, ComparisonObserverShadowActionRows.rows, List.map_flatMap]
  apply (rowsSize_flatMap_le _ _ (Fintype.card (Point B names) * 6) ?_).trans (by simp)
  intro m hm
  apply (rowsSize_flatMap_le _ _ 6 ?_).trans (by simp)
  intro p hp
  split_ifs <;> simp [rowsSize, rawSize, lowerRow, upperRow, RawRow.modal_le, RawRow.le_modal,
    CompareTy.ofTy, subterms]

theorem headRow_card (k : ComparisonStructuralLayout.Constructor) :
    Fintype.card (ComparisonRawHeadFiniteRows.HeadRow B k) ≤ B.heads.length ^ 3 := by
  have h := Fintype.card_le_of_injective
    (fun r : ComparisonRawHeadFiniteRows.HeadRow B k => (r.left,r.right,r.output))
    (fun _ _ he => ComparisonRawHeadFiniteRows.HeadRow.ext (congrArg Prod.fst he)
      (congrArg (fun p => p.2.1) he) (congrArg (fun p => p.2.2) he))
  simpa [Fintype.card_prod, Fintype.card_fin, pow_succ, Nat.mul_assoc] using h

theorem pairRows_size {k : ComparisonStructuralLayout.Constructor} (hk : k = .prod ∨ k = .sum) :
    rowsSize (RawRow.rows hn (assign hn B names base)
      (ComparisonObserverShadowConstructorRows.pairRows hn B names base hk)) ≤
      Fintype.card (Control Δ names) * (Fintype.card (ComparisonRawHeadFiniteRows.HeadRow B k) * 10) := by
  simp only [RawRow.rows, ComparisonObserverShadowConstructorRows.pairRows, List.map_flatMap]
  apply (rowsSize_flatMap_le _ _ (Fintype.card (ComparisonRawHeadFiniteRows.HeadRow B k) * 10) ?_).trans (by simp)
  intro m hm
  apply (rowsSize_flatMap_le _ _ 10 ?_).trans (by simp)
  intro r hr
  split_ifs <;> cases k <;> simp [rowsSize, rawSize,
    ComparisonObserverShadowConstructorRows.lowerPairRow, ComparisonObserverShadowConstructorRows.upperPairRow,
    RawRow.op_le, RawRow.le_op, rawOp, ComparisonStructuralLayout.Constructor.kind, CompareTy.ofTy, subterms]

theorem fnRows_size :
    rowsSize (RawRow.rows hn (assign hn B names base)
      (ComparisonObserverShadowConstructorRows.fnRows hn B names base)) ≤
      Fintype.card (Control Δ names) * (Fintype.card (ComparisonRawHeadFiniteRows.HeadRow B .fn) * 10) := by
  simp only [RawRow.rows, ComparisonObserverShadowConstructorRows.fnRows, List.map_flatMap]
  apply (rowsSize_flatMap_le _ _ (Fintype.card (ComparisonRawHeadFiniteRows.HeadRow B .fn) * 10) ?_).trans (by simp)
  intro m hm
  apply (rowsSize_flatMap_le _ _ 10 ?_).trans (by simp)
  intro r hr
  split_ifs <;> simp [rowsSize, rawSize,
    ComparisonObserverShadowConstructorRows.lowerFnRow, ComparisonObserverShadowConstructorRows.upperFnRow,
    RawRow.op_le, RawRow.le_op, rawOp, CompareTy.ofTy, subterms]

theorem constructorRows_size :
    rowsSize (RawRow.rows hn (assign hn B names base)
      (ComparisonObserverShadowConstructorRows.rows hn B names base)) ≤
      Fintype.card (Control Δ names) * B.heads.length ^ 3 * 30 := by
  have hp := (pairRows_size hn B names base (Or.inl rfl)).trans
    (Nat.mul_le_mul_left (Fintype.card (Control Δ names))
      (Nat.mul_le_mul_right 10 (headRow_card B .prod)))
  have hs := (pairRows_size hn B names base (Or.inr rfl)).trans
    (Nat.mul_le_mul_left (Fintype.card (Control Δ names))
      (Nat.mul_le_mul_right 10 (headRow_card B .sum)))
  have hf := (fnRows_size hn B names base).trans
    (Nat.mul_le_mul_left (Fintype.card (Control Δ names))
      (Nat.mul_le_mul_right 10 (headRow_card B .fn)))
  simpa only [RawRow.rows, ComparisonObserverShadowConstructorRows.rows, List.map_append,
    rowsSize_append, ← Nat.mul_assoc, ← Nat.mul_add] using Nat.add_le_add (Nat.add_le_add hp hs) hf

omit B base in
theorem anchorRows_size (heads : List Ty) (M : Nat) (hM : ∀ a ∈ heads, rawSize a ≤ M) :
    rowsSize (RawRow.rows hn
      (assign hn (Boundary.ofRaw Δ heads) names (ComparisonObserverShadowAnchorRows.freshBase heads))
      (ComparisonObserverShadowAnchorRows.rows hn heads names)) ≤ heads.length * (2 * (M + 1)) := by
  simp only [RawRow.rows, ComparisonObserverShadowAnchorRows.rows, List.map_flatMap]
  apply (rowsSize_flatMap_le _ _ (2 * (M + 1)) ?_).trans (by simp)
  intro i hi
  split_ifs with ha
  · have h := hM heads[i] (List.getElem_mem i.isLt)
    simpa [rowsSize, ComparisonObserverShadowAnchorRows.lowerRow,
      ComparisonObserverShadowAnchorRows.upperRow, anchor_le,
      le_anchor, rawSize, CompareTy.ofTy, subterms, Nat.two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_le_add (Nat.add_le_add_right h 1) (Nat.add_le_add_left h 1)
  · simp [rowsSize]

omit B base in
theorem diagram_boundary_length (heads : List Ty) (queries : List CompareTy) (M : Nat)
    (hM : ∀ a ∈ heads, rawSize a ≤ M) :
    let B := Boundary.ofRaw Δ heads
    let base := ComparisonObserverShadowAnchorRows.freshBase heads
    let C := Fintype.card (Control Δ names)
    let P := Fintype.card (Point B names)
    let extra := ComparisonObserverShadowAnchorRows.rows hn heads names ++
      ComparisonObserverShadowConstructorRows.rows hn B names base
    (ComparisonObserverBoundary.boundary (context Δ (diagramRows hn B names base extra))
      (queryBoundary hn B names base queries)).length ≤
      (P * 2) * (P * 2 * 2) +
        (C * (P * 6) + (heads.length * (2 * (M + 1)) + C * heads.length ^ 3 * 30)) +
        (P * 2 + (closure queries).length) := by
  dsimp only
  let B := Boundary.ofRaw Δ heads
  let base := ComparisonObserverShadowAnchorRows.freshBase heads
  let P := Fintype.card (Point B names)
  have hv := shadowVars_length (presentation hn B names base)
  have ho := (orderRows_size (assign hn B names base) (presentation hn B names base).shadowVars).trans
    (Nat.mul_le_mul hv (Nat.mul_le_mul_right 2 hv))
  have ha := actionRows_size hn B names base
  have hh := anchorRows_size hn names heads M hM
  have hc := constructorRows_size hn B names base
  simpa [boundary_context_length, diagramRows, RawRow.rows, List.map_append,
    queryBoundary, closure, List.flatMap_map, Function.comp_def, subterms, B, base, Boundary.ofRaw]
    using Nat.add_le_add (Nat.add_le_add ho (Nat.add_le_add ha (Nat.add_le_add hh hc)))
      (Nat.add_le_add_right hv (closure queries).length)

omit hn B names base in
theorem calls_length (Δ : Bounds) (a : Ty) (p : Option ModExpr) :
    (ComparisonRawHeadTrace.calls Δ a p).length ≤ rawSize a := by
  induction a generalizing p with
  | var | unit | credit => cases p <;> simp [ComparisonRawHeadTrace.calls, rawSize, subterms, CompareTy.ofTy]
  | prod a b iha ihb | sum a b iha ihb =>
      simpa [ComparisonRawHeadTrace.calls, rawSize, subterms, CompareTy.ofTy] using
        Nat.add_le_add_right (Nat.add_le_add (iha p) (ihb p)) 1
  | fn a b iha ihb =>
      cases p with
      | none => simpa [ComparisonRawHeadTrace.calls, rawSize, subterms, CompareTy.ofTy] using
          Nat.add_le_add_right (Nat.add_le_add (iha none) (ihb none)) 1
      | some p => simp [ComparisonRawHeadTrace.calls, rawSize, subterms, CompareTy.ofTy]
  | modal a m ih =>
      cases p with
      | none => simpa [ComparisonRawHeadTrace.calls, rawSize, subterms, CompareTy.ofTy] using
          Nat.add_le_add_right (ih (ComparisonRawCarrierSuffix.normalize Δ m).literal) 1
      | some p => simpa [ComparisonRawHeadTrace.calls, rawSize, subterms, CompareTy.ofTy] using
          Nat.add_le_add_right (ih (some (.compose m p))) 1

omit hn B names base in
theorem boundInput_nodes (Δ : Bounds) :
    ((ComparisonObserverShadowModel.RawInput.boundInputs Δ).map rawSize).sum =
      (closure (declaredTypes Δ)).length := by
  induction Δ with
  | nil => rfl
  | cons c Δ ih =>
      cases c <;> simpa [ComparisonObserverShadowModel.RawInput.boundInputs, declaredTypes,
        closure, rawSize, List.flatMap_append, List.map_append] using ih

omit hn B names base in
theorem support_nodes (queries : List CompareTy) :
    ((ComparisonObserverShadowQuerySupport.support queries).map rawSize).sum =
      (queries.map (fun q => (types q).card + 2 * (modes q).card)).sum := by
  induction queries with
  | nil => rfl
  | cons q qs ih =>
      simpa [ComparisonObserverShadowQuerySupport.support, List.map_append,
        List.map_map, Function.comp_def, rawSize, subterms, CompareTy.ofTy, Nat.mul_comm, Nat.add_assoc] using ih

omit hn B names base in
theorem input_nodes (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    ((ComparisonObserverShadowModel.RawInput.boundInputs Δ ++
      ComparisonObserverShadowQuerySupport.rawInputs raw queries).map rawSize).sum =
      ComparisonFiniteCertificateBounds.inputNodes Δ raw queries := by
  simp only [ComparisonObserverShadowQuerySupport.rawInputs, List.map_append, List.sum_append,
    ComparisonFiniteCertificateBounds.inputNodes, closure, List.flatMap_append, List.length_append]
  rw [boundInput_nodes, support_nodes]
  simp [closure, List.length_flatMap, List.map_map, Function.comp_def, Nat.add_assoc]
  rfl

omit hn B names base in
theorem ofInputs_length (Δ : Bounds) (raw : List Ty) :
    (ComparisonRawHeadTrace.ofInputs Δ raw).length ≤ (raw.map rawSize).sum := by
  induction raw with
  | nil => rfl
  | cons a raw ih =>
      simpa only [ComparisonRawHeadTrace.ofInputs, List.flatMap_cons, List.length_append,
        List.map_cons, List.sum_cons] using Nat.add_le_add (calls_length Δ a none) ih

omit hn B names base in
theorem sites_length (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) :
    (ComparisonObserverShadowQuerySupport.sites Δ raw queries).length ≤
      ComparisonFiniteCertificateBounds.inputNodes Δ raw queries := by
  exact (ofInputs_length Δ _).trans_eq (input_nodes Δ raw queries)

omit hn B names base in
theorem calls_head_size {Δ : Bounds} {a : Ty} {p : Option ModExpr} {s : ComparisonRawHeadTrace.Site}
    (hs : s ∈ ComparisonRawHeadTrace.calls Δ a p) : rawSize s.1 ≤ rawSize a := by
  induction a generalizing p s <;> cases p <;>
    simp only [ComparisonRawHeadTrace.calls, List.mem_cons, List.mem_append] at hs
  all_goals rcases hs with rfl | hs
  all_goals try exact Nat.le_refl _
  all_goals try exact (List.not_mem_nil hs).elim
  case prod.none.inr a b iha ihb | sum.none.inr a b iha ihb | fn.none.inr a b iha ihb =>
    rcases hs with hs | hs
    · have h := iha hs
      simp only [rawSize, CompareTy.ofTy, subterms, List.length_cons, List.length_append] at h ⊢
      omega
    · have h := ihb hs
      simp only [rawSize, CompareTy.ofTy, subterms, List.length_cons, List.length_append] at h ⊢
      omega
  case prod.some.inr a b iha ihb p | sum.some.inr a b iha ihb p =>
    rcases hs with hs | hs
    · have h := iha hs
      simp only [rawSize, CompareTy.ofTy, subterms, List.length_cons, List.length_append] at h ⊢
      omega
    · have h := ihb hs
      simp only [rawSize, CompareTy.ofTy, subterms, List.length_cons, List.length_append] at h ⊢
      omega
  case modal.none.inr a m ih =>
    simpa [rawSize, CompareTy.ofTy, subterms] using (ih hs).trans (Nat.le_add_right (rawSize a) 1)
  case modal.some.inr a m ih p =>
    simpa [rawSize, CompareTy.ofTy, subterms] using (ih hs).trans (Nat.le_add_right (rawSize a) 1)

omit hn B names base in
theorem le_sum_of_mem {α : Type*} (f : α → Nat) {xs : List α} {x : α} (hx : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_add_right _ _
      · exact (ih hx).trans (Nat.le_add_left _ _)

omit hn B names base in
theorem rawHead_size (Δ : Bounds) (raw : List Ty) (queries : List CompareTy) {a : Ty}
    (ha : a ∈ ComparisonRawHeadTrace.rawHeads (ComparisonObserverShadowQuerySupport.sites Δ raw queries)) :
    rawSize a ≤ ComparisonFiniteCertificateBounds.inputNodes Δ raw queries + 1 := by
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hb,hbs⟩ := List.mem_flatMap.mp hs
  have hinput := (le_sum_of_mem rawSize hb).trans_eq (input_nodes Δ raw queries)
  have h := Nat.add_le_add_right ((calls_head_size hbs).trans hinput) 1
  have hp : rawSize (ComparisonRawHeadTrace.applyPrefix s.2 s.1) ≤ rawSize s.1 + 1 := by
    cases s.2 <;> simp [ComparisonRawHeadTrace.applyPrefix, rawSize, CompareTy.ofTy, subterms]
  exact hp.trans h

omit B names base in
theorem source_boundary_length (raw : List Ty) (queries : List CompareTy) (C : Nat)
    (hC : Fintype.card (Control Δ (ComparisonRawHeadTrace.modeNames Δ
      (ComparisonObserverShadowQuerySupport.sites Δ raw queries))) ≤ C) :
    let sites := ComparisonObserverShadowQuerySupport.sites Δ raw queries
    let B := ComparisonRawHeadTrace.boundary Δ sites
    let names := ComparisonRawHeadTrace.modeNames Δ sites
    let base := ComparisonObserverShadowAnchorRows.freshBase (ComparisonRawHeadTrace.rawHeads sites)
    (ComparisonObserverBoundary.boundary
      (context Δ (diagramRows hn B names base
        (ComparisonObserverShadowModel.RawInput.extraRows hn
          (ComparisonObserverShadowQuerySupport.rawInputs raw queries))))
      (queryBoundary hn B names base queries)).length ≤
      ComparisonFiniteCertificateBounds.diagramNodes
        (ComparisonFiniteCertificateBounds.inputNodes Δ raw queries) C (closure queries).length := by
  dsimp only
  let sites := ComparisonObserverShadowQuerySupport.sites Δ raw queries
  let heads := ComparisonRawHeadTrace.rawHeads sites
  let names := ComparisonRawHeadTrace.modeNames Δ sites
  let H := ComparisonFiniteCertificateBounds.inputNodes Δ raw queries
  have hH : heads.length ≤ H := by simpa only [heads, ComparisonRawHeadTrace.rawHeads, List.length_map] using sites_length Δ raw queries
  have h := diagram_boundary_length hn names heads queries (H + 1) (fun _ ha => rawHead_size Δ raw queries ha)
  have hp : Fintype.card (Point (Boundary.ofRaw Δ heads) names) =
      heads.length * Fintype.card (Control Δ names) := by
    simpa only [Nat.card_eq_fintype_card, Boundary.ofRaw, List.length_map,
      ← ComparisonFiniteCertificate.Dimensions.control_card Δ names] using
      ComparisonFiniteCertificate.Dimensions.point_card (Boundary.ofRaw Δ heads) names
  have hP : Fintype.card (Point (Boundary.ofRaw Δ heads) names) ≤ H * C :=
    hp.le.trans (Nat.mul_le_mul hH hC)
  apply h.trans
  dsimp only [ComparisonFiniteCertificateBounds.diagramNodes]
  have h3 : heads.length ^ 3 ≤ H ^ 3 := by
    simpa only [pow_succ, pow_zero, Nat.one_mul, Nat.mul_assoc] using
      Nat.mul_le_mul (Nat.mul_le_mul hH hH) hH
  have h2 := Nat.mul_le_mul_right 2 hP
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.mul_le_mul h2 (Nat.mul_le_mul_right 2 h2))
      (Nat.add_le_add (Nat.mul_le_mul hC (Nat.mul_le_mul_right 6 hP))
        (Nat.add_le_add (Nat.mul_le_mul_right (2 * (H + 2)) hH)
          (Nat.mul_le_mul_right 30 (Nat.mul_le_mul hC h3)))))
    (Nat.add_le_add_right h2 (closure queries).length)

end
end ModalityInference.ComparisonFiniteCertificateQuerySize
