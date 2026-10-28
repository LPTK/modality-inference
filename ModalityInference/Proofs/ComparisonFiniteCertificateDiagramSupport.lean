import ModalityInference.Proofs.ComparisonFiniteCertificateQueries

/-! Modal names in the finite shadow diagram come only from the original
context, the chosen controls, the raw anchor heads, and the selected queries. -/
namespace ModalityInference.ComparisonFiniteCertificate.DiagramSupport

open ComparisonFiniteControls ComparisonRawHeadFiniteOrbits
  ComparisonObserverShadowActions ComparisonObserverShadowModel ComparisonObserverShadowPresentation
  ComparisonObserverShadowActionRows ComparisonObserverShadowQueries ComparisonObserverRangeTransfer
  ComparisonObserverBoundary

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Δ : Bounds} {hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ}
  {B : Boundary Δ} {names : List ModVar} {base : Nat} {N : Finset ModVar}

def rowModes (p : Ty × Ty) : Finset ModVar := p.1.modVars ∪ p.2.modVars

theorem ofTy_modes (a : Ty) : modes (.ofTy a) = a.modVars := by
  induction a <;> simp_all [CompareTy.ofTy,modes,TypeExpr.modVars]

theorem names_subset {Γ : Bounds} {queries : List CompareTy}
    (hΓ : Γ.modVars ⊆ N) (hq : ∀ a ∈ queries, modes a ⊆ N) :
    ComparisonObserverBoundary.names Γ queries ⊆ N := by
  refine Finset.union_subset hΓ ?_
  intro v hv
  obtain ⟨a,ha,hv⟩ := (mem_allModes _ v).mp hv
  refine (List.mem_append.mp ha).elim (fun ha => ?_) (fun ha => hq _ ha hv)
  obtain ⟨c,hc,ha⟩ := List.mem_flatMap.mp ha
  cases c <;> simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  refine hΓ ((Γ.mem_modVars_iff v).mpr ⟨_,hc,?_⟩)
  rcases ha with rfl | rfl <;>
    first | exact Finset.mem_union_left _ (ofTy_modes _ ▸ hv)
          | exact Finset.mem_union_right _ (ofTy_modes _ ▸ hv)

theorem context_modVars {rows : List (Ty × Ty)}
    (hΔ : Δ.modVars ⊆ N) (hr : ∀ p ∈ rows, rowModes p ⊆ N) :
    (context Δ rows).modVars ⊆ N := by
  intro v hv
  obtain ⟨c,hc,hv⟩ := ((context Δ rows).mem_modVars_iff v).mp hv
  rcases List.mem_append.mp hc with hc | hc
  all_goals obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
  · exact hr _ hp hv
  · exact hΔ ((Δ.mem_modVars_iff v).mpr ⟨p,hp,by cases p <;> exact hv⟩)

theorem context_names {rows : List (Ty × Ty)} {queries : List CompareTy}
    (hΔ : Δ.modVars ⊆ N) (hr : ∀ p ∈ rows, rowModes p ⊆ N)
    (hq : ∀ a ∈ queries, modes a ⊆ N) :
    ComparisonObserverBoundary.names (context Δ rows) queries ⊆ N := by
  exact names_subset (context_modVars hΔ hr) hq

theorem action_rows_modes (hnames : names.toFinset ⊆ N)
    {r : RawRow hn (assign hn B names base)} (hr : r ∈ rows hn B names base) :
    rowModes r.pair ⊆ N := by
  obtain ⟨m,_,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨p,_,hr⟩ := List.mem_flatMap.mp hr
  have hm := (ComparisonFiniteControls.expression_support m).trans hnames
  rcases List.mem_append.mp hr with hr | hr
  all_goals split_ifs at hr <;> simp_all [rowModes,lowerRow,upperRow,
    RawRow.modal_le,RawRow.le_modal,TypeExpr.modVars]

theorem diagramRows_modes {extra : List (RawRow hn (assign hn B names base))}
    (hnames : names.toFinset ⊆ N) (he : ∀ r ∈ extra, rowModes r.pair ⊆ N) :
    ∀ p ∈ diagramRows hn B names base extra, rowModes p ⊆ N := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨v,_,w,_,_,h₁,h₂⟩ := mem_orderRows.mp hp
    simp [rowModes,h₁,h₂,TypeExpr.modVars]
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    exact (List.mem_append.mp hr).elim (action_rows_modes hnames) (he r)

theorem queryBoundary_modes {queries : List CompareTy}
    (hq : ∀ a ∈ queries, modes a ⊆ N) :
    ∀ a ∈ queryBoundary hn B names base queries, modes a ⊆ N := by
  exact fun a ha => (List.mem_append.mp ha).elim
    (fun ha => (List.mem_map.mp ha).elim fun v hv =>
      hv.2 ▸ (show modes (.var v) ⊆ N from Finset.empty_subset N)) (hq a)

theorem diagram_names {extra : List (RawRow hn (assign hn B names base))}
    {queries : List CompareTy} (hΔ : Δ.modVars ⊆ N) (hnames : names.toFinset ⊆ N)
    (he : ∀ r ∈ extra, rowModes r.pair ⊆ N) (hq : ∀ a ∈ queries, modes a ⊆ N) :
    ComparisonObserverBoundary.names (context Δ (diagramRows hn B names base extra))
      (queryBoundary hn B names base queries) ⊆ N := by
  exact context_names hΔ (diagramRows_modes hnames he) (queryBoundary_modes hq)

theorem rawOp_modes (k : ComparisonStructuralLattice.Kind) (a b : Ty) :
    (rawOp k a b).modVars = a.modVars ∪ b.modVars := by
  cases k <;> rfl

theorem anchor_rows_modes {heads : List Ty} (hh : ∀ a ∈ heads, a.modVars ⊆ N)
    {r : RawRow hn (assign hn (Boundary.ofRaw Δ heads) names
      (ComparisonObserverShadowAnchorRows.freshBase heads))}
    (hr : r ∈ ComparisonObserverShadowAnchorRows.rows hn heads names) :
    rowModes r.pair ⊆ N := by
  obtain ⟨i,_,hr⟩ := List.mem_flatMap.mp hr
  split_ifs at hr
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> simpa [rowModes,ComparisonObserverShadowAnchorRows.lowerRow,
    ComparisonObserverShadowAnchorRows.upperRow,anchor_le,le_anchor,TypeExpr.modVars] using
    hh _ (List.getElem_mem i.isLt)

theorem pair_rows_modes {k : ComparisonStructuralLayout.Constructor}
    (hk : k = .prod ∨ k = .sum) (hnames : names.toFinset ⊆ N)
    {r : RawRow hn (assign hn B names base)}
    (hr : r ∈ ComparisonObserverShadowConstructorRows.pairRows hn B names base hk) :
    rowModes r.pair ⊆ N := by
  obtain ⟨m,_,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨q,_,hr⟩ := List.mem_flatMap.mp hr
  have hm := (ComparisonFiniteControls.expression_support m).trans hnames
  rcases List.mem_append.mp hr with hr | hr
  all_goals split_ifs at hr <;> simp_all [rowModes,
    ComparisonObserverShadowConstructorRows.lowerPairRow,ComparisonObserverShadowConstructorRows.upperPairRow,
    RawRow.op_le,RawRow.le_op,TypeExpr.modVars,rawOp_modes]

theorem fn_rows_modes (hnames : names.toFinset ⊆ N)
    {r : RawRow hn (assign hn B names base)}
    (hr : r ∈ ComparisonObserverShadowConstructorRows.fnRows hn B names base) :
    rowModes r.pair ⊆ N := by
  simp only [ComparisonObserverShadowConstructorRows.fnRows,List.mem_flatMap] at hr
  obtain ⟨m,_,q,_,hr⟩ := hr
  have hm := (ComparisonFiniteControls.expression_support m).trans hnames
  rcases List.mem_append.mp hr with hr | hr
  all_goals split_ifs at hr <;> simp_all [rowModes,
    ComparisonObserverShadowConstructorRows.lowerFnRow,ComparisonObserverShadowConstructorRows.upperFnRow,
    RawRow.op_le,RawRow.le_op,TypeExpr.modVars,rawOp_modes]

theorem constructor_rows_modes (hnames : names.toFinset ⊆ N)
    {r : RawRow hn (assign hn B names base)}
    (hr : r ∈ ComparisonObserverShadowConstructorRows.rows hn B names base) :
    rowModes r.pair ⊆ N := by
  exact (List.mem_append.mp hr).elim
    (fun h => (List.mem_append.mp h).elim (pair_rows_modes _ hnames) (pair_rows_modes _ hnames))
    (fn_rows_modes hnames)

end
end ModalityInference.ComparisonFiniteCertificate.DiagramSupport
