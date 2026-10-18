import ModalityInference.Proofs.ComparisonStructuralRealization

/-! Every satisfying coherent finite observer query reconstructs a genuine
observer of the sorted guarded type algebra. Recursion follows the actual
selected layout, preserves whole declared endpoints, and permits constant
children when a finite constructor basis has no cells. -/
namespace ModalityInference.ComparisonStructuralQuerySoundness
open ComparisonAlgebra ComparisonControls ComparisonStructuralLayout ComparisonStructuralWorld
  ComparisonStructuralCoherence ComparisonShapedObserverGluing ComparisonStructuralLattice
  ComparisonStructuralRealization

private theorem basis_none {names modes fixed s} :
    ComparisonStructuralBasis.basis names modes fixed s=none ↔
      ComparisonStructuralBasis.heads names modes fixed s=[] := by
  cases h : ComparisonStructuralBasis.heads names modes fixed s <;>
    simp [ComparisonStructuralBasis.basis,h]

theorem build_based {names modes fixed s layout}
    (h : build names modes fixed s=some layout) :
    layout.shape=s ∧ Based names modes fixed layout := by
  have hb : ∃basis,ComparisonStructuralBasis.basis names modes fixed s=some basis := by
    cases hb : ComparisonStructuralBasis.basis names modes fixed s with
    | some b => exact ⟨b,rfl⟩
    | none =>
      cases s <;> simp [build,hb] at h
  obtain ⟨b,hb⟩ := hb
  obtain ⟨l,hl,hs,_,hbased⟩ := build_complete names modes fixed s hb
  have he := Option.some.inj (h.symm.trans hl)
  exact he.symm ▸ ⟨hs,hbased⟩

inductive Ready (names : List TypeVar) (modes : List ModVar)
    (fixed : TypeVar→ComparisonShape) : Layout→Prop
  | leaf {s b} (basis : ComparisonStructuralBasis.basis names modes fixed s=some b)
      (heads : ∀a∈b.heads,Basic a) : Ready names modes fixed (.leaf s b)
  | fork {k b left right}
      (basis : ComparisonStructuralBasis.basis names modes fixed (k.shape left.shape right.shape)=some b)
      (leftReady : Ready names modes fixed left) (rightReady : Ready names modes fixed right) :
      Ready names modes fixed (.fork k b left right)

theorem Ready.based {names modes fixed layout} (h : Ready names modes fixed layout) :
    Based names modes fixed layout := by
  induction h with
  | leaf hb _ => exact .leaf hb
  | fork hb _ _ ihl ihr => exact .fork hb ihl ihr

private theorem fixed_basic {names fixed s a}
    (h : a∈ComparisonStructuralBasis.fixedHeads names fixed s) : Basic a := by
  obtain ⟨v,_,rfl⟩ := List.mem_map.mp h
  trivial

private theorem leaf_constructor_ready {names modes fixed s t basis} (k : Constructor)
    (hb : ComparisonStructuralBasis.basis names modes fixed (k.shape s t)=some basis)
    (he : ComparisonStructuralBasis.basis names modes fixed s=none ∨
      ComparisonStructuralBasis.basis names modes fixed t=none) :
    Ready names modes fixed (.leaf (k.shape s t) basis) := by
  refine .leaf hb ?_
  intro a ha
  rw [(ComparisonStructuralBasis.basis_spec hb).1] at ha
  rcases he with hs|ht
  · have hs := basis_none.mp hs
    cases k <;> simp [Constructor.shape,ComparisonStructuralBasis.heads,hs,
      ComparisonStructuralBasis.extend,ComparisonStructuralBasis.pairs] at ha
    all_goals exact fixed_basic ha
  · have ht := basis_none.mp ht
    cases k <;> simp [Constructor.shape,ComparisonStructuralBasis.heads,ht,
      ComparisonStructuralBasis.extend,ComparisonStructuralBasis.pairs] at ha
    all_goals exact fixed_basic ha

private theorem build_constructor_ready {names modes fixed s t} (k : Constructor)
    (ihl : ∀left,build names modes fixed s=some left→ Ready names modes fixed left)
    (ihr : ∀right,build names modes fixed t=some right→ Ready names modes fixed right)
    {layout : Layout} (h : build names modes fixed (k.shape s t)=some layout) :
    Ready names modes fixed layout := by
  cases hb : ComparisonStructuralBasis.basis names modes fixed (k.shape s t) <;>
    simp [build_constructor,hb] at h
  rename_i basis
  cases hl : ComparisonStructuralBasis.basis names modes fixed s
  · simp only [hl] at h
    cases Option.some.inj h
    exact leaf_constructor_ready k hb (.inl hl)
  rename_i lb
  cases hr : ComparisonStructuralBasis.basis names modes fixed t
  · simp only [hl,hr] at h
    cases Option.some.inj h
    exact leaf_constructor_ready k hb (.inr hr)
  rename_i rb
  simp only [hl,hr] at h
  cases hleft : build names modes fixed s <;> simp [hleft] at h
  rename_i left
  cases hright : build names modes fixed t <;> simp [hright] at h
  rename_i right
  subst layout
  have hls := (build_based hleft).1
  have hrs := (build_based hright).1
  exact .fork (by simpa only [hls,hrs] using hb) (ihl left hleft) (ihr right hright)

theorem build_ready {names modes fixed s layout} (h : build names modes fixed s=some layout) :
    Ready names modes fixed layout := by
  induction s generalizing layout with
  | var v =>
    cases hb : ComparisonStructuralBasis.basis names modes fixed (.var v) <;> simp [build,hb] at h
    subst layout
    refine .leaf hb ?_
    intro a ha
    rw [(ComparisonStructuralBasis.basis_spec hb).1] at ha
    exact fixed_basic ha
  | unit =>
    cases hb : ComparisonStructuralBasis.basis names modes fixed .unit <;> simp [build,hb] at h
    subst layout
    refine .leaf hb ?_
    intro a ha
    rw [(ComparisonStructuralBasis.basis_spec hb).1] at ha
    rcases List.mem_append.mp ha with ha|ha
    · exact fixed_basic ha
    · simp only [List.mem_singleton] at ha
      subst a
      trivial
  | credit =>
    cases hb : ComparisonStructuralBasis.basis names modes fixed .credit <;> simp [build,hb] at h
    subst layout
    refine .leaf hb ?_
    intro a ha
    rw [(ComparisonStructuralBasis.basis_spec hb).1] at ha
    rcases List.mem_append.mp ha with ha|ha
    · exact fixed_basic ha
    · simp only [List.mem_singleton] at ha
      subst a
      trivial
  | prod s t ihl ihr => exact build_constructor_ready .prod (fun _=>ihl) (fun _=>ihr) h
  | sum s t ihl ihr => exact build_constructor_ready .sum (fun _=>ihl) (fun _=>ihr) h
  | fn s t ihl ihr => exact build_constructor_ready .fn (fun _=>ihl) (fun _=>ihr) h

theorem inputModes_scope (p : SchemePreparation.Prepared) :
    ∀v∈p.assumptions.modVars,v∈ComparisonSelectedBases.inputModes p := by
  intro v hv
  apply (ComparisonSelectedBases.mem_inputModes p v).mpr
  simp [ComparisonWitnessRestriction.inputModes,hv]

theorem fixed_children {k : Constructor} {s t : ComparisonShape} {fixed : TypeVar→ComparisonShape}
    (h : (k.shape s t).subst fixed=k.shape s t) : s.subst fixed=s ∧ t.subst fixed=t := by
  cases k <;> simpa only [Constructor.shape,ComparisonShape.subst,ComparisonShape.prod.injEq,
    ComparisonShape.sum.injEq,ComparisonShape.fn.injEq] using h

theorem Ready.query_realizes {shapeFuel normFuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {originals : List (CompareTy×CompareTy)}
    {pairs : List ComparisonStructuralEndpoints.Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel p solved originals=.success pairs)
    (hdeclared : ∀pair∈ComparisonStructuralEndpoints.declared p,pair∈originals)
    (hΔ : p.assumptions.TypeBoundsDefined)
    {layout : Layout} (hready : Ready (ComparisonSelectedBases.inputNames p)
      (ComparisonSelectedBases.inputModes p) solved.fixedShapes layout)
    (hf : layout.shape.subst solved.fixedShapes=layout.shape)
    {world : Nat→Bool} {q : BoolExpr}
    (hq : query p.assumptions (ComparisonStructuralEndpoints.atShape pairs) layout=some q)
    (hworld : q.eval world=true) (hcoh : (theory layout).eval world=true) :
    Nonempty (Realizes p.assumptions (ComparisonSelectedBases.inputModes p)
      layout.shape layout.basis world) := by
  induction hready generalizing q world with
  | @leaf shape basis hb hbasic =>
    cases hp : ComparisonStructuralNode.prepare basis (ComparisonStructuralEndpoints.atShape pairs shape) <;>
      simp [query,hp] at hq
    rename_i bounds
    subst q
    obtain ⟨view⟩ := nodeTheory_view (inputModes_scope p) hworld
    have hr := resolved_of_normalizer solved.fixedShapes
      (ComparisonShapeSolver.prepare_fixed_equivalent hs) hf
    apply prepared_node_realizes hs hnorm hdeclared hΔ hf hb hp hworld view
      (leafData view) (leaf_coherent view) (fun _ _=>rfl)
      (leaf_heads view hbasic (theory_heads hcoh))
    exact fun a ha=>leaf_range view hr (theory_range hcoh) ha
  | @fork k basis left right hb hl hr ihl ihr =>
    cases hp : ComparisonStructuralNode.prepare basis
        (ComparisonStructuralEndpoints.atShape pairs (k.shape left.shape right.shape)) <;>
      simp [query,Layout.shape,hp] at hq
    rename_i bounds
    cases hql : query p.assumptions (ComparisonStructuralEndpoints.atShape pairs) left <;>
      simp [hql] at hq
    rename_i lq
    cases hqr : query p.assumptions (ComparisonStructuralEndpoints.atShape pairs) right <;>
      simp [hqr] at hq
    rename_i rq
    subst q
    have hfixed := fixed_children (show (k.shape left.shape right.shape).subst solved.fixedShapes=
      k.shape left.shape right.shape from hf)
    have hresolved := resolved_of_normalizer solved.fixedShapes
      (ComparisonShapeSolver.prepare_fixed_equivalent hs) hf
    have hm := (ComparisonStructuralBasis.basis_spec hb).2.1
    have hheads := theory_heads hcoh
    cases hside : world (choiceAtom 0)
    · simp only [BoolExpr.eval,hside,Bool.false_and,Bool.not_false,Bool.true_and,
        Bool.false_or,Bool.or_false,Bool.and_eq_true,rename_eval] at hworld
      have ht := theory_right_parts hside hcoh
      obtain ⟨view⟩ := nodeTheory_view (inputModes_scope p) hworld.1
      obtain ⟨child⟩ := ihr hfixed.2 hqr hworld.2.2.2 ht.2.2.2
      have hi : (childTheory k (ComparisonSelectedBases.inputModes p) rightAtom).eval world=true :=
        by simpa only [hm] using hworld.2.2.1
      apply prepared_node_realizes hs hnorm hdeclared hΔ hf hb hp hworld.1 view
        (nodeData view (fun _=>rightBranch (s:=left.shape) k child.child))
        (fork_right_coherent view child hi ht.2.1) (fun _ _=>rfl)
        (fork_right_heads view child hb (Ready.based hl).basis (Ready.based hr).basis hheads hworld.2.1)
      exact fun a ha=>fork_right_range view child hresolved ht.1 ht.2.2.1 ha
    · simp only [BoolExpr.eval,hside,Bool.true_and,Bool.not_true,Bool.false_and,
        Bool.or_false,Bool.and_eq_true,rename_eval] at hworld
      have ht := theory_left_parts hside hcoh
      obtain ⟨view⟩ := nodeTheory_view (inputModes_scope p) hworld.1
      obtain ⟨child⟩ := ihl hfixed.1 hql hworld.2.2.2 ht.2.2.2
      have hi : (childTheory k (ComparisonSelectedBases.inputModes p) leftAtom).eval world=true :=
        by simpa only [hm] using hworld.2.2.1
      apply prepared_node_realizes hs hnorm hdeclared hΔ hf hb hp hworld.1 view
        (nodeData view (fun _=>leftBranch (t:=right.shape) k child.child))
        (fork_left_coherent view child hi ht.2.1) (fun _ _=>rfl)
        (fork_left_heads view child hb (Ready.based hl).basis (Ready.based hr).basis hheads hworld.2.1)
      exact fun a ha=>fork_left_range view child hresolved ht.1 ht.2.2.1 ha

theorem run_realizes {shapeFuel normFuel fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {originals : List (CompareTy×CompareTy)}
    {pairs : List ComparisonStructuralEndpoints.Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel p solved originals=.success pairs)
    (hdeclared : ∀pair∈ComparisonStructuralEndpoints.declared p,pair∈originals)
    (hΔ : p.assumptions.TypeBoundsDefined)
    {shape : ComparisonShape} {layout : Layout}
    (hb : build (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
      solved.fixedShapes shape=some layout)
    (hf : shape.subst solved.fixedShapes=shape)
    {output : CNF} (hout : ComparisonStructuralCoherence.run fuel p.assumptions
      (ComparisonStructuralEndpoints.atShape pairs) layout=.success output)
    {world : Nat→Bool} (hworld : CNFHolds world output) :
    Nonempty (Realizes p.assumptions (ComparisonSelectedBases.inputModes p)
      layout.shape layout.basis world) := by
  obtain ⟨q,hq,hsem⟩ := ComparisonStructuralCoherence.run_correct hout
  obtain ⟨hqv,hcoh⟩ := (hsem world).mp hworld
  have hfixed : layout.shape.subst solved.fixedShapes=layout.shape := by
    simpa only [(build_based hb).1] using hf
  exact Ready.query_realizes hs hnorm hdeclared hΔ (build_ready hb) hfixed hq hqv hcoh

theorem selected_run_realizes {shapeFuel normFuel fuel first : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {originals : List (CompareTy×CompareTy)}
    {pairs : List ComparisonStructuralEndpoints.Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel p solved originals=.success pairs)
    (hdeclared : ∀pair∈ComparisonStructuralEndpoints.declared p,pair∈originals)
    (hΔ : p.assumptions.TypeBoundsDefined)
    {v : TypeVar} {branch : ComparisonSelectedBases.Branch}
    (hbranch : branch∈ComparisonSelectedBases.prepared first p solved v)
    {layout : Layout} (hb : selected (ComparisonSelectedBases.inputNames p)
      (ComparisonSelectedBases.inputModes p) solved.fixedShapes branch=some layout)
    {output : CNF} (hout : ComparisonStructuralCoherence.run fuel p.assumptions
      (ComparisonStructuralEndpoints.atShape pairs) layout=.success output)
    {world : Nat→Bool} (hworld : CNFHolds world output) :
    Nonempty (Realizes p.assumptions (ComparisonSelectedBases.inputModes p)
      layout.shape layout.basis world) := by
  obtain ⟨raw,_,he,_,_⟩ := ComparisonSelectedBases.bases_origin hbranch
  have hf : branch.shape.subst solved.fixedShapes=branch.shape := by
    rw [he]
    exact ComparisonShapeRetraction.fixedShapes_idempotent hs _
  exact run_realizes hs hnorm hdeclared hΔ hb hf hout hworld

theorem prepared_run_realizes {shapeFuel normFuel fuel first : Nat} {source target : Scheme}
    {solved : ComparisonShapeSolver.Solved} {action : CompareSubstitution}
    {pairs : List ComparisonStructuralEndpoints.Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel (SchemePreparation.prepare [] source target)=
      .success (.solved solved))
    (hnorm : ComparisonStructuralEndpoints.run normFuel (SchemePreparation.prepare [] source target)
      solved action=.success pairs)
    {v : TypeVar} {branch : ComparisonSelectedBases.Branch}
    (hbranch : branch∈ComparisonSelectedBases.prepared first (SchemePreparation.prepare [] source target) solved v)
    {layout : Layout} (hb : selected (ComparisonSelectedBases.inputNames (SchemePreparation.prepare [] source target))
      (ComparisonSelectedBases.inputModes (SchemePreparation.prepare [] source target)) solved.fixedShapes branch=some layout)
    {output : CNF} (hout : ComparisonStructuralCoherence.run fuel (SchemePreparation.prepare [] source target).assumptions
      (ComparisonStructuralEndpoints.atShape pairs) layout=.success output)
    {world : Nat→Bool} (hworld : CNFHolds world output) :
    Nonempty (Realizes (SchemePreparation.prepare [] source target).assumptions
      (ComparisonSelectedBases.inputModes (SchemePreparation.prepare [] source target))
      layout.shape layout.basis world) :=
  selected_run_realizes hs hnorm (fun _ hp=>List.mem_append_left _ hp)
    (SchemePreparation.prepared_typeBoundsDefined source target) hbranch hb hout hworld

end ModalityInference.ComparisonStructuralQuerySoundness
