import ModalityInference.Proofs.ComparisonStructuralQuerySoundness
import ModalityInference.Proofs.ComparisonSignedObservation

/-! Query models reconstruct a recursive trace of genuine selected child
observers. The trace preserves constructor values and interprets shared image
polynomials without requiring exactness of overapproximated range flags. -/
namespace ModalityInference.ComparisonStructuralTrace
open ComparisonAlgebra ComparisonControls ComparisonStructuralLayout ComparisonStructuralWorld
  ComparisonStructuralCoherence ComparisonShapedObserverGluing ComparisonStructuralLattice
  ComparisonStructuralRealization ComparisonStructuralQuerySoundness ComparisonSignedObservation

inductive Trace (Δ : Bounds) (names : List ModVar) :
    (layout : Layout) → (Nat → Bool) → Child Δ layout.shape → Prop
  | leaf {shape basis world} (model : Realizes Δ names shape basis world) :
      Trace Δ names (.leaf shape basis) world model.child
  | left {k basis left right world} (model : Realizes Δ names
        (k.shape left.shape right.shape) basis world) {child : Child Δ left.shape}
      (sub : Trace Δ names left (world ∘ leftAtom) child)
      (side : world (choiceAtom 0)=true)
      (values : ∀a b,Representable Δ left.shape a → Representable Δ right.shape b →
        booleanValue model.child.observer (k.op a b)=
          ComparisonStructuralObservers.leftSign k.kind (booleanValue child.observer a)) :
      Trace Δ names (.fork k basis left right) world model.child
  | right {k basis left right world} (model : Realizes Δ names
        (k.shape left.shape right.shape) basis world) {child : Child Δ right.shape}
      (sub : Trace Δ names right (world ∘ rightAtom) child)
      (side : world (choiceAtom 0)=false)
      (values : ∀a b,Representable Δ left.shape a → Representable Δ right.shape b →
        booleanValue model.child.observer (k.op a b)=booleanValue child.observer b) :
      Trace Δ names (.fork k basis left right) world model.child

theorem Trace.realizes {Δ names layout world child}
    (h : Trace Δ names layout world child) :
    ∃model : Realizes Δ names layout.shape layout.basis world, model.child=child := by
  cases h <;> exact ⟨_,rfl⟩

theorem action_value {Δ names shape basis world} (r : Realizes Δ names shape basis world)
    {m : ModExpr} (hm : Entails Δ (.defined m)) (hs : ∀v∈m.vars,v∈names) (x : Bool) :
    (action m x).eval world=coordinateValue r.view.coordinate x
      (m.complete (ComparisonStructuralWorld.modes names world)) := by
  rw [action_select r.view.first r.view.second]
  rcases r.view.scalar with h|hη
  · simp [h,Coordinate.modalWith,coordinateValue,BoolExpr.eval]
  · apply modalWith_value _ _ hs
    have ht := hm (ComparisonStructuralWorld.modes names world) hη
    simpa only [ModExpr.WellFormed,modes_eval hs] using ht

theorem modal_value {Δ names shape basis world} (r : Realizes Δ names shape basis world)
    {a : CompareTy} (ha : Representable Δ shape a) {m : ModExpr}
    (hm : Entails Δ (.defined m)) (hs : ∀v∈m.vars,v∈names) :
    booleanValue r.child.observer (.modal a m)=
      ((booleanValue r.child.observer a || (action m false).eval world) &&
        (action m true).eval world) := by
  rw [←r.child.action m hm a ha,r.transition,action_value r hm hs false,
    action_value r hm hs true,←coordinate_clamp]

theorem data_realizes_exact {Δ names shape basis world}
    (view : View Δ names basis world) (hm : basis.modes=names)
    (hrep : ∀a∈basis.heads,Representable Δ shape a)
    (d : Data Δ shape) (hr : Resolved Δ shape) (hc : Coherent d)
    (hb : BoundsHold d) (hΔ : Δ.TypeBoundsDefined)
    (ht : ∀m x,d.transition.apply m x=
      coordinateValue view.coordinate x (m.complete (modes names world)))
    (hh : ∀i (hi : i<basis.heads.length),world (headAtom i)=d.value basis.heads[i])
    (hvalues : ∀a,Representable Δ shape a→ range world (d.value a)) :
    ∃model : Realizes Δ names shape basis world,
      ∀a,Representable Δ shape a→ booleanValue model.child.observer a=d.value a := by
  let g := Data.child d hr hc hb hΔ
  have hvalue {a} (ha : Representable Δ shape a) : booleanValue g.observer a=d.value a :=
    d.observer_value hr hc hb hΔ ha
  refine ⟨⟨view,g,ht,?_,?_,?_⟩,fun _ ha=>hvalue ha⟩
  · intro i hi
    exact (view.basis_value hm d.value (fun _ _=>rfl) (fun _ _=>rfl) hh (fun a m=>ht m (d.value a)) i hi).trans
      (hvalue (ComparisonStructuralNode.basis_representable basis hrep _ (List.getElem_mem hi))).symm
  · intro i hi
    exact (hh i hi).trans (hvalue (hrep _ (List.getElem_mem hi))).symm
  · intro x hx
    obtain ⟨a,rfl⟩ := hx
    have he : ComparisonAlgebra.observer g.observer a=d.value a.type := by rfl
    exact he.symm ▸ hvalues a.type ⟨a.shaped,a.defined,a.shape_eq⟩


theorem prepared_node_exact {shapeFuel normFuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {shape : ComparisonShape} {basis : Basis}
    {originals : List (CompareTy×CompareTy)} {pairs : List ComparisonStructuralEndpoints.Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel p solved originals=.success pairs)
    (hdeclared : ∀pair∈ComparisonStructuralEndpoints.declared p,pair∈originals)
    (hΔ : p.assumptions.TypeBoundsDefined)
    (hf : shape.subst solved.fixedShapes=shape)
    (hbasis : ComparisonStructuralBasis.basis (ComparisonSelectedBases.inputNames p)
      (ComparisonSelectedBases.inputModes p) solved.fixedShapes shape=some basis)
    {bounds : List ComparisonStructuralNode.Bound}
    (hp : ComparisonStructuralNode.prepare basis (ComparisonStructuralEndpoints.atShape pairs shape)=some bounds)
    {world : Nat→Bool} (hnode : (nodeTheory p.assumptions basis bounds).eval world=true)
    (view : View p.assumptions (ComparisonSelectedBases.inputModes p) basis world)
    (d : Data p.assumptions shape) (hc : Coherent d)
    (ht : ∀m x,d.transition.apply m x=coordinateValue view.coordinate x
      (m.complete (modes (ComparisonSelectedBases.inputModes p) world)))
    (hh : ∀i (hi : i<basis.heads.length),world (headAtom i)=d.value basis.heads[i])
    (hvalues : ∀a,Representable p.assumptions shape a→ range world (d.value a)) :
    ∃model : Realizes p.assumptions (ComparisonSelectedBases.inputModes p) shape basis world,
      ∀a,Representable p.assumptions shape a→ booleanValue model.child.observer a=d.value a := by
  have hresolved := resolved_of_normalizer solved.fixedShapes
    (ComparisonShapeSolver.prepare_fixed_equivalent hs) hf
  have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ=>(ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
  have hrep : ∀a∈basis.heads,Representable p.assumptions shape a := by
    rw [(ComparisonStructuralBasis.basis_spec hbasis).1]
    exact ComparisonStructuralBasis.heads_representable _ _ _ hshapes shape
  have hm := (ComparisonStructuralBasis.basis_spec hbasis).2.1
  have hval := view.basis_value hm d.value (fun _ _=>rfl) (fun _ _=>rfl) hh (fun a m=>ht m (d.value a))
  have hbound := ComparisonStructuralEndpoints.declared_boundsHold hs d hresolved hf view.scalar ht
    hΔ hnorm hdeclared (nodeTheory_values hnode hp d.value (fun _ _=>rfl) (fun _ _=>rfl) hval)
  exact data_realizes_exact view hm hrep d hresolved hc hbound hΔ ht hh hvalues


theorem query_trace {shapeFuel normFuel : Nat} {p : SchemePreparation.Prepared}
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
    ∃child,Trace p.assumptions (ComparisonSelectedBases.inputModes p) layout world child := by
  induction hready generalizing q world with
  | @leaf shape basis hb hbasic =>
    cases hp : ComparisonStructuralNode.prepare basis (ComparisonStructuralEndpoints.atShape pairs shape) <;>
      simp [query,hp] at hq
    rename_i bounds
    subst q
    obtain ⟨view⟩ := nodeTheory_view (inputModes_scope p) hworld
    have hr := resolved_of_normalizer solved.fixedShapes
      (ComparisonShapeSolver.prepare_fixed_equivalent hs) hf
    obtain ⟨model⟩ := prepared_node_realizes hs hnorm hdeclared hΔ hf hb hp hworld view
      (leafData view) (leaf_coherent view) (fun _ _=>rfl)
      (leaf_heads view hbasic (theory_heads hcoh))
      (fun a ha=>leaf_range view hr (theory_range hcoh) ha)
    exact ⟨model.child,.leaf model⟩
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
      obtain ⟨g,hg⟩ := ihr hfixed.2 hqr hworld.2.2.2 ht.2.2.2
      obtain ⟨child,rfl⟩ := hg.realizes
      have hi : (childTheory k (ComparisonSelectedBases.inputModes p) rightAtom).eval world=true :=
        by simpa only [hm] using hworld.2.2.1
      obtain ⟨model,hvalue⟩ := prepared_node_exact hs hnorm hdeclared hΔ hf hb hp hworld.1 view
        (nodeData view (fun _=>rightBranch (s:=left.shape) k child.child))
        (fork_right_coherent view child hi ht.2.1) (fun _ _=>rfl)
        (fork_right_heads view child hb (Ready.based hl).basis (Ready.based hr).basis hheads hworld.2.1)
        (fun a ha=>fork_right_range view child hresolved ht.1 ht.2.2.1 ha)
      refine ⟨model.child,.right model hg hside ?_⟩
      intro a b ha hb
      have hp : Representable p.assumptions (k.shape left.shape right.shape) (k.op a b) := by
        simpa only [Constructor.kind_shape,Constructor.kind_op] using k.kind.op_representable ha hb
      rw [hvalue _ hp,nodeData_op,rightBranch_value]
    · simp only [BoolExpr.eval,hside,Bool.true_and,Bool.not_true,Bool.false_and,
        Bool.or_false,Bool.and_eq_true,rename_eval] at hworld
      have ht := theory_left_parts hside hcoh
      obtain ⟨view⟩ := nodeTheory_view (inputModes_scope p) hworld.1
      obtain ⟨g,hg⟩ := ihl hfixed.1 hql hworld.2.2.2 ht.2.2.2
      obtain ⟨child,rfl⟩ := hg.realizes
      have hi : (childTheory k (ComparisonSelectedBases.inputModes p) leftAtom).eval world=true :=
        by simpa only [hm] using hworld.2.2.1
      obtain ⟨model,hvalue⟩ := prepared_node_exact hs hnorm hdeclared hΔ hf hb hp hworld.1 view
        (nodeData view (fun _=>leftBranch (t:=right.shape) k child.child))
        (fork_left_coherent view child hi ht.2.1) (fun _ _=>rfl)
        (fork_left_heads view child hb (Ready.based hl).basis (Ready.based hr).basis hheads hworld.2.1)
        (fun a ha=>fork_left_range view child hresolved ht.1 ht.2.2.1 ha)
      refine ⟨model.child,.left model hg hside ?_⟩
      intro a b ha hb
      have hp : Representable p.assumptions (k.shape left.shape right.shape) (k.op a b) := by
        simpa only [Constructor.kind_shape,Constructor.kind_op] using k.kind.op_representable ha hb
      rw [hvalue _ hp,nodeData_op,leftBranch_value]

theorem run_trace {shapeFuel normFuel fuel : Nat} {p : SchemePreparation.Prepared}
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
    ∃child,Trace p.assumptions (ComparisonSelectedBases.inputModes p) layout world child := by
  obtain ⟨q,hq,hsem⟩ := ComparisonStructuralCoherence.run_correct hout
  obtain ⟨hqv,hcoh⟩ := (hsem world).mp hworld
  have hfixed : layout.shape.subst solved.fixedShapes=layout.shape := by
    simpa only [(build_based hb).1] using hf
  exact query_trace hs hnorm hdeclared hΔ (build_ready hb) hfixed hq hqv hcoh



theorem realizes_head_mem {Δ names shape basis world} (r : Realizes Δ names shape basis world)
    {a : CompareTy} (ha : a∈basis.heads) :
    world (headAtom (basis.heads.idxOf a))=booleanValue r.child.observer a := by
  have hi := List.idxOf_lt_length_of_mem ha
  have he : basis.heads[basis.heads.idxOf a]=a := by
    simpa only [List.idxOf,beq_iff_eq] using
      (List.findIdx_getElem (xs:=basis.heads) (p:=(·==a)) (w:=hi))
  exact (r.heads _ hi).trans (congrArg (booleanValue r.child.observer) he)

def Reads {Δ : Bounds} (names : List ModVar) (keys : List Nat)
    (σ : CompareSubstitution) (layout : Layout) (world : Nat→Bool)
    (images : ComparisonSignedEndpoints.Call→Bool) : Prop :=
  ∀route node,nodeAt layout route=some node→
    ∀child,Trace Δ names node (world ∘ routeAtom route) child→
      ∀n∈keys,Representable Δ node.shape (σ.type (.flex n))→
        images ⟨n,route⟩=booleanValue child.observer (σ.type (.flex n))

theorem Reads.child {Δ names keys σ kind basis left right world images}
    (h : @Reads Δ names keys σ (.fork kind basis left right) world images) (direction : Bool) :
    @Reads Δ names keys σ (if direction then right else left)
      (world ∘ (if direction then rightAtom else leftAtom)) (shifted direction images) := by
  intro route node hn child ht n hnkey hr
  apply h (direction::route) node hn child _ n hnkey hr
  simpa only [Function.comp_def,routeAtom_cons] using ht


open ComparisonSignedEndpoints in
theorem interpret_trace {Δ names labels keys σ layout a}
    (he : Endpoint Δ labels keys σ layout a) {modes} (hv : Valid Δ modes layout)
    (hlabels : ∀g∈labels,∀v∈g.expression.vars,v∈names)
    {child : Child Δ layout.shape} {world images}
    (ht : Trace Δ names layout world child) (hi : @Reads Δ names keys σ layout world images) :
    interpret keys (context layout σ.mode) world images [] a=booleanValue child.observer (σ.ty a) := by
  induction he generalizing world images with
  | @image layout n hn hr =>
    have hr := hi [] layout (nodeAt_nil layout) child (by simpa only [routeAtom_nil,Function.comp_id] using ht) n hn hr
    simpa only [interpret,reference,List.contains_iff_mem,hn,if_true,ComparisonSignedEndpoints.Data.eval,beq_true] using hr
  | @fixed layout v hn hf hh =>
    obtain ⟨model,rfl⟩ := ht.realizes
    have ho := realizes_head_mem model hh
    cases v with
    | flex n =>
      have hnot : ¬n∈keys := fun h => hn n h rfl
      simpa [interpret,reference,List.contains_iff_mem,hnot,ComparisonSignedEndpoints.Data.eval,context,nodeAt,
        routeAtom,BoolExpr.eval,CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf] using ho
    | rigid n =>
      simpa [interpret,reference,ComparisonSignedEndpoints.Data.eval,context,nodeAt,routeAtom,BoolExpr.eval,
        CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf] using ho
  | unit hh =>
    obtain ⟨model,rfl⟩ := ht.realizes
    simpa only [interpret,context,nodeAt,routeAtom,BoolExpr.eval,CompareTy.ofTy] using realizes_head_mem model hh
  | credit hh =>
    obtain ⟨model,rfl⟩ := ht.realizes
    simpa only [interpret,context,nodeAt,routeAtom,BoolExpr.eval,CompareTy.ofTy] using realizes_head_mem model hh
  | @node kind basis left right a b hl hr ihl ihr =>
    cases hv with
    | fork hh hm hvl hvr hc =>
      rw [node_interpret,publicOp_subst]
      cases ht with
      | left model hsub hside hvalues =>
        rw [hside]
        simp only [if_true]
        rw [interpret_child]
        simp only [Bool.false_eq_true,if_false]
        rw [ihl hvl hsub (hi.child false)]
        exact (hvalues _ _ (hl.representable hvl) (hr.representable hvr)).symm
      | right model hsub hside hvalues =>
        rw [hside]
        simp only [Bool.false_eq_true,if_false]
        rw [interpret_child]
        simp only [if_true]
        rw [ihr hvr hsub (hi.child true)]
        exact (hvalues _ _ (hl.representable hvl) (hr.representable hvr)).symm
  | @modal layout a m inner hlabel ih =>
    rw [interpret,ih hv ht hi]
    simp only [context,rename_eval,routeAtom,Function.comp_id]
    obtain ⟨model,rfl⟩ := ht.realizes
    obtain ⟨g,hg,he⟩ := hlabel
    exact (modal_value model (inner.representable hv) (he ▸ g.defined)
      (he ▸ hlabels g hg)).symm

theorem polynomialImages_reads {Δ names keys σ layout world} (polynomials : Nat → CNF)
    (hp : ∀route node, nodeAt layout route=some node → ∀n∈keys,
      Representable Δ node.shape (σ.type (.flex n)) →
      ComparisonLatticeCompiler.compile node.basis (σ.type (.flex n))=some (polynomials n)) :
    @Reads Δ names keys σ layout world (polynomialImages polynomials world) := by
  intro route node hn child ht n hk hr
  obtain ⟨model,rfl⟩ := ht.realizes
  apply Bool.eq_iff_iff.mpr
  exact (ComparisonStructuralMatrix.cnfValue_correct _ _).trans
    (ComparisonStructuralNode.compiled_value (hp route node hn n hk hr)
      (booleanValue model.child.observer) (booleanValue_join model.child.observer) (booleanValue_meet model.child.observer) model.types)


theorem polynomialImages_reads_of_bases {Δ traceNames keys σ layout world names modes shapes}
    (hb : Based names modes shapes layout) (hmodel : ComparisonShape.Models Δ shapes)
    (hf : layout.shape.subst shapes=layout.shape) (polynomials : Nat → CNF)
    (hp : ∀n∈keys, ∃basis,
      ComparisonStructuralBasis.basis names modes shapes ((σ.type (.flex n)).shape.subst shapes)=some basis ∧
      ComparisonLatticeCompiler.compile basis (σ.type (.flex n))=some (polynomials n)) :
    @Reads Δ traceNames keys σ layout world (polynomialImages polynomials world) := by
  apply polynomialImages_reads polynomials
  intro route node hn n hk hr
  obtain ⟨basis,hbasis,hcompile⟩ := hp n hk
  have he : (σ.type (.flex n)).shape.subst shapes=node.shape :=
    (hr.2.2 shapes hmodel).trans (nodeAt_fixed hf hn)
  rw [he] at hbasis
  have hbnode := (nodeAt_based hb hn).basis
  have hbe : basis=node.basis := Option.some.inj (hbasis.symm.trans hbnode)
  exact hbe ▸ hcompile


end ModalityInference.ComparisonStructuralTrace
