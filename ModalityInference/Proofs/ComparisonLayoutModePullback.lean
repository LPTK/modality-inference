import ModalityInference.Proofs.ComparisonLayoutStrategy
import ModalityInference.Proofs.ComparisonObserverModeModel
import ModalityInference.Proofs.ComparisonReifiedEndpointTheory

namespace ModalityInference.ComparisonLayoutModePullback
open ComparisonAlgebra ComparisonControls ComparisonStructuralLayout ComparisonStructuralAlignment
  ComparisonStructuralCoherence ComparisonSignedObservation ComparisonSignedEndpoints
  ComparisonModeRestriction

abbrev acted (ms : ModVar→ModExpr) (world : Nat→Bool) : Nat→Bool :=
  ComparisonLayoutWorlds.apply (SchemeModeSynthesis.strategy ms) world

@[simp] theorem acted_basis (ms : ModVar→ModExpr) (world : Nat→Bool) (i : Nat) :
    acted ms world (basisAtom i)=world (basisAtom i) := by
  simp [acted,ComparisonLayoutWorlds.apply,basisAtom]
@[simp] theorem acted_head (ms : ModVar→ModExpr) (world : Nat→Bool) (i : Nat) :
    acted ms world (headAtom i)=world (headAtom i) := by
  simp [acted,ComparisonLayoutWorlds.apply,headAtom]
@[simp] theorem acted_choice (ms : ModVar→ModExpr) (world : Nat→Bool) (i : Nat) :
    acted ms world (choiceAtom i)=world (choiceAtom i) := by
  simp [acted,ComparisonLayoutWorlds.apply,choiceAtom]
@[simp] theorem acted_mode (ms : ModVar→ModExpr) (world : Nat→Bool) (i : Nat) :
    acted ms world (modeAtom i)=SchemeModeSynthesis.strategy ms (world ∘ modeAtom) i := by
  have hi : (4*i+2)/4=i := by omega
  simp [acted,ComparisonLayoutWorlds.apply,modeAtom,hi,Function.comp_def]

theorem acted_left (ms : ModVar→ModExpr) (world : Nat→Bool) :
    acted ms world ∘ leftAtom=acted ms (world ∘ leftAtom) := by
  funext i
  simp only [acted,ComparisonLayoutWorlds.apply,Function.comp_apply,ComparisonLayoutWorlds.location_left,
    routeAtom_cons,Bool.false_eq_true,ite_false]

theorem acted_right (ms : ModVar→ModExpr) (world : Nat→Bool) :
    acted ms world ∘ rightAtom=acted ms (world ∘ rightAtom) := by
  funext i
  simp only [acted,ComparisonLayoutWorlds.apply,Function.comp_apply,ComparisonLayoutWorlds.location_right,
    routeAtom_cons,ite_true]

theorem observes_acted {Δ shape basis f c η world}
    (ho : @Observes Δ shape basis f c η world) (ms : ModVar→ModExpr) :
    Observes basis f c (ComparisonObserverModePullback.world ms η) (acted ms world) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi;simpa using ho.types i hi
  · intro i hi;simpa using ho.heads i hi
  · intro i
    rw [acted_mode,ComparisonObserverModePullback.encode_world]
    exact congrFun (congrArg (SchemeModeSynthesis.strategy ms) (funext ho.modes)) i
  · simpa using ho.first
  · simpa using ho.second
  · simpa using ho.falseRange
  · simpa using ho.trueRange

 theorem realized_query {Δ : Bounds} {modes : List ModVar} {labels : List (GuardedMode Δ)}
    (hlabels : ∀b : Basis,b.modes=modes→∀p∈b.modalPairs,∃m∈labels,m.expression=p.2)
    {endpoints : ComparisonShape→List (CompareTy×CompareTy)}
    (hinput : ∀s,∀pair∈endpoints s,AlgebraSubtype Δ pair.1 pair.2)
    {layout : Layout} (hv : Valid Δ modes layout) {q : BoolExpr}
    (hq : query Δ endpoints layout=some q)
    {f : LatticeHom (Order Δ layout.shape) Bool} {c η world}
    (hr : Realized Δ labels layout f c η world) : q.eval world=true := by
  induction hr generalizing q with
  | @leaf s b f c η world hm ho =>
    cases hv with
    | leaf hheads hmodes =>
      cases hb : ComparisonStructuralNode.prepare b (endpoints s) <;> simp [query,hb] at hq
      subst q
      exact nodeTheory_observer hm ho hb hheads (hlabels b hmodes) (hinput s)
  | @left k b left right f c η world g child θ hm ho hside inherit hvalues hsub ih =>
    cases hv with
    | fork hheads hmodes hlvalid hrvalid hcells =>
      cases hb : ComparisonStructuralNode.prepare b (endpoints (k.shape left.shape right.shape)) <;>
        simp [query,Layout.shape,hb] at hq
      cases hql : query Δ endpoints left <;> simp [hql] at hq
      cases hqr : query Δ endpoints right <;> simp [hqr] at hq
      subst q
      have hlt:=ComparisonStructuralNode.basis_representable left.basis hlvalid.heads
      have hrt:=ComparisonStructuralNode.basis_representable right.basis hrvalid.heads
      have hn:=nodeTheory_observer hm ho hb hheads (hlabels b hmodes) (hinput _)
      have hl:=links_left ho hsub.observes hlt hrt hcells hvalues
      have hc:=childTheory_observer (modes:=b.modes) ho hsub.observes inherit
      have ht:=ih hlvalid hql
      simp only [BoolExpr.eval,rename_eval,hside]
      simp [hn,hl,hc,ht]
  | @right k b left right f c η world g child θ hm ho hside inherit hvalues hsub ih =>
    cases hv with
    | fork hheads hmodes hlvalid hrvalid hcells =>
      cases hb : ComparisonStructuralNode.prepare b (endpoints (k.shape left.shape right.shape)) <;>
        simp [query,Layout.shape,hb] at hq
      cases hql : query Δ endpoints left <;> simp [hql] at hq
      cases hqr : query Δ endpoints right <;> simp [hqr] at hq
      subst q
      have hlt:=ComparisonStructuralNode.basis_representable left.basis hlvalid.heads
      have hrt:=ComparisonStructuralNode.basis_representable right.basis hrvalid.heads
      have hn:=nodeTheory_observer hm ho hb hheads (hlabels b hmodes) (hinput _)
      have hl:=links_right ho hsub.observes hlt hrt hcells hvalues
      have hc:=childTheory_observer (modes:=b.modes) ho hsub.observes inherit
      have ht:=ih hrvalid hqr
      simp only [BoolExpr.eval,rename_eval,hside]
      simp [hn,hl,hc,ht]

inductive Mapped {Δ : Bounds} {ms : ModVar→ModExpr} (h : Fixed Δ ms) (labels : List (GuardedMode Δ)) :
    (layout : Layout) → LatticeHom (Order Δ layout.shape) Bool → Coordinate →
      (ModVar → Mode) → (Nat → Bool) → Prop
  | leaf {s b f c η world}
      (model : Model f labels c η) (observes : Observes b (ComparisonObserverModePullback.observer h f) c η world) :
      Mapped h labels (.leaf s b) f c η world
  | left {k b left right f c η world child θ}
      (g : LatticeHom (Order Δ left.shape) Bool)
      (model : Model f labels c η) (observes : Observes b (ComparisonObserverModePullback.observer h f) c η world)
      (side : world (choiceAtom 0) = true)
      (inheritance : k.dual = true ∨ θ = η ∧ (child = .unaffected ∨ child = c))
      (values : ∀a d, observer f (k.carrier a d) =
        ComparisonStructuralObservers.leftSign k.kind (observer g a))
      (subtree : Mapped h labels left g child θ (world ∘ leftAtom)) :
      Mapped h labels (.fork k b left right) f c η world
  | right {k b left right f c η world child θ}
      (g : LatticeHom (Order Δ right.shape) Bool)
      (model : Model f labels c η) (observes : Observes b (ComparisonObserverModePullback.observer h f) c η world)
      (side : world (choiceAtom 0) = false)
      (inheritance : k.dual = true ∨ θ = η ∧ (child = .unaffected ∨ child = c))
      (values : ∀a d, observer f (k.carrier a d) = observer g d)
      (subtree : Mapped h labels right g child θ (world ∘ rightAtom)) :
      Mapped h labels (.fork k b left right) f c η world



theorem mapped_complete {Δ : Bounds} {ms : ModVar→ModExpr} (h : Fixed Δ ms)
    {modes : List ModVar} {labels : List (GuardedMode Δ)}
    (htests : ∀m∈tests modes,∃n∈labels,n.expression=m)
    (hsupport : ∀m∈labels,∀v∈m.expression.freeVariables,v∈modes)
    {layout : Layout} (hv : Valid Δ modes layout)
    (f : LatticeHom (Order Δ layout.shape) Bool) {c : Coordinate} {η : ModVar→Mode}
    (hm : Model f labels c η) : ∃world,Mapped h labels layout f c η world := by
  induction hv generalizing c η with
  | @leaf s b hheads hmodes =>
    let g:=ComparisonObserverModePullback.observer h f
    exact ⟨combine (localWorld b g c η false) (fun _=>false) (fun _=>false),
      .leaf hm (combine_observes b g c η false _ _)⟩
  | @fork k b left right hheads hmodes hlvalid hrvalid hcells ihl ihr =>
    let a₀:=represented (hlvalid.heads left.basis.head (by simp [Basis.heads]))
    let b₀:=represented (hrvalid.heads right.basis.head (by simp [Basis.heads]))
    rcases constructor_choice k f a₀ b₀ hm htests hsupport with
      ⟨g,child,θ,hg,hi,hvalue⟩|⟨g,child,θ,hg,hi,hvalue⟩
    · obtain ⟨wl,htree⟩:=ihl g hg
      let f':=ComparisonObserverModePullback.observer h f
      let world:=combine (localWorld b f' c η true) wl (fun _=>false)
      refine ⟨world,.left g hm (combine_observes b f' c η true _ _)
        (by simp [world,choiceAtom,localWorld]) hi hvalue ?_⟩
      simpa only [world,Function.comp_def,combine_left] using htree
    · obtain ⟨wr,htree⟩:=ihr g hg
      let f':=ComparisonObserverModePullback.observer h f
      let world:=combine (localWorld b f' c η false) (fun _=>false) wr
      refine ⟨world,.right g hm (combine_observes b f' c η false _ _)
        (by simp [world,choiceAtom,localWorld]) hi hvalue ?_⟩
      simpa only [world,Function.comp_def,combine_right] using htree

theorem pulled_left {Δ : Bounds} {ms : ModVar→ModExpr} (h : Fixed Δ ms)
    {s t : ComparisonShape} (k : Constructor)
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (g : LatticeHom (Order Δ s) Bool)
    (hv : ∀a b,observer f (k.carrier a b)=ComparisonStructuralObservers.leftSign k.kind (observer g a)) :
    ∀a b,observer (ComparisonObserverModePullback.observer h f) (k.carrier a b)=
      ComparisonStructuralObservers.leftSign k.kind (observer (ComparisonObserverModePullback.observer h g) a) := by
  intro a b
  cases k <;> exact hv (ComparisonObserverModePullback.carrier h a) (ComparisonObserverModePullback.carrier h b)

theorem pulled_right {Δ : Bounds} {ms : ModVar→ModExpr} (h : Fixed Δ ms)
    {s t : ComparisonShape} (k : Constructor)
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (g : LatticeHom (Order Δ t) Bool)
    (hv : ∀a b,observer f (k.carrier a b)=observer g b) :
    ∀a b,observer (ComparisonObserverModePullback.observer h f) (k.carrier a b)=
      observer (ComparisonObserverModePullback.observer h g) b := by
  intro a b
  cases k <;> exact hv (ComparisonObserverModePullback.carrier h a) (ComparisonObserverModePullback.carrier h b)

theorem Mapped.acted {Δ : Bounds} {ms : ModVar→ModExpr} {h : Fixed Δ ms}
    {raw closed : List (GuardedMode Δ)}
    (hlabels : ∀m∈raw,∃n∈closed,n.expression=m.expression.subst ms)
    {layout : Layout} {f : LatticeHom (Order Δ layout.shape) Bool} {c η world}
    (ht : Mapped h closed layout f c η world) :
    Realized Δ raw layout (ComparisonObserverModePullback.observer h f) c
      (ComparisonObserverModePullback.world ms η) (acted ms world) := by
  induction ht with
  | leaf hm ho => exact .leaf (ComparisonObserverModePullback.model h _ hlabels hm) (observes_acted ho ms)
  | @left k b left right f c η world child θ g hm ho hside inherit hvalues hsub ih =>
    refine Realized.left (child:=child) (θ:=ComparisonObserverModePullback.world ms θ)
      (ComparisonObserverModePullback.observer h g)
      (ComparisonObserverModePullback.model h f hlabels hm) (observes_acted ho ms)
      (by simpa using hside) ?_ (pulled_left h k f g hvalues) ?_
    · exact inherit.imp_right (fun hi=>⟨congrArg (ComparisonObserverModePullback.world ms) hi.1,hi.2⟩)
    · rw [acted_left]
      exact ih
  | @right k b left right f c η world child θ g hm ho hside inherit hvalues hsub ih =>
    refine Realized.right (child:=child) (θ:=ComparisonObserverModePullback.world ms θ)
      (ComparisonObserverModePullback.observer h g)
      (ComparisonObserverModePullback.model h f hlabels hm) (observes_acted ho ms)
      (by simpa using hside) ?_ (pulled_right h k f g hvalues) ?_
    · exact inherit.imp_right (fun hi=>⟨congrArg (ComparisonObserverModePullback.world ms) hi.1,hi.2⟩)
    · rw [acted_right]
      exact ih


theorem Mapped.model {Δ ms h labels layout f c η world}
    (ht : @Mapped Δ ms h labels layout f c η world) : Model f labels c η := by
  cases ht <;> assumption

theorem Mapped.observes {Δ ms h labels layout f c η world}
    (ht : @Mapped Δ ms h labels layout f c η world) :
    Observes layout.basis (ComparisonObserverModePullback.observer h f) c η world := by
  cases ht <;> assumption

theorem action_observed {Δ shape shape' basis labels c η world}
    {f : LatticeHom (Order Δ shape) Bool} {g : LatticeHom (Order Δ shape') Bool}
    (hm : Model f labels c η) (ho : Observes basis g c η world)
    (m : GuardedMode Δ) (x : Bool) :
    (action m.expression x).eval world=coordinateValue c x (m.value η) := by
  rw [action_select ho.first ho.second]
  exact Coordinate.modalWith_eval ho.modes (hm.modeModel.elim Or.inl (fun hη=>Or.inr (m.eval η hη)))

theorem modal_observed {Δ shape shape' basis labels c η world}
    {f : LatticeHom (Order Δ shape) Bool} {g : LatticeHom (Order Δ shape') Bool}
    (hm : Model f labels c η) (ho : Observes basis g c η world)
    {a : CompareTy} (ha : Representable Δ shape a) {m : ModExpr}
    (hlabel : ∃n∈labels,n.expression=m) :
    booleanValue f (.modal a m)=
      ((booleanValue f a || (action m false).eval world) && (action m true).eval world) := by
  obtain ⟨n,hn,rfl⟩:=hlabel
  rw [action_observed hm ho n false,action_observed hm ho n true,←coordinate_clamp]
  have h:=hm.action (represented ha) n hn
  rw [booleanValue_represented f a ha]
  have han : Representable Δ shape (.modal a n.expression) :=
    ⟨ha.1,CompareTy.definedUnder_modal_iff.mpr ⟨ha.2.1,n.defined⟩,ha.2.2⟩
  rw [booleanValue_represented f _ han]
  exact h

def Reads {Δ : Bounds} {ms : ModVar→ModExpr} (h : Fixed Δ ms)
    (labels : List (GuardedMode Δ)) (keys : List Nat) (σ : CompareSubstitution)
    (layout : Layout) (world : Nat→Bool) (images : Call→Bool) : Prop :=
  ∀route node,nodeAt layout route=some node→
    ∀(f : LatticeHom (Order Δ node.shape) Bool) c η,
      Mapped h labels node f c η (world ∘ routeAtom route)→
      ∀n∈keys,Representable Δ node.shape (σ.type (.flex n))→
        images ⟨n,route⟩=booleanValue f (σ.type (.flex n))

theorem Reads.child {Δ ms h labels keys σ kind basis left right world images}
    (hr : @Reads Δ ms h labels keys σ (.fork kind basis left right) world images) (direction : Bool) :
    Reads h labels keys σ (if direction then right else left)
      (world ∘ (if direction then rightAtom else leftAtom)) (shifted direction images) := by
  intro route node hn f c η ht n hnkey hp
  apply hr (direction::route) node hn f c η _ n hnkey hp
  simpa only [Function.comp_def,routeAtom_cons] using ht

theorem interpret_value {Δ ms h labels keys σ layout a}
    (he : Endpoint Δ labels keys σ layout a) {modes} (hv : Valid Δ modes layout)
    {f : LatticeHom (Order Δ layout.shape) Bool} {c η world images}
    (ht : @Mapped Δ ms h labels layout f c η world) (hi : Reads h labels keys σ layout world images) :
    interpret keys (context layout σ.mode) world images [] a=booleanValue f (σ.ty a) := by
  induction he generalizing c η world images with
  | @image layout n hn hr =>
    have hr := hi [] layout (nodeAt_nil layout) f c η ht n hn hr
    simpa only [interpret,reference,List.contains_iff_mem,hn,if_true,Data.eval,beq_true] using hr
  | @fixed layout v hn hf hh =>
    have ho := ht.observes.head_mem hh
    rw [ComparisonObserverModePullback.observer_value h f (hv.heads _ hh)] at ho
    simp only [CompareTy.subst] at ho
    cases v with
    | flex n =>
      have hnot : ¬n∈keys := fun h => hn n h rfl
      simpa [interpret,reference,List.contains_iff_mem,hnot,Data.eval,context,nodeAt,
        routeAtom,BoolExpr.eval,CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf] using ho
    | rigid n =>
      simpa [interpret,reference,Data.eval,context,nodeAt,routeAtom,BoolExpr.eval,
        CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf] using ho
  | unit hh =>
    have ho:=ht.observes.head_mem hh
    rw [ComparisonObserverModePullback.observer_value h f (hv.heads _ hh)] at ho
    simpa only [interpret,context,nodeAt,routeAtom,BoolExpr.eval,CompareTy.ofTy,CompareTy.subst] using ho
  | credit hh =>
    have ho:=ht.observes.head_mem hh
    rw [ComparisonObserverModePullback.observer_value h f (hv.heads _ hh)] at ho
    simpa only [interpret,context,nodeAt,routeAtom,BoolExpr.eval,CompareTy.ofTy,CompareTy.subst] using ho
  | @node kind basis left right a b hl hr ihl ihr =>
    cases hv with
    | fork hh hm hvl hvr hc =>
      rw [node_interpret,publicOp_subst]
      cases ht with
      | left g hmodel ho hside inherit hvalues hsub =>
        rw [hside]
        simp only [if_true]
        rw [interpret_child]
        simp only [Bool.false_eq_true,if_false]
        rw [ihl hvl hsub (hi.child false)]
        exact (constructor_left kind f g hvalues (hl.representable hvl) (hr.representable hvr)).symm
      | right g hmodel ho hside inherit hvalues hsub =>
        rw [hside]
        simp only [Bool.false_eq_true,if_false]
        rw [interpret_child]
        simp only [if_true]
        rw [ihr hvr hsub (hi.child true)]
        exact (constructor_right kind f g hvalues (hl.representable hvl) (hr.representable hvr)).symm
  | @modal layout a m inner hlabel ih =>
    rw [interpret,ih hv ht hi]
    simp only [context,rename_eval,routeAtom,Function.comp_id]
    exact (modal_observed ht.model ht.observes (inner.representable hv) hlabel).symm


theorem polynomialImages_reads {Δ ms h labels keys σ layout world names modes shapes}
    (hb : Based names modes shapes layout)
    (hshapes : ∀v,ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (hmodel : ComparisonShape.Models Δ shapes)
    (hf : layout.shape.subst shapes=layout.shape) (polynomials : Nat→CNF)
    (hp : ∀n∈keys,∃basis raw,
      ComparisonStructuralBasis.basis names modes shapes ((σ.type (.flex n)).shape.subst shapes)=some basis ∧
      ComparisonPropagation.reify basis.types (polynomials n)=some raw ∧
      σ.type (.flex n)=raw.subst CompareTy.var ms) :
    @Reads Δ ms h labels keys σ layout world (polynomialImages polynomials world) := by
  intro route node hn f c η ht n hk hr
  obtain ⟨basis,raw,hbasis,hreify,heq⟩ := hp n hk
  have he : (σ.type (.flex n)).shape.subst shapes=node.shape :=
    (hr.2.2 shapes hmodel).trans (nodeAt_fixed hf hn)
  rw [he] at hbasis
  have hbnode := nodeAt_based hb hn
  have hbe : basis=node.basis := Option.some.inj (hbasis.symm.trans hbnode.basis)
  subst basis
  have hraw : Representable Δ node.shape raw :=
    ComparisonPropagation.reify_property hreify _
      (ComparisonStructuralNode.basis_representable node.basis (hbnode.valid hshapes).heads)
      (fun _ _=>ComparisonStructuralLattice.representable_typeOp true)
      (fun _ _=>ComparisonStructuralLattice.representable_typeOp false)
  apply Bool.eq_iff_iff.mpr
  have hv := ComparisonReifiedEndpointTheory.reified_value hreify
    (booleanValue (ComparisonObserverModePullback.observer h f))
    (booleanValue_join _) (booleanValue_meet _) ht.observes.types
  rw [ComparisonObserverModePullback.observer_value h f hraw,←heq] at hv
  exact (ComparisonStructuralMatrix.cnfValue_correct _ _).trans hv


theorem run_mapped_labels {Δ : Bounds} {ms : ModVar→ModExpr} (h : Fixed Δ ms)
    {names modes fixed layout} (hb : Based names modes fixed layout)
    (hs : ∀v,ComparisonShape.Equivalent Δ (.var v) (fixed v))
    {closed : List (GuardedMode Δ)}
    (htests : ∀m∈tests modes,∃n∈closed,n.expression=m)
    (hlabels : ∀m∈ComparisonStructuralLayout.labels Δ modes,
      ∃n∈closed,n.expression=m.expression.subst ms)
    (hsupport : ∀m∈closed,∀v∈m.expression.freeVariables,v∈modes)
    {endpoints : ComparisonShape→List (CompareTy×CompareTy)}
    (hinput : ∀s,∀pair∈endpoints s,AlgebraSubtype Δ pair.1 pair.2)
    {fuel output} (hr : ComparisonStructuralCoherence.run fuel Δ endpoints layout=.success output)
    (f : LatticeHom (Order Δ layout.shape) Bool) :
    ∃c η world,CNFHolds (acted ms world) output ∧ Mapped h closed layout f c η world := by
  have hv:=hb.valid hs
  let anchor:=represented (hv.heads layout.basis.head (by simp [Basis.heads]))
  obtain ⟨c,η,hm⟩:=observer_model f anchor closed
  obtain ⟨q,hq,hqcorrect⟩:=ComparisonStructuralCoherence.run_correct hr
  obtain ⟨world,htree⟩:=mapped_complete h htests hsupport hv f hm
  have hraw:=htree.acted hlabels
  have hqtrue:=realized_query (fun b=>labels_basis Δ b) hinput hv hq hraw
  have htop : ∃m∈labels Δ modes,m.expression=.top :=
    labels_mem.mpr (by simp [labelExpressions,tests,ModExpr.top])
  have hbottom : ∃m∈labels Δ modes,m.expression=.const Mode.bottom :=
    labels_mem.mpr (by simp [labelExpressions])
  exact ⟨c,η,world,(hqcorrect _).mpr ⟨hqtrue,Realized.theory hraw hv hbottom htop⟩,htree⟩

/-- A query at the common strategy's output worlds is sufficient for the
closed type images. The raw mode input is retained for every endpoint action. -/
theorem endpoint_sound {shapeFuel normFuel fuel : Nat} {p : SchemePreparation.Prepared}
    {solved : ComparisonShapeSolver.Solved} {pairs : List ComparisonStructuralEndpoints.Pair}
    (hs : ComparisonShapeSolver.prepare shapeFuel p=.success (.solved solved))
    (hnorm : ComparisonStructuralEndpoints.normalizeList normFuel p solved
      (ComparisonStructuralEndpoints.declared p)=.success pairs)
    (hΔ : p.assumptions.TypeBoundsDefined)
    {shape : ComparisonShape} {layout : Layout}
    (hbuild : build (ComparisonSelectedBases.inputNames p) (ComparisonSelectedBases.inputModes p)
      solved.fixedShapes shape=some layout)
    (hf : shape.subst solved.fixedShapes=shape)
    {theory : CNF} (htheory : ComparisonStructuralCoherence.run fuel p.assumptions
      (ComparisonStructuralEndpoints.atShape pairs) layout=.success theory)
    {keys : List Nat} {σ : CompareSubstitution} (hμ : Fixed p.assumptions σ.mode)
    {closed : List (GuardedMode p.assumptions)} {left right : Ty}
    (hl : Endpoint p.assumptions closed keys σ layout left)
    (hr : Endpoint p.assumptions closed keys σ layout right)
    (htests : ∀m∈tests (ComparisonSelectedBases.inputModes p),∃n∈closed,n.expression=m)
    (hlabels : ∀m∈labels p.assumptions (ComparisonSelectedBases.inputModes p),
      ∃n∈closed,n.expression=m.expression.subst σ.mode)
    (hsupport : ∀m∈closed,∀v∈m.expression.freeVariables,v∈ComparisonSelectedBases.inputModes p)
    (polynomials : Nat→CNF)
    (hp : ∀n∈keys,∃basis raw,
      ComparisonStructuralBasis.basis (ComparisonSelectedBases.inputNames p)
        (ComparisonSelectedBases.inputModes p) solved.fixedShapes
        ((σ.type (.flex n)).shape.subst solved.fixedShapes)=some basis ∧
      ComparisonPropagation.reify basis.types (polynomials n)=some raw ∧
      σ.type (.flex n)=raw.subst CompareTy.var σ.mode)
    (hall : ∀world,CNFHolds (acted σ.mode world) theory→
      interpret keys (context layout σ.mode) world (polynomialImages polynomials world) [] left ≤
        interpret keys (context layout σ.mode) world (polynomialImages polynomials world) [] right) :
    AlgebraSubtype p.assumptions (σ.ty left) (σ.ty right) := by
  have hbased:=(ComparisonStructuralQuerySoundness.build_based hbuild).2
  have hshapes : ∀v,ComparisonShape.Equivalent p.assumptions (.var v) (solved.fixedShapes v) :=
    fun v φ hφ=>(ComparisonShapeSolver.unify_factor (ComparisonShapeSolver.prepare_solved_iff.mp hs).1 hφ v).symm
  have hfixed : layout.shape.subst solved.fixedShapes=layout.shape := by
    simpa only [(ComparisonStructuralQuerySoundness.build_based hbuild).1] using hf
  have hmodel:=ComparisonShapeSolver.unify_sound (ComparisonShapeSolver.prepare_solved_iff.mp hs).1
  have hv:=hbased.valid hshapes
  apply (subtype_iff_boolean_observers (represented (hl.representable hv)) (represented (hr.representable hv))).mpr
  intro f
  have hn:=ComparisonStructuralTheory.declared_normalized hs hnorm hΔ
  obtain ⟨c,η,world,hw,ht⟩:=run_mapped_labels hμ hbased hshapes htests hlabels hsupport
    (fun _ _ hp=>hn.at_subtype hp) htheory f
  have hreads:=polynomialImages_reads (h:=hμ) (labels:=closed) (world:=world)
    hbased hshapes hmodel hfixed polynomials hp
  have he:=hall world hw
  rw [interpret_value hl hv ht hreads,interpret_value hr hv ht hreads] at he
  rw [←booleanValue_represented f _ (hl.representable hv),←booleanValue_represented f _ (hr.representable hv)]
  exact he

end ModalityInference.ComparisonLayoutModePullback
