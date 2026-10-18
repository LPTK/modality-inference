import ModalityInference.ComparisonSignedObservation
import ModalityInference.Proofs.ComparisonSignedEndpoints
import ModalityInference.Proofs.ComparisonStructuralLayout

/-! Public endpoint observations in an actual structural observer tree.
Each selected binder uses one positive polynomial at every occurrence, and all
annotation expressions use one shared modality substitution. -/

namespace ModalityInference.ComparisonSignedObservation
open ComparisonSignedEndpoints ComparisonStructuralLayout ComparisonControls ComparisonAlgebra

@[simp] theorem nodeAt_nil (layout : Layout) : nodeAt layout []=some layout := by cases layout <;> rfl

@[simp] theorem routeAtom_nil (i : Nat) : routeAtom [] i=i := rfl
@[simp] theorem routeAtom_cons (b : Bool) (route : Route) (i : Nat) :
    routeAtom (b::route) i=(if b then rightAtom else leftAtom) (routeAtom route i) := rfl

theorem routeAtom_append (left right : Route) (i : Nat) :
    routeAtom (left++right) i=routeAtom left (routeAtom right i) := by
  induction left with
  | nil => rfl
  | cons b rest ih => simp only [List.cons_append,routeAtom_cons,ih]

theorem action_select {c : Coordinate} {world : Nat → Bool}
    (h₁ : world (choiceAtom 1)=(coordinateBits c).1)
    (h₂ : world (choiceAtom 2)=(coordinateBits c).2) (m : ModExpr) (value : Bool) :
    (action m value).eval world=(c.modalWith modeAtom (.const value) m).eval world := by
  cases c <;> simp [action,BoolExpr.any,coordinateTest,BoolExpr.equal,BoolExpr.eval,h₁,h₂,coordinateBits]

theorem coordinate_clamp (c : Coordinate) (x : Bool) (m : Mode) :
    coordinateValue c x m =
      ((x || coordinateValue c false m) && coordinateValue c true m) := by
  cases c <;> cases x <;> simp [coordinateValue]

theorem action_observed {Δ shape basis f labels c η world}
    (hm : @ComparisonStructuralAlignment.Model Δ shape f labels c η)
    (ho : Observes basis f c η world) (m : GuardedMode Δ) (x : Bool) :
    (action m.expression x).eval world=coordinateValue c x (m.value η) := by
  rw [action_select ho.first ho.second]
  exact Coordinate.modalWith_eval ho.modes (hm.modeModel.elim Or.inl
    (fun hη => Or.inr (m.eval η hη)))

theorem modal_observed {Δ shape basis f labels c η world}
    (hm : @ComparisonStructuralAlignment.Model Δ shape f labels c η)
    (ho : Observes basis f c η world) {a : CompareTy} (ha : Representable Δ shape a)
    {m : ModExpr} (hlabel : ∃g∈labels,g.expression=m) :
    booleanValue f (.modal a m)=
      ((booleanValue f a || (action m false).eval world) && (action m true).eval world) := by
  obtain ⟨g,hg,rfl⟩ := hlabel
  rw [action_observed hm ho g false,action_observed hm ho g true,←coordinate_clamp]
  have h := hm.action (represented ha) g hg
  rw [booleanValue_represented f a ha]
  have ham : Representable Δ shape (.modal a g.expression) :=
    ⟨ha.1,CompareTy.definedUnder_modal_iff.mpr ⟨ha.2.1,g.defined⟩,ha.2.2⟩
  rw [booleanValue_represented f _ ham]
  exact h

def shifted (direction : Bool) (images : Call → Bool) (call : Call) : Bool :=
  images ⟨call.name,direction::call.route⟩

theorem interpret_child (keys : List Nat) (modes : ModVar → ModExpr)
    (kind : Constructor) (basis : Basis) (left right : Layout)
    (world : Nat → Bool) (images : Call → Bool) (direction : Bool)
    (route : Route) (a : Ty) :
    interpret keys (context (.fork kind basis left right) modes) world images (direction::route) a=
      interpret keys (context (if direction then right else left) modes)
        (world ∘ (if direction then rightAtom else leftAtom)) (shifted direction images) route a := by
  induction a generalizing route with
  | var v =>
    cases v <;> simp only [interpret,reference]
    · split
      · rfl
      · cases hn : nodeAt (if direction then right else left) route <;>
          simp [context,nodeAt,hn,Data.eval,routeAtom,Function.comp_def,BoolExpr.eval]
    · cases hn : nodeAt (if direction then right else left) route <;>
        simp [context,nodeAt,hn,Data.eval,routeAtom,Function.comp_def,BoolExpr.eval]
  | unit | credit =>
    cases hn : nodeAt (if direction then right else left) route <;>
      simp [interpret,context,nodeAt,hn,routeAtom,Function.comp_def,BoolExpr.eval]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [interpret,List.cons_append,iha,ihb]
    rfl
  | modal a m ih =>
    simp only [interpret,ih]
    simp only [context,rename_eval,Function.comp_def,routeAtom_cons]

def publicOp : Constructor → Ty → Ty → Ty
  | .prod => .prod | .sum => .sum | .fn => .fn

inductive Endpoint (Δ : Bounds) (labels : List (GuardedMode Δ)) (keys : List Nat)
    (σ : CompareSubstitution) : Layout → Ty → Prop
  | image {layout n} (selected : n∈keys)
      (represented : Representable Δ layout.shape (σ.type (.flex n))) :
      Endpoint Δ labels keys σ layout (.var (.flex n))
  | fixed {layout v} (unselected : ∀n∈keys,v≠.flex n) (fixed : σ.type v=.var v)
      (member : CompareTy.var v∈layout.basis.heads) :
      Endpoint Δ labels keys σ layout (.var v)
  | unit {layout} (member : CompareTy.unit∈layout.basis.heads) :
      Endpoint Δ labels keys σ layout .unit
  | credit {layout} (member : CompareTy.credit∈layout.basis.heads) :
      Endpoint Δ labels keys σ layout .credit
  | node {kind basis left right a b}
      (leftEndpoint : Endpoint Δ labels keys σ left a)
      (rightEndpoint : Endpoint Δ labels keys σ right b) :
      Endpoint Δ labels keys σ (.fork kind basis left right) (publicOp kind a b)
  | modal {layout a m} (inner : Endpoint Δ labels keys σ layout a)
      (label : ∃g∈labels,g.expression=m.subst σ.mode) :
      Endpoint Δ labels keys σ layout (.modal a m)

theorem Endpoint.representable {Δ labels keys σ layout a} (h : Endpoint Δ labels keys σ layout a)
    {modes} (hv : Valid Δ modes layout) : Representable Δ layout.shape (σ.ty a) := by
  induction h with
  | image _ h => exact h
  | fixed _ hf hh => simpa only [CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf] using hv.heads _ hh
  | unit hh => exact hv.heads _ hh
  | credit hh => exact hv.heads _ hh
  | @node k basis left right a b hl hr ihl ihr =>
    cases hv with
    | fork hh hm hvl hvr hc =>
      have h := k.kind.op_representable (ihl hvl) (ihr hvr)
      cases k <;> exact h
  | modal hi hm ih =>
    obtain ⟨g,hg,he⟩ := hm
    exact ⟨(ih hv).1,CompareTy.definedUnder_modal_iff.mpr
      ⟨(ih hv).2.1,he ▸ g.defined⟩,(ih hv).2.2⟩

def Reads {Δ : Bounds} (labels : List (GuardedMode Δ)) (keys : List Nat)
    (σ : CompareSubstitution) (layout : Layout) (world : Nat → Bool) (images : Call → Bool) : Prop :=
  ∀route node, nodeAt layout route=some node →
    ∀(f : LatticeHom (Order Δ node.shape) Bool) c η,
      Realized Δ labels node f c η (world ∘ routeAtom route) →
      ∀n∈keys, Representable Δ node.shape (σ.type (.flex n)) →
        images ⟨n,route⟩=booleanValue f (σ.type (.flex n))

theorem Reads.child {Δ labels keys σ kind basis left right world images}
    (h : @Reads Δ labels keys σ (.fork kind basis left right) world images) (direction : Bool) :
    Reads labels keys σ (if direction then right else left)
      (world ∘ (if direction then rightAtom else leftAtom)) (shifted direction images) := by
  intro route node hn f c η ht n hnkey hr
  apply h (direction::route) node hn f c η _ n hnkey hr
  simpa only [Function.comp_def,routeAtom_cons] using ht

theorem publicOp_subst (σ : CompareSubstitution) (k : Constructor) (a b : Ty) :
    σ.ty (publicOp k a b)=k.op (σ.ty a) (σ.ty b) := by cases k <;> rfl

theorem constructor_left {Δ s t} (k : Constructor)
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (g : LatticeHom (Order Δ s) Bool)
    (h : ∀a b,observer f (k.carrier a b)=ComparisonStructuralObservers.leftSign k.kind (observer g a))
    {a b : CompareTy} (ha : Representable Δ s a) (hb : Representable Δ t b) :
    booleanValue f (k.op a b)=ComparisonStructuralObservers.leftSign k.kind (booleanValue g a) := by
  have hp : Representable Δ (k.shape s t) (k.op a b) := by
    simpa only [Constructor.kind_shape,Constructor.kind_op] using k.kind.op_representable ha hb
  rw [booleanValue_represented f _ hp,booleanValue_represented g a ha]
  exact h (represented ha) (represented hb)

theorem constructor_right {Δ s t} (k : Constructor)
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (g : LatticeHom (Order Δ t) Bool)
    (h : ∀a b,observer f (k.carrier a b)=observer g b)
    {a b : CompareTy} (ha : Representable Δ s a) (hb : Representable Δ t b) :
    booleanValue f (k.op a b)=booleanValue g b := by
  have hp : Representable Δ (k.shape s t) (k.op a b) := by
    simpa only [Constructor.kind_shape,Constructor.kind_op] using k.kind.op_representable ha hb
  rw [booleanValue_represented f _ hp,booleanValue_represented g b hb]
  exact h (represented ha) (represented hb)

theorem node_interpret (keys : List Nat) (modes : ModVar → ModExpr)
    (kind : Constructor) (basis : Basis) (left right : Layout)
    (world : Nat → Bool) (images : Call → Bool) (a b : Ty) :
    interpret keys (context (.fork kind basis left right) modes) world images [] (publicOp kind a b)=
      if world (choiceAtom 0) then
        ComparisonStructuralObservers.leftSign kind.kind
          (interpret keys (context (.fork kind basis left right) modes) world images [false] a)
      else interpret keys (context (.fork kind basis left right) modes) world images [true] b := by
  cases kind <;> rfl

theorem Endpoint.interpret_value {Δ labels keys σ layout a}
    (he : Endpoint Δ labels keys σ layout a) {modes} (hv : Valid Δ modes layout)
    {f : LatticeHom (Order Δ layout.shape) Bool} {c η world images}
    (ht : Realized Δ labels layout f c η world) (hi : Reads labels keys σ layout world images) :
    interpret keys (context layout σ.mode) world images [] a=booleanValue f (σ.ty a) := by
  induction he generalizing c η world images with
  | @image layout n hn hr =>
    have hr := hi [] layout (nodeAt_nil layout) f c η ht n hn hr
    simpa only [interpret,reference,List.contains_iff_mem,hn,if_true,Data.eval,beq_true] using hr
  | @fixed layout v hn hf hh =>
    have ho := ht.observes.head_mem hh
    cases v with
    | flex n =>
      have hnot : ¬n∈keys := fun h => hn n h rfl
      simpa [interpret,reference,List.contains_iff_mem,hnot,Data.eval,context,nodeAt,
        routeAtom,BoolExpr.eval,CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf] using ho
    | rigid n =>
      simpa [interpret,reference,Data.eval,context,nodeAt,routeAtom,BoolExpr.eval,
        CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,hf] using ho
  | unit hh =>
    simpa only [interpret,context,nodeAt,routeAtom,BoolExpr.eval,CompareTy.ofTy] using ht.observes.head_mem hh
  | credit hh =>
    simpa only [interpret,context,nodeAt,routeAtom,BoolExpr.eval,CompareTy.ofTy] using ht.observes.head_mem hh
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

def polynomialImages (polynomials : Nat → CNF) (world : Nat → Bool) : Call → Bool :=
  shared (fun n values => ComparisonStructuralMatrix.cnfValue false values (polynomials n))
    (fun route i => world (routeAtom route (basisAtom i)))

theorem polynomialImages_reads {Δ labels keys σ layout world} (polynomials : Nat → CNF)
    (hp : ∀route node, nodeAt layout route=some node → ∀n∈keys,
      Representable Δ node.shape (σ.type (.flex n)) →
      ComparisonLatticeCompiler.compile node.basis (σ.type (.flex n))=some (polynomials n)) :
    @Reads Δ labels keys σ layout world (polynomialImages polynomials world) := by
  intro route node hn f c η ht n hk hr
  apply Bool.eq_iff_iff.mpr
  exact (ComparisonStructuralMatrix.cnfValue_correct _ _).trans
    (ComparisonStructuralNode.compiled_value (hp route node hn n hk hr)
      (booleanValue f) (booleanValue_join f) (booleanValue_meet f) ht.observes.types)

theorem compiled_observed {Δ labels keys σ layout left right modes}
    (hl : Endpoint Δ labels keys σ layout left) (hr : Endpoint Δ labels keys σ layout right)
    (hv : Valid Δ modes layout)
    {f : LatticeHom (Order Δ layout.shape) Bool} {c η world images}
    (ht : Realized Δ labels layout f c η world) (hi : Reads labels keys σ layout world images)
    {fuel output} (hc : compileGuards fuel (compile keys (context layout σ.mode) left right)=.success output) :
    (∀clause∈output,clause.Holds world images) ↔
      booleanValue f (σ.ty left) ≤ booleanValue f (σ.ty right) := by
  rw [compileGuards_correct hc,ComparisonSignedEndpoints.compile_correct,hl.interpret_value hv ht hi,
    hr.interpret_value hv ht hi,Bool.le_iff_imp]

theorem compiled_polynomials {Δ labels keys σ layout left right modes}
    (hl : Endpoint Δ labels keys σ layout left) (hr : Endpoint Δ labels keys σ layout right)
    (hv : Valid Δ modes layout)
    {f : LatticeHom (Order Δ layout.shape) Bool} {c η world}
    (ht : Realized Δ labels layout f c η world) (polynomials : Nat → CNF)
    (hp : ∀route node, nodeAt layout route=some node → ∀n∈keys,
      Representable Δ node.shape (σ.type (.flex n)) →
      ComparisonLatticeCompiler.compile node.basis (σ.type (.flex n))=some (polynomials n))
    {fuel output} (hc : compileGuards fuel (compile keys (context layout σ.mode) left right)=.success output) :
    (∀clause∈output,clause.Holds world (polynomialImages polynomials world)) ↔
      booleanValue f (σ.ty left) ≤ booleanValue f (σ.ty right) :=
  compiled_observed hl hr hv ht (polynomialImages_reads polynomials hp) hc

theorem nodeAt_based {names modes shapes layout}
    (hb : Based names modes shapes layout) {route node} (hn : nodeAt layout route=some node) :
    Based names modes shapes node := by
  induction route generalizing layout with
  | nil => simp only [nodeAt_nil,Option.some.injEq] at hn;subst node;exact hb
  | cons direction route ih =>
    cases hb with
    | leaf _ => simp [nodeAt] at hn
    | fork _ hl hr =>
      cases direction
      · exact ih hl hn
      · exact ih hr hn

theorem nodeAt_fixed {shapes : TypeVar → ComparisonShape} {layout : Layout}
    (hf : layout.shape.subst shapes=layout.shape) {route node}
    (hn : nodeAt layout route=some node) : node.shape.subst shapes=node.shape := by
  induction route generalizing layout with
  | nil => simp only [nodeAt_nil,Option.some.injEq] at hn;subst node;exact hf
  | cons direction route ih =>
    cases layout with
    | leaf _ _ => simp [nodeAt] at hn
    | fork kind basis left right =>
      have hh : left.shape.subst shapes=left.shape ∧ right.shape.subst shapes=right.shape := by
        cases kind <;> simpa only [Layout.shape,Constructor.shape,ComparisonShape.subst,
          ComparisonShape.prod.injEq,ComparisonShape.sum.injEq,ComparisonShape.fn.injEq] using hf
      cases direction
      · exact ih hh.1 hn
      · exact ih hh.2 hn

theorem polynomialImages_reads_of_bases {Δ labels keys σ layout world names modes shapes}
    (hb : Based names modes shapes layout) (hmodel : ComparisonShape.Models Δ shapes)
    (hf : layout.shape.subst shapes=layout.shape) (polynomials : Nat → CNF)
    (hp : ∀n∈keys, ∃basis,
      ComparisonStructuralBasis.basis names modes shapes ((σ.type (.flex n)).shape.subst shapes)=some basis ∧
      ComparisonLatticeCompiler.compile basis (σ.type (.flex n))=some (polynomials n)) :
    @Reads Δ labels keys σ layout world (polynomialImages polynomials world) := by
  apply polynomialImages_reads polynomials
  intro route node hn n hk hr
  obtain ⟨basis,hbasis,hcompile⟩ := hp n hk
  have he : (σ.type (.flex n)).shape.subst shapes=node.shape :=
    (hr.2.2 shapes hmodel).trans (nodeAt_fixed hf hn)
  rw [he] at hbasis
  have hbnode := (nodeAt_based hb hn).basis
  have hbe : basis=node.basis := Option.some.inj (hbasis.symm.trans hbnode)
  exact hbe ▸ hcompile

theorem compiled_basis_family {Δ labels keys σ layout left right names modes shapes}
    (hl : Endpoint Δ labels keys σ layout left) (hr : Endpoint Δ labels keys σ layout right)
    (hb : Based names modes shapes layout) (hmodel : ComparisonShape.Models Δ shapes)
    (hs : ∀v,ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (hf : layout.shape.subst shapes=layout.shape)
    {f : LatticeHom (Order Δ layout.shape) Bool} {c η world}
    (ht : Realized Δ labels layout f c η world) (polynomials : Nat → CNF)
    (hp : ∀n∈keys, ∃basis,
      ComparisonStructuralBasis.basis names modes shapes ((σ.type (.flex n)).shape.subst shapes)=some basis ∧
      ComparisonLatticeCompiler.compile basis (σ.type (.flex n))=some (polynomials n))
    {fuel output} (hc : compileGuards fuel (compile keys (context layout σ.mode) left right)=.success output) :
    (∀clause∈output,clause.Holds world (polynomialImages polynomials world)) ↔
      booleanValue f (σ.ty left) ≤ booleanValue f (σ.ty right) :=
  compiled_observed hl hr (hb.valid hs) ht (polynomialImages_reads_of_bases hb hmodel hf polynomials hp) hc

end ModalityInference.ComparisonSignedObservation
