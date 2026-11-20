import ModalityInference.Proofs.ComparisonWindowWitness
import ModalityInference.ComparisonObserverBoundary

/-! A fixed admissible public comparison with recursive declared bounds has no
order-preserving choice of completions at any finite observation radius. The
view records the full canonical header and the written subterms at each node. -/
namespace ModalityInference.ComparisonWindowSections
open ComparisonObserverMachine ComparisonObserverMachineCheck ComparisonStructuralLayout
  ComparisonWindowObservers ComparisonObserverBoundary

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

def T : Ty := .var (.rigid 0)
def F : Ty := .var (.rigid 1)
def B (j : Nat) : Ty := .var (.rigid (2+j))
def C (j : Nat) : Ty := .var (.rigid (7+j))
def X (j : Nat) : Ty := .var (.flex j)
def P (a : Ty) : Ty := .prod a a
def equal (a b : Ty) : Bounds := [.sub a b, .sub b a]
def target : Scheme := {body := .unit, bounds :=
  [.sub T (.prod T (B 0)), .sub (.prod (C 0) F) F] ++ equal T (P T) ++ equal F (P F) ++
  ([0,1,2,3] : List Nat).flatMap (fun j => equal (B (j+1)) (P (B j)) ++ equal (C (j+1)) (P (C j)))}
def source : Scheme := {body := .unit, typeParams := [0,1,2,3], bounds := (
  equal (X 0) (P (X 1)) ++ equal (X 1) (P (X 2)) ++ equal (X 2) (P (X 3)) ++
  equal (X 3) (.prod T F))}
def Δ := target.bounds.assumptions
def names : List TypeVar := (List.range 12).map TypeVar.rigid
abbrev O := Observer Δ names []
abbrev N := observerNodes Δ names []
def atTy (a : Ty) (x : O) := value N (.ofTy a) x
def child (x : O) := ((N x).branch .prod).next
def test : Ty := P (P (P (.prod T F)))

private theorem atP (a : Ty) (x : O) : atTy (P a) x = atTy a (child x) := by
  simp [P,atTy,child,CompareTy.ofTy,value]
private theorem declared {a b : Ty} (h : Constraint.sub a b ∈ Δ) (x : O) : atTy a x ≤ atTy b x :=
  (certified Δ names []).bounds x a b h
private theorem eqstep {a b : Ty} (hf : Constraint.sub a (P b) ∈ Δ)
    (hr : Constraint.sub (P b) a ∈ Δ) (x : O) : atTy a x = atTy b (child x) :=
  (le_antisymm (declared hf x) (declared hr x)).trans (atP b x)
private theorem stayT (x : O) : atTy T x = atTy T (child x) := eqstep (a := T) (b := T) (by decide) (by decide) x
private theorem stayF (x : O) : atTy F x = atTy F (child x) := eqstep (a := F) (b := F) (by decide) (by decide) x
private theorem trail (G : Nat → Ty)
    (h : ∀ j : Fin 4, Constraint.sub (G (j.val+1)) (P (G j.val)) ∈ Δ ∧
      Constraint.sub (P (G j.val)) (G (j.val+1)) ∈ Δ) (x : O) :
    atTy (G 4) x = atTy (G 0) (child (child (child (child x)))) :=
  (eqstep (h 3).1 (h 3).2 x).trans ((eqstep (h 2).1 (h 2).2 _).trans
    ((eqstep (h 1).1 (h 1).2 _).trans (eqstep (h 0).1 (h 0).2 _)))

private theorem forced (x : O) (ht : atTy T x = true) (hf : atTy F x = false) :
    (atTy (B 4) x = false → atTy test x = true) ∧
    (atTy (C 4) x = true → atTy test x = false) := by
  let z := child (child (child x))
  have t3 : atTy T z = true := by simp only [z, ←stayT, ht]
  have f3 : atTy F z = false := by simp only [z, ←stayF, hf]
  have t4 := (stayT z).symm.trans t3
  have f4 := (stayF z).symm.trans f3
  have l := declared (a := T) (b := .prod T (B 0)) (by decide) z
  have r := declared (a := .prod (C 0) F) (b := F) (by decide) z
  let left := ((N z).branch .prod).left
  change atTy T z ≤ (if left then atTy T (child z) else atTy (B 0) (child z)) at l
  change (if left then atTy (C 0) (child z) else atTy F (child z)) ≤ atTy F z at r
  simp only [test, atP]
  change (atTy (B 4) x = false → (if left then atTy T (child z) else atTy F (child z)) = true) ∧ _
  have b4 : atTy (B 4) x = atTy (B 0) (child z) := trail B (by decide) x
  have c4 : atTy (C 4) x = atTy (C 0) (child z) := trail C (by decide) x
  change _ ∧ (atTy (C 4) x = true → (if left then atTy T (child z) else atTy F (child z)) = false)
  cases e : left <;> simp_all
  · exact Bool.eq_true_of_true_le l
  · exact le_antisymm r (Bool.false_le _)

private def next (i : Fin 9) : Fin 9 := ⟨min (i.val+1) 8, by omega⟩
private def atom (q : Fin 4) (i : Fin 9) (v : Nat) : Bool :=
  if v = 0 then true else if v = 1 then false else if v < 7 then
    !decide (q.val = 0 ∧ i.val + (v-2) = 7)
  else decide (q.val = 3 ∧ i.val + (v-7) = 7)
private def data (q : Fin 4) (i : Fin 9) : Description (Fin 9) where
  atoms := (List.range 12).map (atom q i)
  modes := []
  coordinate := .unaffected
  unitValue := false
  creditValue := false
  range _ := true
  branch k := ⟨decide (k = .prod ∧ i.val = 6 ∧ q.val < 2), next i⟩
private theorem ok : ∀ q : Fin 4, check Δ names [] (data q) = true := by decide
private def o (q : Fin 4) (i : Fin 9 := 3) : O := embed (ok q) i
private theorem at_o (a : Ty) (q : Fin 4) (i : Fin 9) : atTy a (o q i) =
    value (ComparisonObserverMachineCheck.nodes names [] (data q)) (.ofTy a) i := embed_value ..

def head (x : O) := (observerTrees Δ names []).root x

def ports := boundary Δ (declaredTypes source.bounds ++ [.unit])
def reads (ts : List CompareTy) (x : O) := ts.map fun a => value N a x

def header (x : O) := (head x, reads ports x)

private theorem same_desc (i : Fin 9) (h : i.val < 6) : data 1 i = data 2 i := by
  have ne : i.val ≠ 6 := by omega
  simp [data, atom, ne]

private theorem captured (n : Nat) (i : Fin 9) (h : i.val + n ≤ 6) :
    ComparisonDefiniteTreeMachines.Window.capture n (unroll names [] (data 1) i) =
    ComparisonDefiniteTreeMachines.Window.capture n (unroll names [] (data 2) i) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext (congrArg (encode names []) (same_desc i (by omega)))
    funext k
    apply ih (next i)
    change min (i.val+1) 8 + n ≤ 6
    omega

private theorem same_head : head (o 1) = head (o 2) := by
  dsimp only [head, o, embed, observerTrees, closedTrees]
  change ComparisonDefiniteTreeMachines.Window.capture 3 (unroll names [] (data 1) 3) =
    ComparisonDefiniteTreeMachines.Window.capture 3 (unroll names [] (data 2) 3)
  exact captured 3 3 (by decide)

private theorem ports_machine (q : Fin 4) (i : Fin 9) : reads ports (o q i) =
    ports.map (fun a => value (ComparisonObserverMachineCheck.nodes names [] (data q)) a i) := by
  unfold reads
  exact List.map_congr_left (fun _ _ => embed_value ..)

private theorem same_header : header (o 1) = header (o 2) := by
  apply Prod.ext same_head
  rw [show (header (o 1)).2 = reads ports (o 1) from rfl,
    show (header (o 2)).2 = reads ports (o 2) from rfl, ports_machine, ports_machine]
  decide

private theorem atomorder {q r : Fin 4} (hr : q=0 ∧ r=1 ∨ q=2 ∧ r=3) (i : Fin 9) (v : TypeVar) :
    atomValue names (data q i) v ≤ atomValue names (data r i) v := by
  by_cases hv : v ∈ names
  · obtain ⟨k,hk,rfl⟩ := (List.mem_map.mp hv)
    have h : k < 12 := List.mem_range.mp hk
    have all : ∀ i : Fin 9, ∀ k : Fin 12, ∀ q r : Fin 4, (q=0 ∧ r=1 ∨ q=2 ∧ r=3) →
        atomValue names (data q i) (.rigid k) ≤ atomValue names (data r i) (.rigid k) := by decide
    exact all i ⟨k,h⟩ q r hr
  · simp [atomValue, data, hv]

private theorem all_order {q r : Fin 4} (hr : q=0 ∧ r=1 ∨ q=2 ∧ r=3) (a : CompareTy)
    (i : Fin 9) : value N a (o q i) ≤ value N a (o r i) := by
  simp only [o, embed_value]
  induction a generalizing i with
  | var v => exact atomorder hr i v
  | unit | credit => exact le_rfl
  | prod a b ha hb =>
    have same : (data q i).branch .prod = (data r i).branch .prod := by
      rcases hr with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [data]
    simp only [value, ComparisonObserverMachineCheck.nodes, same]
    split <;> first | exact ha _ | exact hb _
  | sum a b ha hb | fn a b ha hb => exact hb _
  | modal a m ha => exact ha _
  | join a b ha hb => exact sup_le_sup (ha i) (hb i)
  | meet a b ha hb => exact inf_le_inf (ha i) (hb i)

private theorem header_port {x y : O} (h : header x = header y) (a : Ty)
    (ha : CompareTy.ofTy a ∈ ports) : atTy a x = atTy a y := by
  have e : reads ports x = reads ports y := congrArg Prod.snd h
  exact (List.map_eq_map_iff.mp e) _ ha

abbrev Allowed := ComparisonWindowTerms.Allowed Δ names []
def Ordered (x y : O) := ∀ a, Allowed a → value N a x ≤ value N a y

def a3 : Ty := .prod T F
def a2 : Ty := P a3
def a1 : Ty := P a2
def a0 : Ty := P a1
def action : Substitution := {types := [(0,a0), (1,a1), (2,a2), (3,a3)]}
private theorem defined_action : CompareInstantiatesUnder Δ source (.ofSubstitution action) := by
  refine ⟨⟨List.Perm.refl _,List.Perm.refl _⟩,?_,?_⟩
  · apply CompareSubstitution.wellFormedUnder_of_images <;>
      simp [CompareSubstitution.ofSubstitution, action, a0, a1, a2, a3, P,T,F,
        CompareTy.ofTy, CompareTy.DefinedUnder,CompareTy.wellFormedBounds,ModeModels]
  · simp [source,CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,
      CompareTy.DefinedUnder,CompareTy.wellFormedBounds,ModeModels]

private theorem good_bounds : EntailsAll Δ (action.bounds source.bounds) := by
  change EntailsAll Δ [.sub a0 a0, .sub a0 a0, .sub a1 a1, .sub a1 a1,
    .sub a2 a2, .sub a2 a2, .sub a3 a3, .sub a3 a3]
  simp [EntailsAll, Entails, a0, a1, a2, a3, P, T, F, Subtype.refl,
    TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]

theorem admissible : AlgebraSubsumesUnder [] source target := by
  refine ⟨.ofSubstitution action, defined_action.domain, CompareSubstitution.wellShaped_ofSubstitution _ _,
    defined_action.images, defined_action.body, ?_, ?_⟩
  · simpa only [CompareSubstitution.ofSubstitution_bounds] using good_bounds.to_shaped.to_algebra
  · exact .shaped (.refl (CompareTy.wellShaped_ofTy .unit _))

theorem no_finite_shape : ¬∃ ρ, ComparisonShape.Models Δ ρ := by
  rintro ⟨ρ,hρ⟩
  have e := hρ (.var (.rigid 0),.prod (.var (.rigid 0)) (.var (.rigid 0))) (by decide)
  have size := congrArg sizeOf e
  simp only [ComparisonShape.subst,ComparisonShape.prod.sizeOf_spec] at size
  omega

/-- Every admissible solution has the same value on the leading image as the
explicit positive solution. All four equalities are actual source constraints. -/
theorem leading_image (σ : CompareSubstitution)
    (h : AlgebraEntailsAll Δ (σ.bounds source.bounds)) (t : O) :
    value N (σ.type (.flex 0)) t = atTy test t := by
  have rel {a b : CompareTy} (ab : AlgebraEntails Δ (.sub a b)) (i : O) :
      value N a i ≤ value N b i := subtype_mono (certified Δ names []).modal
    (certified Δ names []).range (certified Δ names []).coherent (certified Δ names []).bounds
    (Bounds.assumptions_typeBoundsDefined _) ab.2.1 ab.2.2 ab.1 i
  let eqv (a b : CompareTy) (ab : AlgebraEntails Δ (.sub a b))
      (ba : AlgebraEntails Δ (.sub b a)) (i : O) := le_antisymm (rel ab i) (rel ba i)
  change AlgebraEntailsAll Δ [_,_,_,_,_,_,_,_] at h
  have eqs (a b : Ty) (i : O)
      (ab : Constraint.sub a b ∈ source.bounds) (ba : Constraint.sub b a ∈ source.bounds) :
      value N (σ.ty a) i = value N (σ.ty b) i :=
    eqv _ _ (h _ (List.mem_map.mpr ⟨_,ab,rfl⟩)) (h _ (List.mem_map.mpr ⟨_,ba,rfl⟩)) i
  have s0 := eqs (X 0) (P (X 1)) t (by decide) (by decide)
  have s1 := eqs (X 1) (P (X 2)) (child t) (by decide) (by decide)
  have s2 := eqs (X 2) (P (X 3)) (child (child t)) (by decide) (by decide)
  have s3 := eqs (X 3) (.prod T F) (child (child (child t))) (by decide) (by decide)
  simp only [X,P,CompareSubstitution.ty,CompareTy.ofTy,CompareTy.subst,value,ite_self] at s0 s1 s2 s3
  simp only [test, atP]
  exact s0.trans (s1.trans (s2.trans s3))

open ComparisonWindowEndpoints ComparisonDefiniteTreeMachines ComparisonRankedBasis

abbrev kid (x : O) (k : Constructor) := (observerTrees Δ names []).child x k

def View : Nat → O → O → Prop
  | 0,x,y => header x = header y
  | n+1,x,y => header x = header y ∧ ∀ k, View n (kid x k) (kid y k)

private theorem read_raw (a : CompareTy) (x : O) :
    value N a x = value ((fields names []).nodes rawTrees) a x.val := by
  induction a generalizing x with
  | var | unit | credit => rfl
  | prod a b ha hb | sum a b ha hb | fn a b ha hb =>
    simp only [value, ha, hb]
    rfl
  | _ => simp_all [value,Fields.nodes,readFields,closedTrees,rawTrees,Window.capture,
      observerFields,observerTrees]

private theorem cap_raw {A I} (n : Nat) {x y : List I → A} :
    Window.capture (n+1) x = Window.capture (n+1) y → rawTrees.Prefix n x y := by
  induction n generalizing x y with
  | zero => exact congrArg Prod.fst
  | succ n ih => exact fun h => ⟨congrArg Prod.fst h,fun i => ih (congrFun (congrArg Prod.snd h) i)⟩

private theorem header_eq {x y : O} (h : head x = head y) : header x = header y := by
  apply Prod.ext h
  change reads ports x = reads ports y
  unfold reads
  apply List.map_congr_left
  intro a ha
  have bound : ports.all (fun t => decide (rank t ≤ 2)) = true := by decide
  have r := of_decide_eq_true (List.all_eq_true.mp bound a ha)
  rw [read_raw,read_raw]
  exact (value_reads rawTrees (fields names []) a).mono _ r x.val y.val (cap_raw 2 h)

private theorem kid_o (q : Fin 4) (i : Fin 9) (k : Constructor) : kid (o q i) k = o q (next i) :=
  Subtype.ext rfl

private def anchor : O := o 2 8
private theorem kid_anchor (k : Constructor) : kid anchor k = anchor := kid_o 2 8 k
private abbrev Stable := {u : O // head u = head anchor}
private theorem paste_stable (x : Stable) : ∃ u : O, head u = head anchor ∧ ∀k, kid u k = x.val := by
  obtain ⟨u,hu,hc⟩ := (observerTrees Δ names []).paste anchor (fun _ => x.val)
    (fun k => by simpa only [kid_anchor] using x.property)
  exact ⟨u,hu,fun k => congrFun hc k⟩
private noncomputable def wrap (x : Stable) : Stable :=
  ⟨(paste_stable x).choose,(paste_stable x).choose_spec.1⟩
private theorem kid_wrap (x : Stable) (k : Constructor) : kid (wrap x).val k = x.val :=
  (paste_stable x).choose_spec.2 k

private theorem primitive {x : O} (h : head x = head anchor) : x.val [] = anchor.val [] :=
  congrArg Prod.fst h

private theorem lifted_order {x y w z : O} (hw : w.val [] = anchor.val [])
    (hz : z.val [] = anchor.val []) (hc : ∀ k, kid w k = x) (hd : ∀ k, kid z k = y)
    (h : ∀ a, value N a x ≤ value N a y) (a : CompareTy) : value N a w ≤ value N a z := by
  have rootAtom : (N w).atom = (N z).atom := congrArg (fields names []).atom (hw.trans hz.symm)
  have rootUnit : (N w).unitValue = (N z).unitValue := congrArg (fields names []).unit (hw.trans hz.symm)
  have rootCredit : (N w).creditValue = (N z).creditValue := congrArg (fields names []).credit (hw.trans hz.symm)
  have right {u : O} (hu : u.val [] = anchor.val []) (k : Constructor) : ((N u).branch k).left = false := by
    change (fields names []).left (u.val []) k = false
    rw [hu]
    cases k <;> rfl
  have hal {u : O} (hu : u.val [] = anchor.val []) (m : ModExpr) (b : Bool) :
      (N u).action m b = b := by
    change (fields names []).action (u.val []) m b = b
    rw [hu]
    rfl
  induction a with
  | var v => exact le_of_eq (congrFun rootAtom v)
  | unit => exact le_of_eq rootUnit
  | credit => exact le_of_eq rootCredit
  | prod a b h₁ h₂ | sum a b h₁ h₂ | fn a b h₁ h₂ =>
    simp only [value, right hw, right hz, Bool.false_eq_true, if_false]
    change value N b (kid w _) ≤ value N b (kid z _)
    simpa only [hc,hd] using h b
  | modal a m ih => simpa only [value,hal hw,hal hz] using ih
  | join a b hp hq => exact sup_le_sup hp hq
  | meet a b hp hq => exact inf_le_inf hp hq

private structure Obstruction (n : Nat) (samples : Fin 4 → O) where
  middle : View n (samples 1) (samples 2)
  orderLo : ∀ a, value N a (samples 0) ≤ value N a (samples 1)
  orderHi : ∀ a, value N a (samples 2) ≤ value N a (samples 3)
  expr : CompareTy
  allowed : Allowed expr
  low : ∀ u, View n u (samples 0) → value N expr u = true
  high : ∀ u, View n u (samples 3) → value N expr u = false

private def initial : Obstruction 0 (fun q => o q 3) where
  middle := same_header
  orderLo a := all_order (q := 0) (r := 1) (by decide) a 3
  orderHi a := all_order (q := 2) (r := 3) (by decide) a 3
  expr := .ofTy test
  allowed := by
    constructor
    · simp [test,P,T,F,CompareTy.ofTy,CompareTy.DefinedUnder,CompareTy.wellFormedBounds,ModeModels]
    · simp [test,P,T,F,CompareTy.ofTy,ComparisonInterpolation.Supports,names]
  low u hu := (forced u
    ((header_port hu T (by decide)).trans ((at_o T 0 3).trans (by decide)))
    ((header_port hu F (by decide)).trans ((at_o F 0 3).trans (by decide)))).1
    ((header_port hu (B 4) (by decide)).trans ((at_o (B 4) 0 3).trans (by decide)))
  high u hu := (forced u
    ((header_port hu T (by decide)).trans ((at_o T 3 3).trans (by decide)))
    ((header_port hu F (by decide)).trans ((at_o F 3 3).trans (by decide)))).2
    ((header_port hu (C 4) (by decide)).trans ((at_o (C 4) 3 3).trans (by decide)))

private def ascend {n : Nat} {sample nextSample : Fin 4 → O} (old : Obstruction n sample)
    (root : ∀ q, (nextSample q).val [] = anchor.val [])
    (middle : header (nextSample 1) = header (nextSample 2))
    (children : ∀ q k, kid (nextSample q) k = sample q) : Obstruction (n+1) nextSample where
  middle := ⟨middle, fun k => by rw [children,children]; exact old.middle⟩
  orderLo := lifted_order (root 0) (root 1) (children 0) (children 1) old.orderLo
  orderHi := lifted_order (root 2) (root 3) (children 2) (children 3) old.orderHi
  expr := .prod old.expr old.expr
  allowed := ⟨CompareTy.definedUnder_prod_iff.mpr ⟨old.allowed.1,old.allowed.1⟩,
    old.allowed.2,old.allowed.2⟩
  low u hu := by
    have h := hu.2 Constructor.prod
    rw [children] at h
    simpa only [value,ite_self] using old.low (kid u .prod) h
  high u hu := by
    have h := hu.2 Constructor.prod
    rw [children] at h
    simpa only [value,ite_self] using old.high (kid u .prod) h

private instance : Fintype Constructor := ⟨{.prod,.sum,.fn}, by intro k; cases k <;> simp⟩

private theorem early : ∀ (q : Fin 4) (i : Fin 9), i.val < 3 →
    (o q i).val [] = anchor.val [] := by
  change ∀ q : Fin 4, ∀ i : Fin 9, i.val < 3 →
    encode names [] (data q i) = encode names [] (data 2 8)
  intro q i hi
  have e : ∀ (q : Fin 4) (i : Fin 9), i.val < 3 → (data q i).atoms = (data 2 8).atoms := by decide
  have hleft : ∀(q : Fin 4) (i : Fin 9), i.val < 3 → ∀ k,
      ((data q i).branch k).left = ((data 2 8).branch k).left := by decide
  have first : (fun v : ↥names.toFinset => atomValue names (data q i) v.val) =
      (fun v : ↥names.toFinset => atomValue names (data 2 8) v.val) := by
    funext v
    simp only [atomValue, e q i hi]
    rfl
  unfold encode
  rw [first, funext (hleft q i hi)]
  rfl

private def increase {n : Nat} (i : Fin 9) (h : i.val < 3)
    (old : Obstruction n (fun q => o q (next i))) : Obstruction (n+1) (fun q => o q i) :=
  ascend old (fun q => early q i h) (header_eq (captured 3 i (by omega)))
    (fun q k => kid_o q i k)

private theorem cap_early (q : Fin 4) (i : Fin 9) (n : Nat) (h : i.val + n ≤ 3) :
    Window.capture n (unroll names [] (data q) i) = Window.capture n anchor.val := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    apply Prod.ext (early q i (by omega))
    funext k
    change Window.capture n (unroll names [] (data q) (next i)) = Window.capture n anchor.val
    apply ih (next i)
    change min (i.val+1) 8 + n ≤ 3
    omega

private noncomputable def padding : Nat → Fin 4 → Stable
  | 0,q => ⟨o q 0,cap_early q 0 3 (by decide)⟩
  | n+1,q => wrap (padding n q)

private noncomputable def long_obstruction (n : Nat) :
    Obstruction (n+3) (fun q => (padding n q).val) := by
  induction n with
  | zero => exact increase 0 (by decide) (increase 1 (by decide) (increase 2 (by decide) initial))
  | succ k ih =>
    exact ascend ih (fun q => primitive (wrap (padding k q)).property)
      (header_eq ((wrap (padding k 1)).property.trans (wrap (padding k 2)).property.symm))
      (fun q i => kid_wrap (padding k q) i)

private theorem Obstruction.excludes {n s} (bad : Obstruction n s) :
    ¬∃ f : O → O, (∀ x, View n (f x) x) ∧
      (∀ x y, View n x y → f x = f y) ∧ (∀ x y, Ordered x y → Ordered (f x) (f y)) := by
  rintro ⟨f,keep,loc,mono⟩
  have lo := bad.low _ (keep (s 0))
  have hi := bad.high _ (keep (s 3))
  have e := mono _ _ (fun a _ => bad.orderLo a) _ bad.allowed
  have g := mono _ _ (fun a _ => bad.orderHi a) _ bad.allowed
  rw [loc _ _ bad.middle] at e
  exact (by decide : ¬true ≤ false) (lo ▸ hi ▸ e.trans g)

/-- One fixed admissible input has no order-preserving section of the enriched
window projection at any radius. Every input subterm occurrence is retained
at every node of the prefix, in addition to the canonical observer header. -/
theorem no_section_at_any_depth (n : Nat) :
    ¬∃ f : O → O, (∀ x, View n (f x) x) ∧
      (∀ x y, View n x y → f x = f y) ∧ (∀ x y, Ordered x y → Ordered (f x) (f y)) := by
  match n with
  | 0 => exact initial.excludes
  | 1 => exact (increase 2 (by decide) initial).excludes
  | 2 => exact (increase 1 (by decide) (increase 2 (by decide) initial)).excludes
  | k+3 => exact (long_obstruction k).excludes

end ModalityInference.ComparisonWindowSections
