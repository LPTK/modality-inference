import ModalityInference.Proofs.ComparisonObserverCompactness
import ModalityInference.Proofs.ComparisonSignedGraph
import Mathlib.Data.Fintype.Prod

/-! An exact finite-term criterion for shared signed observer constraints.
Finite quotients include order and constant-boundary edges. The chain relation
intersects reachability in every such quotient; its consistency is equivalent
to one shared family of finite lattice expressions. This characterization does
not supply an effective bound or a decision procedure for chain reachability. -/
namespace ModalityInference.ComparisonObserverChains

open ComparisonSignedGraph

abbrev Point (I L : Type*) [Lattice L] := Bool × I × LatticeHom L Bool

def complement {I L} [Lattice L] (a : Point I L) : Point I L := (!a.1,a.2)

def observe {I L} [Lattice L] (p : Finset L) (a : Point I L) :
    Bool × I × (p → Bool) := (a.1,a.2.1,fun x => a.2.2 x.val)

structure System (I L : Type*) [Lattice L] where
  edge : Finset L → Point I L → Point I L → Prop
  contrapose : ∀p {a b},edge p a b → edge p (complement b) (complement a)
  restrict : ∀{p q},p ⊆ q → ∀{a b},edge q a b → edge p a b

def System.graph {I L} [Lattice L] (s : System I L) (p : Finset L) : Graph (Point I L) where
  complement := complement
  involutive := by intro a; cases a; simp [complement]
  edge := s.edge p
  contrapose := s.contrapose p

def System.quotient {I L} [Lattice L] (s : System I L) (p : Finset L) :
    Graph (Bool × I × (p → Bool)) where
  complement a := (!a.1,a.2)
  involutive := by intro a; cases a; simp
  edge a b := ∃x y,observe p x = a ∧ observe p y = b ∧ s.edge p x y
  contrapose := by
    rintro _ _ ⟨x,y,rfl,rfl,hxy⟩
    exact ⟨complement y,complement x,rfl,rfl,s.contrapose p hxy⟩

theorem System.reaches_origin {I L} [Lattice L] (s : System I L)
    {p a b} (h : (s.quotient p).Reaches a b) :
    a = b ∨ ∃x,observe p x = a := by
  induction h with
  | refl => exact .inl rfl
  | tail _ h ih =>
    rcases ih with rfl | ih
    · obtain ⟨x,y,hx,hy,hxy⟩ := h
      exact .inr ⟨x,hx⟩
    · exact .inr ih

theorem System.reaches_restrict {I L} [Lattice L] (s : System I L)
    {p q : Finset L} (hpq : p ⊆ q) {a b : Point I L}
    (h : (s.quotient q).Reaches (observe q a) (observe q b)) :
    (s.quotient p).Reaches (observe p a) (observe p b) := by
  let restrict : (Bool × I × (q → Bool)) → (Bool × I × (p → Bool)) :=
    fun x => (x.1,x.2.1,fun y => x.2.2 ⟨y.val,hpq y.property⟩)
  have hm : ∀{x y},(s.quotient q).edge x y →
      (s.quotient p).edge (restrict x) (restrict y) := by
    rintro _ _ ⟨x,y,rfl,rfl,hxy⟩
    exact ⟨x,y,rfl,rfl,s.restrict hpq hxy⟩
  exact Relation.ReflTransGen.lift restrict (fun _ _ hxy => hm hxy) h

def System.Bad {I L} [Lattice L] (s : System I L) (p : Finset L)
    (i : I) (f : LatticeHom L Bool) : Prop :=
  (s.quotient p).Reaches (observe p (false,i,f)) (observe p (true,i,f)) ∧
  (s.quotient p).Reaches (observe p (true,i,f)) (observe p (false,i,f))

theorem System.consistent_iff {I L} [Lattice L] (s : System I L) (p : Finset L) :
    (s.quotient p).Consistent ↔ ∀i f,¬s.Bad p i f := by
  constructor
  · intro h i f hb
    exact h (observe p (false,i,f)) hb
  · intro h a hab
    rcases s.reaches_origin hab.1 with he | ⟨⟨b,i,f⟩,rfl⟩
    · have hs := congrArg Prod.fst he
      change a.1 = !a.1 at hs
      cases hv : a.1 <;> simp [hv] at hs
    · cases b with
      | false => exact h i f hab
      | true => exact h i f ⟨hab.2,hab.1⟩

def System.Chain {I L} [Lattice L] (s : System I L) (a b : Point I L) : Prop :=
  ∀p,(s.quotient p).Reaches (observe p a) (observe p b)

def System.ChainConsistent {I L} [Lattice L] (s : System I L) : Prop :=
  ∀i f,¬(s.Chain (false,i,f) (true,i,f) ∧ s.Chain (true,i,f) (false,i,f))

theorem System.finite_consistent_iff {I L} [Fintype I] [Lattice L]
    (s : System I L) :
    (∃p,(s.quotient p).Consistent) ↔ s.ChainConsistent := by
  classical
  constructor
  · rintro ⟨p,hp⟩ i f ⟨ha,hb⟩
    exact (s.consistent_iff p).mp hp i f ⟨ha p,hb p⟩
  · intro h
    by_contra hn
    have hi (p : Finset L) : ∃i f,s.Bad p i f := by
      have hp : ¬(s.quotient p).Consistent := fun hp => hn ⟨p,hp⟩
      rw [s.consistent_iff] at hp
      push_neg at hp
      exact hp
    obtain ⟨i,f,hf⟩ := ComparisonObserverCompactness.compact s.Bad
      (by
        intro p i f g hfg
        have he : (fun x : p => f x.val) = fun x : p => g x.val :=
          funext (fun x => hfg x.val x.property)
        simp only [System.Bad,observe,he])
      (by
        intro p q hpq i f hbad
        exact ⟨s.reaches_restrict hpq hbad.1,s.reaches_restrict hpq hbad.2⟩) hi
    exact h i f ⟨fun p => (hf p).1,fun p => (hf p).2⟩

def constant {L : Type*} [Lattice L] (b : Bool) : LatticeHom L Bool where
  toFun _ := b
  map_sup' _ _ := by cases b <;> rfl
  map_inf' _ _ := by cases b <;> rfl

structure Constraints (I L : Type*) [Lattice L] where
  edge : Point I L → Point I L → Prop
  contrapose : ∀{a b},edge a b → edge (complement b) (complement a)

inductive Constraints.Edge {I L} [Lattice L] (r : Constraints I L) (p : Finset L) :
    Point I L → Point I L → Prop
  | original {a b} : r.edge a b → r.Edge p a b
  | positive (i : I) (f g : LatticeHom L Bool) :
      (∀a ∈ p,f a ≤ g a) → r.Edge p (true,i,f) (true,i,g)
  | negative (i : I) (f g : LatticeHom L Bool) :
      (∀a ∈ p,g a ≤ f a) → r.Edge p (false,i,f) (false,i,g)
  | boundary (i : I) (b : Bool) :
      r.Edge p (!b,i,constant b) (b,i,constant b)

def Constraints.system {I L} [Lattice L] (r : Constraints I L) : System I L where
  edge := r.Edge
  contrapose := by
    intro p a b h
    cases h with
    | original h => exact .original (r.contrapose h)
    | positive i f g h => exact .negative i g f h
    | negative i f g h => exact .positive i g f h
    | boundary i b => simpa only [complement,Bool.not_not] using Constraints.Edge.boundary (r := r) (p := p) i b
  restrict := by
    intro p q hpq a b h
    cases h with
    | original h => exact .original h
    | positive i f g h => exact .positive i f g (fun a ha => h a (hpq ha))
    | negative i f g h => exact .negative i f g (fun a ha => h a (hpq ha))
    | boundary i b => exact .boundary i b

/-- A finitely observed monotone assignment preserving the two constant
observers is represented by one finite lattice expression. -/
theorem finite_reify {L : Type*} [Lattice L] (p : Finset L)
    (v : LatticeHom L Bool → Bool)
    (mono : ∀f g,(∀a ∈ p,f a ≤ g a) → v f ≤ v g)
    (zero : v (constant false) = false) (one : v (constant true) = true) :
    ∃t : L,∀f,f t = v f := by
  classical
  let positives : Finset (p → Bool) := Finset.univ.filter
    (fun w => ∃f : LatticeHom L Bool,(∀a : p,f a.val = w a) ∧ v f = true)
  have hp : positives.Nonempty := by
    refine ⟨fun _ => true,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    exact ⟨constant true,fun _ => rfl,one⟩
  let inputs (w : p → Bool) : Finset p := Finset.univ.filter (fun a => w a = true)
  have hn (w : p → Bool) (hw : w ∈ positives) : (inputs w).Nonempty := by
    obtain ⟨f,hf,hv⟩ := (Finset.mem_filter.mp hw).2
    by_contra he
    have hle := mono f (constant false) (by
      intro a ha
      rw [hf ⟨a,ha⟩]
      cases hwa : w ⟨a,ha⟩ with
      | false => exact Bool.false_le _
      | true => exact False.elim (he ⟨⟨a,ha⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwa⟩⟩))
    rw [hv,zero] at hle
    exact (by decide : ¬(true : Bool) ≤ false) hle
  let meet (w : positives) : L := (inputs w.val).inf' (hn w.val w.property) Subtype.val
  have hm (w : positives) (f : LatticeHom L Bool) :
      f (meet w) = true ↔ ∀a : p,w.val a = true → f a.val = true := by
    constructor
    · intro hf a ha
      have hle := OrderHomClass.monotone f (Finset.inf'_le Subtype.val
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a,ha⟩ : a ∈ inputs w.val))
      change f (meet w) ≤ f a.val at hle
      rw [hf] at hle
      exact Bool.eq_true_of_true_le hle
    · intro hf
      change f ((inputs w.val).inf' (hn w.val w.property) Subtype.val) = true
      rw [map_finset_inf']
      apply Bool.eq_true_of_true_le
      apply Finset.le_inf'
      intro a ha
      rw [show (f ∘ Subtype.val) a = true from hf a (Finset.mem_filter.mp ha).2]
  let t : L := positives.attach.sup' hp.attach meet
  refine ⟨t,?_⟩
  intro f
  apply le_antisymm
  · change f (positives.attach.sup' hp.attach meet) ≤ v f
    rw [map_finset_sup']
    apply Finset.sup'_le
    intro w _
    apply Bool.le_iff_imp.mpr
    intro hmeet
    obtain ⟨g,hg,hv⟩ := (Finset.mem_filter.mp w.property).2
    apply Bool.le_iff_imp.mp (mono g f ?_) hv
    intro a ha
    apply Bool.le_iff_imp.mpr
    intro hga
    exact (hm w f).mp hmeet ⟨a,ha⟩ ((hg ⟨a,ha⟩).symm.trans hga)
  · apply Bool.le_iff_imp.mpr
    intro hv
    let w : p → Bool := fun a => f a.val
    have hw : w ∈ positives :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,f,fun _ => rfl,hv⟩
    have hmeet : f (meet ⟨w,hw⟩) = true := (hm _ f).mpr (fun _ ha => ha)
    have hle := OrderHomClass.monotone f (Finset.le_sup' meet
      (Finset.mem_attach positives ⟨w,hw⟩))
    change f (meet ⟨w,hw⟩) ≤ f t at hle
    rw [hmeet] at hle
    exact Bool.eq_true_of_true_le hle

def signedValue {I L} [Lattice L] (terms : I → L) (a : Point I L) : Bool :=
  if a.1 then a.2.2 (terms a.2.1) else !(a.2.2 (terms a.2.1))

def Constraints.Solvable {I L} [Lattice L] (r : Constraints I L) : Prop :=
  ∃terms : I → L,∀{a b},r.edge a b → signedValue terms a ≤ signedValue terms b

theorem Constraints.finite_model_reify {I L} [Lattice L] (r : Constraints I L)
    (p : Finset L) {model : Bool × I × (p → Bool) → Bool}
    (hm : (r.system.quotient p).Model model) : r.Solvable := by
  classical
  have hi (i : I) : ∃t : L,∀f,f t = model (observe p (true,i,f)) := by
    apply finite_reify p
    · intro f g hfg
      exact hm.edge ⟨(true,i,f),(true,i,g),rfl,rfl,.positive i f g hfg⟩
    · have hle := hm.edge ⟨(true,i,constant false),(false,i,constant false),
        rfl,rfl,Constraints.Edge.boundary (r := r) (p := p) i false⟩
      have hneg := hm.complement (observe p (true,i,constant false))
      change model (observe p (false,i,constant false)) =
        !model (observe p (true,i,constant false)) at hneg
      rw [hneg] at hle
      cases hv : model (observe p (true,i,constant false)) <;> simp_all [Bool.le_iff_imp]
    · have hle := hm.edge ⟨(false,i,constant true),(true,i,constant true),
        rfl,rfl,Constraints.Edge.boundary (r := r) (p := p) i true⟩
      have hneg := hm.complement (observe p (true,i,constant true))
      change model (observe p (false,i,constant true)) =
        !model (observe p (true,i,constant true)) at hneg
      rw [hneg] at hle
      cases hv : model (observe p (true,i,constant true)) <;> simp_all [Bool.le_iff_imp]
  choose terms ht using hi
  have he (a : Point I L) : signedValue terms a = model (observe p a) := by
    obtain ⟨b,i,f⟩ := a
    cases b with
    | true => exact ht i f
    | false =>
      have hneg := hm.complement (observe p (true,i,f))
      change model (observe p (false,i,f)) = !model (observe p (true,i,f)) at hneg
      exact (congrArg Bool.not (ht i f)).trans hneg.symm
  refine ⟨terms,?_⟩
  intro a b hab
  rw [he a,he b]
  exact hm.edge ⟨a,b,rfl,rfl,.original hab⟩

theorem Constraints.solvable_of_chain {I L} [Fintype I] [Lattice L]
    (r : Constraints I L) (h : r.system.ChainConsistent) : r.Solvable := by
  classical
  obtain ⟨p,hp⟩ := r.system.finite_consistent_iff.mpr h
  let V := Bool × I × (p → Bool)
  letI : Fintype V := by dsimp [V]; infer_instance
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  exact r.finite_model_reify p ((r.system.quotient p).canonical_model hp)

theorem Constraints.chain_of_solvable {I L} [Fintype I] [Lattice L]
    (r : Constraints I L) (h : r.Solvable) : r.system.ChainConsistent := by
  classical
  obtain ⟨terms,ht⟩ := h
  let p : Finset L := Finset.univ.image terms
  have hp (i : I) : terms i ∈ p := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  let value (a : Bool × I × (p → Bool)) : Bool :=
    if a.1 then a.2.2 ⟨terms a.2.1,hp a.2.1⟩ else !a.2.2 ⟨terms a.2.1,hp a.2.1⟩
  have he (a : Point I L) : value (observe p a) = signedValue terms a := rfl
  have hm : (r.system.quotient p).Model value := by
    constructor
    · rintro ⟨b,i,w⟩
      cases b <;> simp [value,System.quotient]
    · rintro _ _ ⟨a,b,rfl,rfl,hab⟩
      rw [he a,he b]
      cases hab with
      | original h => exact ht h
      | positive i f g h => exact h (terms i) (hp i)
      | negative i f g h =>
        have hh := h (terms i) (hp i)
        change (!(f (terms i))) ≤ (!(g (terms i)))
        cases hf : f (terms i) <;> cases hg : g (terms i) <;>
          simp_all [Bool.le_iff_imp]
      | boundary i b => cases b <;> simp [signedValue,constant]
  exact r.system.finite_consistent_iff.mp ⟨p,hm.consistent⟩

/-- A shared family of finite lattice terms exists exactly when the
finite-observation chain relation has no complementary strongly connected pair.
The criterion includes monotonicity and constant-boundary constraints, so it
characterizes term witnesses rather than arbitrary infinite Boolean assignments. -/
theorem Constraints.solvable_iff_chain {I L} [Fintype I] [Lattice L]
    (r : Constraints I L) : r.Solvable ↔ r.system.ChainConsistent :=
  ⟨r.chain_of_solvable,r.solvable_of_chain⟩

/-- Specialization to the original derivability lattice returns actual finite,
defined, shape-compatible internal types, simultaneously for all image keys. -/
theorem Constraints.carriers_iff_chain {I : Type*} [Fintype I]
    {Δ : Bounds} {shape : ComparisonShape}
    (r : Constraints I (ComparisonAlgebra.Order Δ shape)) :
    (∃images : I → ComparisonAlgebra.Carrier Δ shape,
      ∀{a b},r.edge a b →
        signedValue (fun i => ComparisonAlgebra.Order.of (images i)) a ≤
        signedValue (fun i => ComparisonAlgebra.Order.of (images i)) b) ↔
      r.system.ChainConsistent := by
  constructor
  · rintro ⟨images,hi⟩
    exact r.chain_of_solvable ⟨fun i => ComparisonAlgebra.Order.of (images i),hi⟩
  · intro h
    obtain ⟨terms,ht⟩ := r.solvable_of_chain h
    let images (i : I) : ComparisonAlgebra.Carrier Δ shape := (terms i).out
    have he : (fun i => ComparisonAlgebra.Order.of (images i)) = terms :=
      funext (fun i => Quotient.out_eq (terms i))
    exact ⟨images,he.symm ▸ ht⟩

end ModalityInference.ComparisonObserverChains
