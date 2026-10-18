import ModalityInference.Proofs.ComparisonObserverPortProfiles

/-! An exact root cut for defined algebraic comparisons in a context without a
finite shape model. The original declared endpoints retain their definedness
guards. Finite child patterns are tested by full child algebra comparisons;
modal transfers remain coherent across every guarded label. This is a root
certificate, not a bound on simultaneous substitution-witness syntax. -/

namespace ModalityInference.ComparisonObserverRootCut

open ComparisonAlgebra ComparisonControls ComparisonObserverActions ComparisonObserverProfiles
  ComparisonObserverGluing ComparisonObserverProfileExtension ComparisonObserverPortProfiles
  ComparisonStructuralLattice ComparisonStructuralObservers

/-- A root pattern contains scalar transfers and finite child observations,
without presupposing any child lattice observer. -/
structure Pattern (Δ : Bounds) where
  transition : Transition Δ
  atom : TypeVar → Bool
  unitValue : Bool
  creditValue : Bool
  left : Kind → Bool
  childTransition : Kind → Transition Δ
  childValue : Kind → CompareTy → Bool

def Pattern.sign {Δ} (p : Pattern Δ) (k : Kind) (x : Bool) : Bool :=
  if p.left k then leftSign k x else x

def Pattern.value {Δ} (p : Pattern Δ) : CompareTy → Bool
  | .var v => p.atom v
  | .unit => p.unitValue
  | .credit => p.creditValue
  | .prod a b => if p.left .prod then leftSign .prod (p.childValue .prod a) else p.childValue .prod b
  | .sum a b => if p.left .sum then leftSign .sum (p.childValue .sum a) else p.childValue .sum b
  | .fn a b => if p.left .fn then leftSign .fn (p.childValue .fn a) else p.childValue .fn b
  | .modal a m => p.transition.apply m (p.value a)
  | .join a b => p.value a || p.value b
  | .meet a b => p.value a && p.value b

def Pattern.data {Δ} (p : Pattern Δ) (children : Kind → Child Δ) : Data Δ where
  transition := p.transition
  atom := p.atom
  unitValue := p.unitValue
  creditValue := p.creditValue
  branch k := ⟨p.left k,children k⟩

theorem Pattern.data_value {Δ} (p : Pattern Δ) (children : Kind → Child Δ) (a : CompareTy)
    (hp : ∀ q ∈ ports a, booleanValue (children q.1).observer q.2 = p.childValue q.1 q.2) :
    (p.data children).value a = p.value a := by
  induction a with
  | var | unit | credit => rfl
  | prod a b =>
    have ha := hp (.prod,a) (by simp [ports])
    have hb := hp (.prod,b) (by simp [ports])
    simp only [Data.value,Pattern.data,Branch.value,ha,hb,Pattern.value]
  | sum a b =>
    have ha := hp (.sum,a) (by simp [ports])
    have hb := hp (.sum,b) (by simp [ports])
    simp only [Data.value,Pattern.data,Branch.value,ha,hb,Pattern.value]
  | fn a b =>
    have ha := hp (.fn,a) (by simp [ports])
    have hb := hp (.fn,b) (by simp [ports])
    simp only [Data.value,Pattern.data,Branch.value,ha,hb,Pattern.value]
  | modal a m ih => exact congrArg (p.transition.apply m) (ih hp)
  | join a b iha ihb =>
    exact congrArg₂ (· || ·) (iha (fun q h => hp q (List.mem_append_left _ h)))
      (ihb (fun q h => hp q (List.mem_append_right _ h)))
  | meet a b iha ihb =>
    exact congrArg₂ (· && ·) (iha (fun q h => hp q (List.mem_append_left _ h)))
      (ihb (fun q h => hp q (List.mem_append_right _ h)))

/-- The child cuts are full algebra comparisons. Modal coherence is checked
only at the finitely observed fibers; their global sufficiency is proved below. -/
structure Admissible {Δ names} (hs : Δ.modVars ⊆ names) (p : Pattern Δ)
    (boundary : List CompareTy)
    (hp : ∀ a ∈ portTypes boundary, Representable Δ .unit a) : Prop where
  action : ∀ k a, a ∈ close names (.unit :: portTypes boundary) →
    ∀ m ∈ generators names, p.childValue k (.modal a m) =
      (p.childTransition k).apply m (p.childValue k a)
  cut : ∀ k, ¬ patternObstruction
    (close names (close names (.unit :: portTypes boundary)))
    (layers_representable hp) (p.childValue k)
  pair : ∀ k, k = Kind.prod ∨ k = Kind.sum → ∀ m, Entails Δ (.defined m) →
    ∀ a ∈ close names (.unit :: portTypes boundary),
      p.transition.apply m ((restricted (p.childTransition k) hs).apply m (p.childValue k a)) =
        p.transition.apply m (p.childValue k a)
  fn : ∀ m n, Submode Δ m (.compose n .top) →
    ∀ a ∈ close names (.unit :: portTypes boundary),
      p.transition.apply m (p.sign .fn (p.childValue .fn a)) ≤
        p.transition.apply n (p.sign .fn (p.childValue .fn a))
  bounds : ∀ a b, Constraint.sub a b ∈ Δ → p.value (.ofTy a) ≤ p.value (.ofTy b)

/-- An admissible finite root pattern extends to an actual observer of the
full algebra, including its lattice equations and interval-clamp rules. -/
theorem Admissible.realize {Δ names} (hs : Δ.modVars ⊆ names) (p : Pattern Δ)
    (boundary : List CompareTy)
    (hp : ∀ a ∈ portTypes boundary, Representable Δ .unit a)
    (hsupport : ∀ a ∈ portTypes boundary,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (hc : Admissible hs p boundary hp)
    (hd : DeclaredIn Δ boundary)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined) :
    ∃ f : LatticeHom (Order Δ .unit) Bool,
      ∀ a ∈ boundary, a.DefinedUnder Δ → booleanValue f a = p.value a := by
  have hchildren (k : Kind) := realize_exact hs (p.childTransition k) (portTypes boundary)
    (p.childValue k) hp hsupport (hc.action k) (hc.cut k)
  choose children hv hr ht using hchildren
  have hcoherent : Coherent (p.data children) := by
    constructor
    · intro k hk m hm x hx
      change p.transition.apply m ((children k).transition.apply m x) = p.transition.apply m x
      rw [ht k m hm x hx]
      obtain ⟨a,ha,hax⟩ := (hr k x).mp hx
      rw [←hax]
      exact hc.pair k hk m hm a ha
    · intro m n hmn x hx
      obtain ⟨a,ha,hax⟩ := (hr .fn x).mp hx
      change p.transition.apply m (p.sign .fn x) ≤ p.transition.apply n (p.sign .fn x)
      rw [←hax]
      exact hc.fn m n hmn a ha
  have hvalues (a : CompareTy) (ha : a ∈ boundary) : (p.data children).value a = p.value a := by
    apply Pattern.data_value
    intro q hq
    exact hv q.1 q.2 (mem_close (List.mem_cons_of_mem _ (port_mem_portTypes ha hq)))
  have hbounds : BoundsHold (p.data children) := by
    intro a b hab
    rw [hvalues _ (hd a b hab).1,hvalues _ (hd a b hab).2]
    exact hc.bounds a b hab
  refine ⟨(p.data children).observer hcoherent hbounds hn hΔ,?_⟩
  intro a ha had
  exact ((p.data children).observer_value_defined hcoherent hbounds hn hΔ had).trans (hvalues a ha)

theorem port_defined {Δ a} (ha : CompareTy.DefinedUnder a Δ) :
    ∀ q ∈ ports a, q.2.DefinedUnder Δ := by
  induction a with
  | var | unit | credit => simp [ports]
  | prod a b | sum a b | fn a b =>
    have hh : a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
      exact CompareTy.definedUnder_prod_iff.mp ha
    intro q hq
    simp only [ports,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact hh.1
    · exact hh.2
  | modal a m ih => exact ih (CompareTy.definedUnder_modal_iff.mp ha).1
  | join a b iha ihb | meet a b iha ihb =>
    have hh : a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
      exact CompareTy.definedUnder_join_iff.mp ha
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact iha hh.1 q hq
    · exact ihb hh.2 q hq

theorem port_support {names : Finset ModVar} {a}
    (ha : ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    ∀ q ∈ ports a, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) q.2 := by
  induction a with
  | var | unit | credit => simp [ports]
  | prod a b | sum a b | fn a b =>
    intro q hq
    simp only [ports,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl | rfl
    · exact ha.1
    · exact ha.2
  | modal a m ih => exact ih ha.1
  | join a b iha ihb | meet a b iha ihb =>
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact iha ha.1 q hq
    · exact ihb ha.2 q hq

noncomputable def ofData {Δ names} (hs : Δ.modVars ⊆ names) (d : Data Δ) : Pattern Δ where
  transition := restricted d.transition hs
  atom := d.atom
  unitValue := d.unitValue
  creditValue := d.creditValue
  left k := (d.branch k).left
  childTransition k := (d.branch k).child.transition
  childValue k := booleanValue (d.branch k).child.observer

private theorem child_fixed_value {Δ names} (hs : Δ.modVars ⊆ names) (g : Child Δ)
    {a : CompareTy} (ha : Representable Δ .unit a)
    (hsupport : ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    booleanValue (restrictedChild hs g).observer a = booleanValue g.observer a := by
  change booleanValue (restrictedObserver hs g.observer) a = booleanValue g.observer a
  rw [restrictedObserver_booleanValue hs g.observer ha,restrictedType_fixed hsupport]

theorem ofData_value {Δ names} (hs : Δ.modVars ⊆ names) (d : Data Δ) (a : CompareTy)
    (hp : ∀ q ∈ ports a, Representable Δ .unit q.2)
    (hsupport : ∀ q ∈ ports a,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) q.2) :
    (ofData hs d).value a = (restrictedData hs d).value a := by
  symm
  exact (ofData hs d).data_value (fun k => restrictedChild hs (d.branch k).child) a
    (fun q hq => child_fixed_value hs _ (hp q hq) (hsupport q hq))

theorem ofData_admissible {Δ names} (hs : Δ.modVars ⊆ names) (d : Data Δ)
    (hc : Coherent d) (hb : BoundsHold d) (boundary : List CompareTy)
    (hd : DeclaredIn Δ boundary)
    (hp : ∀ a ∈ portTypes boundary, Representable Δ .unit a)
    (hsupport : ∀ a ∈ portTypes boundary,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined) :
    Admissible hs (ofData hs d) boundary hp := by
  have hrepr (a) (ha : a ∈ close names (.unit :: portTypes boundary)) :
      Representable Δ .unit a := layers_representable hp a (mem_close ha)
  have hsupp : ∀ a ∈ close names (.unit :: portTypes boundary),
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a := by
    apply close_support
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · trivial
    · exact hsupport a ha
  have hr (k : Kind) (a) (ha : a ∈ close names (.unit :: portTypes boundary)) :
      (restrictedChild hs (d.branch k).child).Range
        (booleanValue (d.branch k).child.observer a) := by
    rw [←child_fixed_value hs _ (hrepr a ha) (hsupp a ha)]
    exact (restrictedChild hs (d.branch k).child).range_value (hrepr a ha)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k a ha m hm
    exact ((d.branch k).child.action m (generator_generated hm).defined a (hrepr a ha)).symm
  · intro k
    exact (pattern_iff _ (layers_representable hp) _).mp
      ⟨(d.branch k).child.observer,fun _ _ => rfl⟩
  · intro k hk m hm a ha
    exact (restrictedData_coherent hs hc).pair k hk m hm _ (hr k a ha)
  · intro m n hmn a ha
    exact (restrictedData_coherent hs hc).fn m n hmn _ (hr .fn a ha)
  · intro a b hab
    rw [ofData_value hs d _ (fun q hq => hp _ (port_mem_portTypes (hd a b hab).1 hq))
      (fun q hq => hsupport _ (port_mem_portTypes (hd a b hab).1 hq)),
      ofData_value hs d _ (fun q hq => hp _ (port_mem_portTypes (hd a b hab).2 hq))
      (fun q hq => hsupport _ (port_mem_portTypes (hd a b hab).2 hq))]
    exact restrictedData_bounds hs d hn hΔ hb a b hab

/-- Every actual observer yields a root pattern satisfying the same finite
child cuts and range-coherence conditions used in the converse construction. -/
theorem observer_pattern {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (boundary : List CompareTy) (hd : DeclaredIn Δ boundary)
    (hp : ∀ a ∈ portTypes boundary, Representable Δ .unit a)
    (hsupport : ∀ a ∈ boundary,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (f : LatticeHom (Order Δ .unit) Bool) :
    ∃ p : Pattern Δ, Admissible hs p boundary hp ∧
      ∀ a ∈ boundary, a.DefinedUnder Δ → p.value a = booleanValue f a := by
  let d := extracted hn f
  have hports : ∀ a ∈ portTypes boundary,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a := by
    intro a ha
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
    exact port_support (hsupport b hb) q hq
  have hc := ofData_admissible hs d (extracted_coherent hn f)
    ((extracted_represents hn f).bounds hn hΔ) boundary hd hp hports hn hΔ
  refine ⟨ofData hs d,hc,?_⟩
  intro a ha had
  rw [ofData_value hs d a (fun q hq => hp _ (port_mem_portTypes ha hq))
    (port_support (hsupport a ha)),restrictedData_value hs d hn had,
    restrictedType_fixed (hsupport a ha)]
  exact extracted_represents hn f a had

/-- Root-pattern extension is exact, not merely a necessary observer test.
The child comparison premises retain the original full algebra. -/
theorem observer_iff_pattern {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (boundary : List CompareTy) (hd : DeclaredIn Δ boundary)
    (hp : ∀ a ∈ portTypes boundary, Representable Δ .unit a)
    (hsupport : ∀ a ∈ boundary,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (value : CompareTy → Bool) :
    (∃ f : LatticeHom (Order Δ .unit) Bool,
      ∀ a ∈ boundary, a.DefinedUnder Δ → booleanValue f a = value a) ↔
    (∃ p : Pattern Δ, Admissible hs p boundary hp ∧
      ∀ a ∈ boundary, a.DefinedUnder Δ → p.value a = value a) := by
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨p,hp,hv⟩ := observer_pattern hs hn hΔ boundary hd hp hsupport f
    exact ⟨p,hp,fun a ha had => (hv a ha had).trans (hf a ha had)⟩
  · rintro ⟨p,hp,hv⟩
    have hports : ∀ a ∈ portTypes boundary,
        ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a := by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
      exact port_support (hsupport b hb) q hq
    obtain ⟨f,hf⟩ := hp.realize hs p boundary _ hports hd hn hΔ
    exact ⟨f,fun a ha had => (hf a ha had).trans (hv a ha had)⟩

theorem not_subtype_iff_pattern {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (boundary : List CompareTy) (hd : DeclaredIn Δ boundary)
    (hp : ∀ a ∈ portTypes boundary, Representable Δ .unit a)
    (hsupport : ∀ a ∈ boundary,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    {a b : CompareTy} (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ)
    (hba : a ∈ boundary) (hbb : b ∈ boundary) :
    ¬ AlgebraSubtype Δ a b ↔ ∃ p : Pattern Δ,
      Admissible hs p boundary hp ∧ p.value a = true ∧ p.value b = false := by
  constructor
  · intro h
    have ha' := representable hn ha
    have hb' := representable hn hb
    obtain ⟨f,hfa,hfb⟩ := lattice_separator
      (show ¬ (Order.of (represented ha')) ≤ Order.of (represented hb') from h)
    obtain ⟨p,hp,hv⟩ := observer_pattern hs hn hΔ boundary hd hp hsupport f
    refine ⟨p,hp,?_,?_⟩
    · rw [hv a hba ha,booleanValue_represented f a ha']
      exact hfa
    · rw [hv b hbb hb,booleanValue_represented f b hb']
      exact hfb
  · rintro ⟨p,hp,hpa,hpb⟩ hab
    have hports : ∀ a ∈ portTypes boundary,
        ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a := by
      intro a ha
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ha
      obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
      exact port_support (hsupport b hb) q hq
    obtain ⟨f,hf⟩ := hp.realize hs p boundary _ hports hd hn hΔ
    have hv := value_mono (Child.ofObserver f) (representable hn ha) (representable hn hb) hab
    change booleanValue f a ≤ booleanValue f b at hv
    rw [hf a hba ha,hf b hbb hb,hpa,hpb] at hv
    exact (by decide : ¬(true : Bool) ≤ false) hv

def modeNames : CompareTy → Finset ModVar
  | .var _ | .unit | .credit => ∅
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => modeNames a ∪ modeNames b
  | .modal a m => modeNames a ∪ m.vars

theorem support_iff {names : Finset ModVar} (a : CompareTy) :
    ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a ↔ modeNames a ⊆ names := by
  induction a with
  | var | unit | credit => simp [ComparisonInterpolation.Supports,modeNames]
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb | join a b iha ihb | meet a b iha ihb =>
    simp only [ComparisonInterpolation.Supports,modeNames,Finset.union_subset_iff,iha,ihb]
  | modal a m ih =>
    simp only [ComparisonInterpolation.Supports,modeNames,Finset.union_subset_iff,ih]
    rfl

def boundaryNames (Δ : Bounds) (boundary : List CompareTy) : Finset ModVar :=
  Δ.modVars ∪ boundary.toFinset.biUnion modeNames

theorem boundaryNames_context (Δ : Bounds) (boundary : List CompareTy) :
    Δ.modVars ⊆ boundaryNames Δ boundary := Finset.subset_union_left

theorem boundaryNames_support (Δ : Bounds) (boundary : List CompareTy)
    {a : CompareTy} (ha : a ∈ boundary) :
    ComparisonInterpolation.Supports (fun _ => True) (· ∈ boundaryNames Δ boundary) a := by
  apply (support_iff a).mpr
  intro v hv
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a,by simpa using ha,hv⟩)

def declaredEndpoints (Δ : Bounds) : List CompareTy := Δ.flatMap fun c =>
  match c with
  | .sub a b => [.ofTy a,.ofTy b]
  | _ => []

def boundary (Δ : Bounds) (a b : CompareTy) : List CompareTy := a :: b :: declaredEndpoints Δ

theorem boundary_declared (Δ : Bounds) (a b : CompareTy) : DeclaredIn Δ (boundary Δ a b) := by
  intro s t hst
  have hs : CompareTy.ofTy s ∈ declaredEndpoints Δ :=
    List.mem_flatMap.mpr ⟨.sub s t,hst,by simp⟩
  have ht : CompareTy.ofTy t ∈ declaredEndpoints Δ :=
    List.mem_flatMap.mpr ⟨.sub s t,hst,by simp⟩
  exact ⟨by simp [boundary,hs],by simp [boundary,ht]⟩

theorem boundary_defined {Δ a b} (hΔ : Δ.TypeBoundsDefined)
    (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ) :
    ∀ c ∈ boundary Δ a b, c.DefinedUnder Δ := by
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ha
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hb
  obtain ⟨d,hd,hc⟩ := List.mem_flatMap.mp hc
  cases d with
  | sub s t =>
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact (CompareTy.definedUnder_ofTy _ _).mpr (hΔ s t hd).1
    · exact (CompareTy.definedUnder_ofTy _ _).mpr (hΔ s t hd).2
  | _ => simp at hc

theorem boundary_ports {Δ a b} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Δ.TypeBoundsDefined) (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ) :
    ∀ c ∈ portTypes (boundary Δ a b), Representable Δ .unit c := by
  intro c hc
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
  obtain ⟨d,hd,hq⟩ := List.mem_flatMap.mp hq
  exact representable hn (port_defined (boundary_defined hΔ ha hb d hd) q hq)

/-- Canonical exact root cut: every vertex and child port is drawn from the
original queried endpoints, the declared endpoints, and two finite control
layers. The child cuts still use the original full subtype judgment. -/
theorem not_subtype_iff_cut {Δ a b} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Δ.TypeBoundsDefined) (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ) :
    ¬ AlgebraSubtype Δ a b ↔ ∃ p : Pattern Δ,
      Admissible (boundaryNames_context Δ (boundary Δ a b)) p (boundary Δ a b)
        (boundary_ports hn hΔ ha hb) ∧ p.value a = true ∧ p.value b = false :=
  not_subtype_iff_pattern (boundaryNames_context Δ (boundary Δ a b)) hn hΔ
    (boundary Δ a b) (boundary_declared Δ a b) (boundary_ports hn hΔ ha hb)
    (fun _ h => boundaryNames_support Δ (boundary Δ a b) h) ha hb (by simp [boundary]) (by simp [boundary])

theorem subtype_iff_cut {Δ a b} (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Δ.TypeBoundsDefined) (ha : CompareTy.DefinedUnder a Δ) (hb : CompareTy.DefinedUnder b Δ) :
    AlgebraSubtype Δ a b ↔ ∀ p : Pattern Δ,
      Admissible (boundaryNames_context Δ (boundary Δ a b)) p (boundary Δ a b)
        (boundary_ports hn hΔ ha hb) → p.value a ≤ p.value b := by
  constructor
  · intro hab p hp
    by_contra h
    have hvalues : p.value a = true ∧ p.value b = false := by
      cases hea : p.value a <;> cases heb : p.value b <;> simp_all
    exact ((not_subtype_iff_cut hn hΔ ha hb).mpr ⟨p,hp,hvalues⟩) hab
  · intro h
    by_contra hab
    obtain ⟨p,hp,hpa,hpb⟩ := (not_subtype_iff_cut hn hΔ ha hb).mp hab
    have hv := h p hp
    rw [hpa,hpb] at hv
    exact (by decide : ¬(true : Bool) ≤ false) hv

end ModalityInference.ComparisonObserverRootCut
