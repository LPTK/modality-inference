import ModalityInference.Proofs.ComparisonObserverPorts
import ModalityInference.Proofs.ComparisonObserverProfileExtension

/-! Finite child boundary patterns with globally valid guarded modal actions.
Two finite signed-control layers provide representatives for every retained
Boolean fiber. Realizability is an exact child algebra obstruction; no
independent observer table or global range assumption is introduced. -/

namespace ModalityInference.ComparisonObserverPortProfiles

open ComparisonAlgebra ComparisonControls ComparisonObserverActions
  ComparisonObserverProfiles ComparisonObserverGluing ComparisonObserverProfileExtension

noncomputable def close (names : Finset ModVar) (ports : List CompareTy) : List CompareTy :=
  ports ++ ports.flatMap fun a => (generators names).map (CompareTy.modal a)

theorem mem_close {names ports a} (ha : a ∈ ports) : a ∈ close names ports :=
  List.mem_append_left _ ha

theorem modal_mem_close {names ports a m} (ha : a ∈ ports) (hm : m ∈ generators names) :
    CompareTy.modal a m ∈ close names ports :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨m,hm,rfl⟩⟩)

theorem generator_generated {names m} (hm : m ∈ generators names) : ComparisonObserverProfiles.Generated names m := by
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨m,_,rfl⟩ := List.mem_map.mp hm
    exact .const m
  · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
    obtain ⟨v,hv,hq⟩ := List.mem_flatMap.mp hq
    have hn : q.name = v := by
      cases q with
      | locality n p => cases p <;> simp_all [controls,Control.name]
      | affinity n u p | uniqueness n u p => cases u <;> cases p <;>
          simp_all [controls,Control.name]
    exact .control q (by simpa only [hn,Finset.mem_toList] using hv)

theorem generator_support {names m} (hm : m ∈ generators names) : m.vars ⊆ names := by
  have h := generator_generated hm
  clear hm
  induction h with
  | const m => simp [ModExpr.vars]
  | control q hq => simpa only [control_vars,Finset.singleton_subset_iff] using hq
  | compose _ _ ih₁ ih₂ | join _ _ ih₁ ih₂ | meet _ _ ih₁ ih₂ =>
    exact Finset.union_subset ih₁ ih₂

private theorem unit_representable (Δ : Bounds) : Representable Δ .unit .unit :=
  ⟨trivial, by simp [CompareTy.DefinedUnder,CompareTy.wellFormedBounds,ModeModels], .refl⟩

theorem close_representable {Δ names ports}
    (hp : ∀ a ∈ ports, Representable Δ .unit a) :
    ∀ a ∈ close names ports, Representable Δ .unit a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hp a ha
  · obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp ha
    have h := hp b hb
    exact ⟨h.1, CompareTy.definedUnder_modal_iff.mpr
      ⟨h.2.1,(generator_generated hm).defined⟩, h.2.2⟩

theorem close_support {names ports}
    (hp : ∀ a ∈ ports, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    ∀ a ∈ close names ports,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hp a ha
  · obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp ha
    exact ⟨hp b hb, fun _ hv => generator_support hm hv⟩

private def constantObserver {Δ : Bounds} (x : Bool) : LatticeHom (Order Δ .unit) Bool where
  toFun _ := x
  map_sup' _ _ := by cases x <;> rfl
  map_inf' _ _ := by cases x <;> rfl

private theorem constant_value {Δ x a} (ha : Representable Δ .unit a) :
    booleanValue (constantObserver (Δ := Δ) x) a = x := by
  rw [booleanValue_represented _ a ha]
  rfl

private def constantChild (Δ : Bounds) (x : Bool) : Child Δ where
  observer := constantObserver x
  transition := .identity Δ
  action m hm a ha := by
    rw [constant_value ha, constant_value
      (show Representable Δ .unit (.modal a m) from
        ⟨ha.1, CompareTy.definedUnder_modal_iff.mpr ⟨ha.2.1,hm⟩,ha.2.2⟩)]
    rfl

private theorem constant_range {Δ x y} (hy : (constantChild Δ x).Range y) : y = x := by
  obtain ⟨a,ha⟩ := hy
  exact ha.symm

theorem Transition.generated_fixes {Δ names} (t : Transition Δ) {x : Bool}
    (h : ∀ m ∈ generators names, t.apply m x = x)
    {m} (hm : ComparisonObserverProfiles.Generated names m) : t.apply m x = x := by
  induction hm with
  | const m => exact h _ (const_mem_generators names m)
  | control q hq => exact h _ (control_mem_generators q hq)
  | compose h₁ h₂ ih₁ ih₂ => rw [t.compose _ _ h₁.defined h₂.defined,ih₁,ih₂]
  | join h₁ h₂ ih₁ ih₂ => rw [t.join _ _ h₁.defined h₂.defined,ih₁,ih₂,Bool.or_self]
  | meet h₁ h₂ ih₁ ih₂ => rw [t.meet _ _ h₁.defined h₂.defined,ih₁,ih₂,Bool.and_self]

theorem Transition.restricted_fixes {Δ names} (t : Transition Δ) (hs : Δ.modVars ⊆ names)
    {x : Bool} (h : ∀ m ∈ generators names, t.apply m x = x)
    {m} (hm : Entails Δ (.defined m)) : (restricted t hs).apply m x = x := by
  have hd := (ComparisonModeRestriction.restrict_fixed Δ names hs).defined hm
  change t.apply (m.subst (ComparisonModeRestriction.restrict names)) x = x
  rw [← ComparisonObserverProfiles.Transition.normal_apply t hd x]
  exact Transition.generated_fixes t h (normal_generated
    (ComparisonModeRestriction.restrict_support names m))

/-- Two finite signed-control layers suffice to turn a realizable observation
pattern into an actual child with the prescribed guarded transfer on every
inhabited fiber. The range certificate is obtained from the first finite layer. -/
theorem realize {Δ names} (hs : Δ.modVars ⊆ names) (t : Transition Δ)
    (ports : List CompareTy) (value : CompareTy → Bool)
    (hp : ∀ a ∈ ports, Representable Δ .unit a)
    (hsupport : ∀ a ∈ ports,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (haction : ∀ a ∈ close names (.unit :: ports), ∀ m ∈ generators names,
      value (.modal a m) = t.apply m (value a))
    (f : LatticeHom (Order Δ .unit) Bool)
    (hf : ∀ a ∈ close names (close names (.unit :: ports)), booleanValue f a = value a) :
    ∃ g : Child Δ,
      (∀ a ∈ close names (.unit :: ports), booleanValue g.observer a = value a) ∧
      (∀ x, g.Range x → ∃ a ∈ close names (.unit :: ports), value a = x) ∧
      (∀ m, Entails Δ (.defined m) → ∀ x, g.Range x →
        g.transition.apply m x = (restricted t hs).apply m x) := by
  classical
  have hbase : ∀ a ∈ (.unit :: ports), Representable Δ .unit a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact unit_representable Δ
    · exact hp a ha
  have hbaseSupport : ∀ a ∈ (.unit :: ports),
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a := by
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · trivial
    · exact hsupport a ha
  have hrepr := close_representable (names := names) hbase
  have hsupp := close_support (names := names) hbaseSupport
  have hunit : CompareTy.unit ∈ close names (.unit :: ports) := mem_close (by simp)
  by_cases hc : ∀ a ∈ close names (.unit :: ports), value a = value .unit
  · refine ⟨constantChild Δ (value .unit), ?_, ?_, ?_⟩
    · intro a ha
      exact (constant_value (hrepr a ha)).trans (hc a ha).symm
    · intro x hx
      exact ⟨.unit,hunit,(constant_range hx).symm⟩
    · intro m hm x hx
      have hx := constant_range hx
      subst x
      change value .unit = (restricted t hs).apply m (value .unit)
      apply (Transition.restricted_fixes t hs ?_ hm).symm
      intro n hn
      exact (haction .unit hunit n hn).symm.trans
        (hc _ (modal_mem_close (by simp) hn))
  · have hboth (x : Bool) : ∃ a ∈ close names (.unit :: ports), value a = x := by
      push_neg at hc
      obtain ⟨a,ha,hne⟩ := hc
      cases he : value .unit <;> cases hx : value a <;> cases x
      all_goals first
        | exact ⟨.unit,hunit,he⟩
        | exact ⟨a,ha,hx⟩
        | exact False.elim (hne (hx.trans he.symm))
    let g := Child.ofObserver f
    have hprofile : profile g.transition names = profile t names := by
      apply List.map_eq_map_iff.mpr
      intro m hm
      have he (x : Bool) : g.transition.apply m x = t.apply m x := by
        obtain ⟨a,ha,hv⟩ := hboth x
        have hg := g.action m (generator_generated hm).defined a (hrepr a ha)
        change g.transition.apply m (booleanValue f a) = booleanValue f (.modal a m) at hg
        rw [hf a (mem_close ha),hf _ (modal_mem_close ha hm),haction a ha m hm,hv] at hg
        exact hg
      exact Prod.ext (he false) (he true)
    refine ⟨restrictedChild hs g, ?_, ?_, ?_⟩
    · intro a ha
      change booleanValue (restrictedObserver hs f) a = value a
      rw [restrictedObserver_booleanValue hs f (hrepr a ha),restrictedType_fixed (hsupp a ha)]
      exact hf a (mem_close ha)
    · intro x _
      exact hboth x
    · intro m hm x _
      exact profile_restricted hs hprofile hm x

/-- The finite port list carries its own definedness and shape witnesses. -/
noncomputable def carriers {Δ} (ports : List CompareTy)
    (hp : ∀ a ∈ ports, Representable Δ .unit a) : List (Carrier Δ .unit) :=
  ports.attach.map fun a => represented (hp a.val a.property)

theorem carrier_origin {Δ ports hp} {a : Carrier Δ .unit} (ha : a ∈ carriers ports hp) :
    a.type ∈ ports := by
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact b.property

theorem carrier_exists {Δ ports hp} {a : CompareTy} (ha : a ∈ ports) :
    ∃ b ∈ carriers (Δ := Δ) ports hp, b.type = a := by
  refine ⟨represented (hp a ha),List.mem_map.mpr ⟨⟨a,ha⟩,?_,rfl⟩,rfl⟩
  simp

noncomputable def patternObstruction {Δ} (ports : List CompareTy)
    (hp : ∀ a ∈ ports, Representable Δ .unit a) (value : CompareTy → Bool) : Prop :=
  ComparisonObserverPorts.carrierObstruction
    ((carriers ports hp).filter fun a => value a.type)
    ((carriers ports hp).filter fun a => !(value a.type))

/-- The only realization premise is one full child algebra obstruction between
finite meets and joins of the requested observation ports. -/
theorem pattern_iff {Δ} (ports : List CompareTy)
    (hp : ∀ a ∈ ports, Representable Δ .unit a) (value : CompareTy → Bool) :
    (∃ f : LatticeHom (Order Δ .unit) Bool,
      ∀ a ∈ ports, booleanValue f a = value a) ↔
      ¬ patternObstruction ports hp value := by
  rw [patternObstruction,←ComparisonObserverPorts.boolean_pattern_iff_no_obstruction]
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f,?_,?_⟩
    · intro a ha
      obtain ⟨ha,hv⟩ := List.mem_filter.mp ha
      exact (hf a.type (carrier_origin ha)).trans hv
    · intro a ha
      obtain ⟨ha,hv⟩ := List.mem_filter.mp ha
      have he : value a.type = false := by cases he : value a.type <;> simp_all
      exact (hf a.type (carrier_origin ha)).trans he
  · rintro ⟨f,ht,hf⟩
    refine ⟨f,fun a ha => ?_⟩
    obtain ⟨b,hb,hba⟩ := carrier_exists (Δ := Δ) (hp := hp) ha
    rw [←hba]
    cases hv : value b.type
    · exact hf b (List.mem_filter.mpr ⟨hb,by simp [hv]⟩)
    · exact ht b (List.mem_filter.mpr ⟨hb,hv⟩)

theorem layers_representable {Δ names ports}
    (hp : ∀ a ∈ ports, Representable Δ .unit a) :
    ∀ a ∈ close names (close names (.unit :: ports)), Representable Δ .unit a := by
  apply close_representable
  apply close_representable
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact unit_representable Δ
  · exact hp a ha

/-- An exact finite child obligation suffices for a global guarded child action;
no separately chosen child truth table or global range assumption is required. -/
theorem realize_of_no_obstruction {Δ names} (hs : Δ.modVars ⊆ names) (t : Transition Δ)
    (ports : List CompareTy) (value : CompareTy → Bool)
    (hp : ∀ a ∈ ports, Representable Δ .unit a)
    (hsupport : ∀ a ∈ ports,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (haction : ∀ a ∈ close names (.unit :: ports), ∀ m ∈ generators names,
      value (.modal a m) = t.apply m (value a))
    (hn : ¬ patternObstruction (close names (close names (.unit :: ports)))
      (layers_representable hp) value) :
    ∃ g : Child Δ,
      (∀ a ∈ close names (.unit :: ports), booleanValue g.observer a = value a) ∧
      (∀ x, g.Range x → ∃ a ∈ close names (.unit :: ports), value a = x) ∧
      (∀ m, Entails Δ (.defined m) → ∀ x, g.Range x →
        g.transition.apply m x = (restricted t hs).apply m x) := by
  obtain ⟨f,hf⟩ := (pattern_iff _ (layers_representable hp) value).mpr hn
  exact realize hs t ports value hp hsupport haction f hf

/-- The realized child's entire range is witnessed by the first finite layer. -/
theorem realize_exact {Δ names} (hs : Δ.modVars ⊆ names) (t : Transition Δ)
    (ports : List CompareTy) (value : CompareTy → Bool)
    (hp : ∀ a ∈ ports, Representable Δ .unit a)
    (hsupport : ∀ a ∈ ports,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (haction : ∀ a ∈ close names (.unit :: ports), ∀ m ∈ generators names,
      value (.modal a m) = t.apply m (value a))
    (hn : ¬ patternObstruction (close names (close names (.unit :: ports)))
      (layers_representable hp) value) :
    ∃ g : Child Δ,
      (∀ a ∈ close names (.unit :: ports), booleanValue g.observer a = value a) ∧
      (∀ x, g.Range x ↔ ∃ a ∈ close names (.unit :: ports), value a = x) ∧
      (∀ m, Entails Δ (.defined m) → ∀ x, g.Range x →
        g.transition.apply m x = (restricted t hs).apply m x) := by
  obtain ⟨g,hg,hr,ht⟩ := realize_of_no_obstruction hs t ports value hp hsupport haction hn
  refine ⟨g,hg,fun x => ⟨hr x,?_⟩,ht⟩
  rintro ⟨a,ha,hv⟩
  have hrepr : Representable Δ .unit a := layers_representable hp a (mem_close ha)
  have hh := g.range_value hrepr
  rwa [hg a ha,hv] at hh

/-- Every actual child can be replaced while preserving the finite boundary,
with global inhabited fibers now witnessed inside its finite control closure. -/
theorem child_replacement {Δ names} (hs : Δ.modVars ⊆ names) (g : Child Δ)
    (ports : List CompareTy)
    (hp : ∀ a ∈ ports, Representable Δ .unit a)
    (hsupport : ∀ a ∈ ports,
      ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    ∃ h : Child Δ,
      (∀ a ∈ close names (.unit :: ports),
        booleanValue h.observer a = booleanValue g.observer a) ∧
      (∀ x, h.Range x ↔ ∃ a ∈ close names (.unit :: ports), booleanValue g.observer a = x) ∧
      (∀ m, Entails Δ (.defined m) → ∀ x, h.Range x →
        h.transition.apply m x = (restrictedChild hs g).transition.apply m x) := by
  refine realize_exact hs g.transition ports (booleanValue g.observer) hp hsupport ?_ ?_
  · intro a ha m hm
    exact (g.action m (generator_generated hm).defined a
      (layers_representable hp a (mem_close ha))).symm
  · exact (pattern_iff _ (layers_representable hp) _).mp ⟨g.observer,fun _ _ => rfl⟩

end ModalityInference.ComparisonObserverPortProfiles
