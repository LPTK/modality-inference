import ModalityInference.Proofs.ComparisonObserverProfiles
import ModalityInference.Proofs.ComparisonObserverExtraction

/-! Finite transfer and range profiles extend to genuine constructor observers.
The extension is for guarded declared type bounds in a context without a finite
shape model. Restricting unused mode names justifies every guarded label, not
only the finite labels inspected by the profile. -/
namespace ModalityInference.ComparisonObserverProfileExtension

open ComparisonAlgebra ComparisonObserverActions ComparisonObserverProfiles
  ComparisonObserverGluing ComparisonModeRestriction ComparisonStructuralLattice

abbrev restrictedType (names : Finset ModVar) (a : CompareTy) : CompareTy :=
  a.subst CompareTy.var (ComparisonModeRestriction.restrict names)

def restrictedCarrier {Δ shape names} (hs : Δ.modVars ⊆ names)
    (a : Carrier Δ shape) : Carrier Δ shape where
  type := restrictedType names a.type
  shaped := (a.type.wellShaped_subst_modes_iff _).mpr a.shaped
  defined := (restrict_fixed Δ names hs).type_defined a.defined
  shape_eq := by simpa only [CompareTy.shape_subst_modes] using a.shape_eq

theorem restricted_representable {Δ shape names} (hs : Δ.modVars ⊆ names)
    {a : CompareTy} (ha : Representable Δ shape a) :
    Representable Δ shape (restrictedType names a) :=
  ⟨(a.wellShaped_subst_modes_iff _).mpr ha.1, (restrict_fixed Δ names hs).type_defined ha.2.1,
    by simpa only [CompareTy.shape_subst_modes] using ha.2.2⟩

noncomputable def restrictedObserver {Δ shape names} (hs : Δ.modVars ⊆ names)
    (f : LatticeHom (Order Δ shape) Bool) : LatticeHom (Order Δ shape) Bool where
  toFun := Quotient.lift (fun a : Carrier Δ shape => observer f (restrictedCarrier hs a)) (by
    intro a b hab
    apply congrArg f
    exact Quotient.sound ⟨(restrict_fixed Δ names hs).algebra hab.1,
      (restrict_fixed Δ names hs).algebra hab.2⟩)
  map_sup' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rename_i a b
    exact observer_join f (restrictedCarrier hs a) (restrictedCarrier hs b)
  map_inf' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rename_i a b
    exact observer_meet f (restrictedCarrier hs a) (restrictedCarrier hs b)

theorem restrictedObserver_value {Δ shape names} (hs : Δ.modVars ⊆ names)
    (f : LatticeHom (Order Δ shape) Bool) (a : Carrier Δ shape) :
    observer (restrictedObserver hs f) a = observer f (restrictedCarrier hs a) := rfl

theorem restrictedObserver_booleanValue {Δ shape names} (hs : Δ.modVars ⊆ names)
    (f : LatticeHom (Order Δ shape) Bool) {a : CompareTy} (ha : Representable Δ shape a) :
    booleanValue (restrictedObserver hs f) a = booleanValue f (restrictedType names a) := by
  rw [booleanValue_represented _ a ha,
    booleanValue_represented _ _ (restricted_representable hs ha)]
  rfl

noncomputable def restrictedChild {Δ names} (hs : Δ.modVars ⊆ names) (g : Child Δ) : Child Δ where
  observer := restrictedObserver hs g.observer
  transition := restricted g.transition hs
  action m hm a ha := by
    rw [restrictedObserver_booleanValue hs g.observer ha,
      restrictedObserver_booleanValue hs g.observer
        (show Representable Δ .unit (.modal a m) from
          ⟨ha.1, CompareTy.definedUnder_modal_iff.mpr ⟨ha.2.1, hm⟩, ha.2.2⟩)]
    exact g.action _ ((restrict_fixed Δ names hs).defined hm) _ (restricted_representable hs ha)

theorem restrictedChild_range {Δ names} (hs : Δ.modVars ⊆ names) (g : Child Δ) {x}
    (h : (restrictedChild hs g).Range x) : g.Range x := by
  obtain ⟨a, ha⟩ := h
  exact ⟨restrictedCarrier hs a, ha⟩


noncomputable def restrictedData {Δ names} (hs : Δ.modVars ⊆ names) (d : Data Δ) : Data Δ :=
  { d with
    transition := restricted d.transition hs
    branch := fun k => { left := (d.branch k).left, child := restrictedChild hs (d.branch k).child } }

theorem restrictedData_coherent {Δ names} (hs : Δ.modVars ⊆ names) {d : Data Δ}
    (hc : Coherent d) : Coherent (restrictedData hs d) where
  pair k hk _ hm x hx := hc.pair k hk _ ((restrict_fixed Δ names hs).defined hm) x
    (restrictedChild_range hs _ hx)
  fn _ _ h x hx := hc.fn _ _ ((restrict_fixed Δ names hs).submode h) x
    (restrictedChild_range hs _ hx)

theorem restrictedData_value {Δ names} (hs : Δ.modVars ⊆ names) (d : Data Δ)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) {a : CompareTy} (ha : a.DefinedUnder Δ) :
    (restrictedData hs d).value a = d.value (restrictedType names a) := by
  induction a with
  | var | unit | credit => rfl
  | prod a b iha ihb =>
    have hh := CompareTy.definedUnder_prod_iff.mp ha
    simp only [restrictedType, CompareTy.subst, Data.value, restrictedData, Branch.value, restrictedChild,
      restrictedObserver_booleanValue hs _ (representable hn hh.1),
      restrictedObserver_booleanValue hs _ (representable hn hh.2)]
  | sum a b iha ihb =>
    have hh := CompareTy.definedUnder_sum_iff.mp ha
    simp only [restrictedType, CompareTy.subst, Data.value, restrictedData, Branch.value, restrictedChild,
      restrictedObserver_booleanValue hs _ (representable hn hh.1),
      restrictedObserver_booleanValue hs _ (representable hn hh.2)]
  | fn a b iha ihb =>
    have hh := CompareTy.definedUnder_fn_iff.mp ha
    simp only [restrictedType, CompareTy.subst, Data.value, restrictedData, Branch.value, restrictedChild,
      restrictedObserver_booleanValue hs _ (representable hn hh.1),
      restrictedObserver_booleanValue hs _ (representable hn hh.2)]
  | modal a m ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp ha
    exact congrArg (d.transition.apply (m.subst (ComparisonModeRestriction.restrict names))) (ih hh.1)
  | join a b iha ihb =>
    have hh := CompareTy.definedUnder_join_iff.mp ha
    exact congrArg₂ (· || ·) (iha hh.1) (ihb hh.2)
  | meet a b iha ihb =>
    have hh := CompareTy.definedUnder_meet_iff.mp ha
    exact congrArg₂ (· && ·) (iha hh.1) (ihb hh.2)

theorem restrictedType_fixed {names : Finset ModVar} {a : CompareTy}
    (hs : ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a) :
    restrictedType names a = a := by
  induction a <;> simp only [ComparisonInterpolation.Supports] at hs <;>
    simp only [restrictedType, CompareTy.subst]
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb |
      join a b iha ihb | meet a b iha ihb =>
    congr 1
    · exact iha hs.1
    · exact ihb hs.2
  case modal a m ih =>
    congr 1
    · exact ih hs.1
    · rw [m.subst_congr (τ := ModExpr.var) (fun v hv => by
        simp [ComparisonModeRestriction.restrict, hs.2 v hv])]
      exact m.subst_id

theorem restrictedData_bounds {Δ names} (hs : Δ.modVars ⊆ names) (d : Data Δ)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined) (hb : BoundsHold d) :
    BoundsHold (restrictedData hs d) := by
  intro a b hab
  rw [restrictedData_value hs d hn ((CompareTy.definedUnder_ofTy a Δ).mpr (hΔ a b hab).1),
    restrictedData_value hs d hn ((CompareTy.definedUnder_ofTy b Δ).mpr (hΔ a b hab).2)]
  have hfa : restrictedType names (.ofTy a) = .ofTy a := ofTy_fixed a (by
    intro v hv
    exact (restrict_fixed Δ names hs).fixed v ((Δ.mem_modVars_iff v).mpr
      ⟨.sub a b, hab, by simp [Constraint.modVars, hv]⟩))
  have hfb : restrictedType names (.ofTy b) = .ofTy b := ofTy_fixed b (by
    intro v hv
    exact (restrict_fixed Δ names hs).fixed v ((Δ.mem_modVars_iff v).mpr
      ⟨.sub a b, hab, by simp [Constraint.modVars, hv]⟩))
  rw [hfa, hfb]
  exact hb a b hab


/-- Finite observations retain transfer, inhabited fibers, and the requested
child boundary values. The range entries are global properties of the observer. -/
structure ChildProfile where
  transfer : List (Bool × Bool)
  range : Bool × Bool
  values : List Bool
  deriving DecidableEq

noncomputable def childProfile {Δ names} (hs : Δ.modVars ⊆ names) (g : Child Δ)
    (probes : List CompareTy) : ChildProfile := by
  classical
  exact ⟨profile g.transition names,
    (decide ((restrictedChild hs g).Range false), decide ((restrictedChild hs g).Range true)),
    probes.map (booleanValue (restrictedChild hs g).observer)⟩

theorem childProfile_range {Δ names} (hs : Δ.modVars ⊆ names) {g h : Child Δ}
    {probes : List CompareTy} (he : childProfile hs g probes = childProfile hs h probes)
    {x : Bool} (hx : (restrictedChild hs g).Range x) : (restrictedChild hs h).Range x := by
  classical
  have hr := congrArg ChildProfile.range he
  cases x
  · have hh := congrArg Prod.fst hr
    change decide ((restrictedChild hs g).Range false) = decide ((restrictedChild hs h).Range false) at hh
    have ht : decide ((restrictedChild hs g).Range false) = true := decide_eq_true hx
    rw [hh] at ht
    exact of_decide_eq_true ht
  · have hh := congrArg Prod.snd hr
    change decide ((restrictedChild hs g).Range true) = decide ((restrictedChild hs h).Range true) at hh
    have ht : decide ((restrictedChild hs g).Range true) = true := decide_eq_true hx
    rw [hh] at ht
    exact of_decide_eq_true ht

theorem childProfile_action {Δ names} (hs : Δ.modVars ⊆ names) {g h : Child Δ}
    {probes : List CompareTy} (he : childProfile hs g probes = childProfile hs h probes)
    {m} (hm : Entails Δ (.defined m)) (x : Bool) :
    (restrictedChild hs g).transition.apply m x = (restrictedChild hs h).transition.apply m x :=
  profile_restricted hs (congrArg ChildProfile.transfer he) hm x

theorem childProfile_value {Δ names} (hs : Δ.modVars ⊆ names) {g h : Child Δ}
    {probes : List CompareTy} (he : childProfile hs g probes = childProfile hs h probes)
    {a : CompareTy} (ha : a ∈ probes) :
    booleanValue (restrictedChild hs g).observer a = booleanValue (restrictedChild hs h).observer a :=
  List.map_eq_map_iff.mp (congrArg ChildProfile.values he) a ha

def portTypes (boundary : List CompareTy) : List CompareTy := (boundary.flatMap ports).map Prod.snd

theorem port_mem_portTypes {boundary : List CompareTy} {a : CompareTy} (ha : a ∈ boundary)
    {p : Kind × CompareTy} (hp : p ∈ ports a) : p.2 ∈ portTypes boundary :=
  List.mem_map.mpr ⟨p, List.mem_flatMap.mpr ⟨a, ha, hp⟩, rfl⟩

/-- Equal finite child profiles give a genuine parent extension preserving the
chosen finite boundary. Modality support is discharged by actual name restriction;
the modal condition of `Replacement` is not an additional premise. -/
theorem finite_profile_extension {Δ names} (hs : Δ.modVars ⊆ names) (d : Data Δ)
    (hc : Coherent d) (hb : BoundsHold d) (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Δ.TypeBoundsDefined) (children : Kind → Child Δ) (boundary : List CompareTy)
    (hd : DeclaredIn Δ boundary)
    (hsb : ∀ a ∈ boundary, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (hp : ∀ k, childProfile hs (children k) (portTypes boundary) =
      childProfile hs (d.branch k).child (portTypes boundary)) :
    ∃ f : LatticeHom (Order Δ .unit) Bool,
      (∀ a, a.DefinedUnder Δ → booleanValue f a =
        ((restrictedData hs d).replace (fun k => restrictedChild hs (children k))).value a) ∧
      (∀ a ∈ boundary, a.DefinedUnder Δ → booleanValue f a = d.value a) := by
  have hr : Replacement (restrictedData hs d) (fun k => restrictedChild hs (children k)) :=
    ⟨fun k _ hx => childProfile_range hs (hp k) hx,
      fun k _ hm x _ => childProfile_action hs (hp k) hm x⟩
  have hports : PortsAgree (restrictedData hs d) (fun k => restrictedChild hs (children k)) boundary := by
    intro a ha p hp'
    exact childProfile_value hs (hp p.1) (port_mem_portTypes ha hp')
  obtain ⟨f, hf, hbound⟩ := observer_extension (restrictedData hs d)
    (restrictedData_coherent hs hc) (restrictedData_bounds hs d hn hΔ hb) hn hΔ
    (fun k => restrictedChild hs (children k)) hr boundary hd hports
  refine ⟨f, hf, fun a ha had => ?_⟩
  rw [hbound a ha had, restrictedData_value hs d hn had, restrictedType_fixed (hsb a ha)]

/-- Every actual parent observer admits replacement using only the finite
profiles of its selected children, without assuming an independent modal model. -/
theorem extracted_finite_profile_extension {Δ names} (hs : Δ.modVars ⊆ names)
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (f : LatticeHom (Order Δ .unit) Bool) (children : Kind → Child Δ)
    (boundary : List CompareTy) (hd : DeclaredIn Δ boundary)
    (hsb : ∀ a ∈ boundary, ComparisonInterpolation.Supports (fun _ => True) (· ∈ names) a)
    (hp : ∀ k, childProfile hs (children k) (portTypes boundary) =
      childProfile hs ((extracted hn f).branch k).child (portTypes boundary)) :
    ∃ g : LatticeHom (Order Δ .unit) Bool,
      (∀ a, a.DefinedUnder Δ → booleanValue g a =
        ((restrictedData hs (extracted hn f)).replace (fun k => restrictedChild hs (children k))).value a) ∧
      (∀ a ∈ boundary, a.DefinedUnder Δ → booleanValue g a = booleanValue f a) := by
  have hr := extracted_represents hn f
  obtain ⟨g, hg, hbound⟩ := finite_profile_extension hs (extracted hn f)
    (extracted_coherent hn f) (hr.bounds hn hΔ) hn hΔ children boundary hd hsb hp
  exact ⟨g, hg, fun a ha had => (hbound a ha had).trans (hr a had)⟩

end ModalityInference.ComparisonObserverProfileExtension
