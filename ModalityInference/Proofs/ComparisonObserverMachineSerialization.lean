import ModalityInference.Proofs.ComparisonObserverCoordinateAlignment
import ModalityInference.Proofs.ComparisonObserverCoordinateRealization
import ModalityInference.Proofs.ComparisonObserverMachineActions

/-! Coordinate machines admit exact finite descriptions on their retained
input names. Unlisted type atoms use the inhabited unit value. -/
namespace ModalityInference.ComparisonObserverMachineSerialization

open ComparisonAlgebra ComparisonControls ComparisonInterpolation
  ComparisonObserverMachine ComparisonObserverMachineCheck
  ComparisonObserverGluing ComparisonObserverProfiles ComparisonObserverRepresentatives
  ComparisonObserverProfileExtension

variable {State : Type}

def serialize (types : List TypeVar) (names : List ModVar) (original : State → Node State)
    (coordinates : State → Coordinate) (worlds : State → ModVar → Mode)
    (i : State) : Description State where
  atoms := types.map (original i).atom
  modes := names.map (worlds i)
  coordinate := coordinates i
  unitValue := (original i).unitValue
  creditValue := (original i).creditValue
  branch := (original i).branch
  range := (original i).range

private theorem getElem_idxOf_mem {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {a : α}
    (ha : a ∈ xs) : xs[xs.idxOf a]? = some a := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    by_cases hb : b = a
    · subst b
      simp
    · have hx : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hb)
      have he : (b == a) = false := beq_eq_false_iff_ne.mpr hb
      simpa [List.idxOf_cons, he] using ih hx

theorem atom_serialize {types names original coordinates worlds} {i : State} {v : TypeVar}
    (hv : v ∈ types) :
    atomValue types (serialize types names original coordinates worlds i) v = (original i).atom v := by
  simp [atomValue, serialize, hv, List.getElem?_map, getElem_idxOf_mem hv]

theorem mode_serialize {types names original coordinates worlds} {i : State}
    (hw : ∀v ∉ names, worlds i v = Mode.identity) :
    modeValue names (serialize types names original coordinates worlds i) = worlds i := by
  funext v
  by_cases hv : v ∈ names
  · simp [modeValue, serialize, hv, List.getElem?_map, getElem_idxOf_mem hv]
  · simp [modeValue, hv, hw v hv]

structure Coordinates (Δ : Bounds) (names : List ModVar) (original : State → Node State)
    (coordinates : State → Coordinate) (worlds : State → ModVar → Mode) : Prop where
  outside : ∀i v, v ∉ names → worlds i v = Mode.identity
  models : ∀i, coordinates i = .unaffected ∨ ModeModels Δ (worlds i)
  active : ∀i, coordinates i ≠ .unaffected → ∀x, (original i).range x = true
  action : ∀i m, Entails Δ (.defined m) → ∀x, (original i).range x = true →
    (original i).action m x = coordinateValue (coordinates i) x (m.complete (worlds i))

theorem scalar_serialize {Δ types names} {original : State → Node State} {coordinates worlds}
    (h : Coordinates Δ names original coordinates worlds) (i : State) :
    scalarOK Δ names (serialize types names original coordinates worlds i) = true := by
  apply scalarOK_correct.mpr
  rw [mode_serialize (h.outside i)]
  exact h.models i

theorem actions_agree {Δ types names} {original : State → Node State} {coordinates worlds}
    (h : Coordinates Δ names original coordinates worlds) :
    ActionsAgree Δ original (fun i => action names (serialize types names original coordinates worlds i)) := by
  intro i m hm x hx
  change action names (serialize types names original coordinates worlds i) m x = _
  rw [action_complete (scalar_serialize (types := types) h i) hm, mode_serialize (h.outside i)]
  exact (h.action i m hm x hx).symm

theorem serialize_value {Δ types names} {original : State → Node State} {coordinates worlds}
    (h : Coordinates Δ names original coordinates worlds)
    (hr : RangeClosed Δ original) {a : CompareTy}
    (ha : a.DefinedUnder Δ) (ht : Supports (· ∈ types) (fun _ => True) a) (i : State) :
    value (nodes types names (serialize types names original coordinates worlds)) a i =
      value original a i := by
  induction a generalizing i with
  | var v => exact atom_serialize ht
  | unit | credit => rfl
  | prod a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_prod_iff.mp ha
    simp only [value, nodes, serialize, iha ha ht.1, ihb hb ht.2]
  | sum a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_sum_iff.mp ha
    simp only [value, nodes, serialize, iha ha ht.1, ihb hb ht.2]
  | fn a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_fn_iff.mp ha
    simp only [value, nodes, serialize, iha ha ht.1, ihb hb ht.2]
  | modal a m ih =>
    obtain ⟨ha,hm⟩ := CompareTy.definedUnder_modal_iff.mp ha
    change action names (serialize types names original coordinates worlds i) m
      (value (nodes types names (serialize types names original coordinates worlds)) a i) = _
    rw [ih ha ht.1]
    exact actions_agree h i m hm _ (hr.value_mem ha i)
  | join a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_join_iff.mp ha
    exact congrArg₂ (· || ·) (iha ha ht.1 i) (ihb hb ht.2 i)
  | meet a b iha ihb =>
    obtain ⟨ha,hb⟩ := CompareTy.definedUnder_meet_iff.mp ha
    exact congrArg₂ (· && ·) (iha ha ht.1 i) (ihb hb ht.2 i)

theorem serialize_range {Δ types names} {original : State → Node State} {coordinates worlds}
    (h : Coordinates Δ names original coordinates worlds) (hr : RangeClosed Δ original) :
    RangeClosed Δ (nodes types names (serialize types names original coordinates worlds)) := by
  refine ⟨?_, hr.unit, hr.credit, hr.branch, (hr.withActions (actions_agree h)).modal⟩
  intro i v
  change (original i).range (atomValue types (serialize types names original coordinates worlds i) v) = true
  by_cases hv : v ∈ types
  · rw [atom_serialize hv]
    exact hr.atom i v
  · simpa only [atomValue, List.contains_eq_mem, hv, decide_false, Bool.false_eq_true,
      if_false, serialize] using hr.unit i

theorem serialize_coherent {Δ types names} {original : State → Node State} {coordinates worlds}
    (h : Coordinates Δ names original coordinates worlds)
    (hr : RangeClosed Δ original) (hc : Coherent Δ original) :
    Coherent Δ (nodes types names (serialize types names original coordinates worlds)) :=
  ⟨(hc.withActions hr (actions_agree (types := types) h)).pair,
    (hc.withActions hr (actions_agree (types := types) h)).fn⟩

theorem serialize_bounds {Δ types names} {original : State → Node State} {coordinates worlds}
    (h : Coordinates Δ names original coordinates worlds) (hr : RangeClosed Δ original)
    (hb : BoundsHold Δ original) (hΔ : Δ.TypeBoundsDefined)
    (ht : ∀a b, .sub a b ∈ Δ → Supports (· ∈ types) (fun _ => True) (.ofTy a) ∧
      Supports (· ∈ types) (fun _ => True) (.ofTy b)) :
    BoundsHold Δ (nodes types names (serialize types names original coordinates worlds)) := by
  intro i a b hab
  rw [serialize_value h hr ((CompareTy.definedUnder_ofTy a Δ).mpr (hΔ a b hab).1) (ht a b hab).1,
    serialize_value h hr ((CompareTy.definedUnder_ofTy b Δ).mpr (hΔ a b hab).2) (ht a b hab).2]
  exact hb i a b hab

theorem serialize_checked {count : Nat} {Δ types names} {original : Machine count} {coordinates worlds}
    (h : Coordinates Δ names original coordinates worlds) (hc : Certified Δ original)
    (hΔ : Δ.TypeBoundsDefined)
    (ht : ∀a b, .sub a b ∈ Δ → Supports (· ∈ types) (fun _ => True) (.ofTy a) ∧
      Supports (· ∈ types) (fun _ => True) (.ofTy b)) :
    check Δ types names (serialize types names original coordinates worlds) = true := by
  apply ComparisonObserverCoordinateAlignment.check_complete (scalar_serialize h)
    (serialize_range h hc.range) (serialize_coherent h hc.range hc.coherent)
    (serialize_bounds h hc.range hc.bounds hΔ ht)
  intro i
  by_cases hi : coordinates i = .unaffected
  · exact Or.inl hi
  · exact Or.inr (h.active i hi)

/-- One finite checked description preserves every genuine observer's values
on a supported, port-closed boundary, with the original representative bound. -/
theorem bounded_descriptions_on {Δ : Bounds} {names : Finset ModVar}
    (hs : Δ.modVars ⊆ names) (hn : ¬ ∃ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Δ.TypeBoundsDefined) (types : List TypeVar) (modes : List ModVar)
    (hml : ∀v, v ∈ modes ↔ v ∈ names) (boundary : List CompareTy)
    (hp : ComparisonObserverRepresentatives.PortsClosed boundary)
    (hd : ComparisonObserverGluing.DeclaredIn Δ boundary)
    (hm : ∀a ∈ boundary, Supports (fun _ => True) (· ∈ names) a)
    (ht : ∀a ∈ boundary, Supports (· ∈ types) (fun _ => True) a) :
    ∃count ≤ 2 ^ (2 * (8 + 10 * names.card) + 2 + boundary.length),
      ∃data : Fin count → Description (Fin count), check Δ types modes data = true ∧
      ∀f : LatticeHom (Order Δ .unit) Bool, ∃i : Fin count,
        ∀a ∈ boundary, a.DefinedUnder Δ →
          value (nodes types modes data) a i = booleanValue f a := by
  classical
  let S := ComparisonObserverFiniteMachine.State hs boundary
  let e := (Fintype.equivFin S).symm
  let original := ComparisonObserverMachine.transport e (ComparisonObserverFiniteMachine.nodes hs hn boundary)
  have hz (i : Fin (Fintype.card S)) :=
    ComparisonObserverCoordinateRealization.representative_realization hs (e i).property
  choose coordinates worlds outside models active actions using hz
  have hc : Coordinates Δ modes original coordinates worlds := by
    refine ⟨?_, models, ?_, ?_⟩
    · intro i v hv
      exact outside i v (fun hvn => hv ((hml v).mpr hvn))
    · intro i hi x
      change decide ((e i).val.Range x) = true
      exact decide_eq_true (by cases x; exact (active i hi).1; exact (active i hi).2)
    · intro i m hm x hx
      exact actions i m hm x (of_decide_eq_true hx)
  have hcert : Certified Δ original :=
    (ComparisonObserverFiniteMachine.certified hs hn hΔ boundary hp hd hm).transport e
  refine ⟨Fintype.card S, ?_, serialize types modes original coordinates worlds,
    serialize_checked hc hcert hΔ (fun a b hab => ⟨ht _ (hd a b hab).1, ht _ (hd a b hab).2⟩), ?_⟩
  · exact (Fintype.card_coe (representatives hs boundary)).le.trans (representatives_card hs boundary)
  · intro f
    obtain ⟨r,hr,_,_,hv⟩ := representatives_cover hs boundary (Child.ofObserver f)
    let j : S := ⟨r,hr⟩
    refine ⟨e.symm j, ?_⟩
    intro a ha had
    rw [serialize_value hc hcert.range had (ht a ha)]
    change value (transport e (ComparisonObserverFiniteMachine.nodes hs hn boundary)) a (e.symm j) = _
    rw [transport_value, Equiv.apply_symm_apply,
      ComparisonObserverFiniteMachine.value_eq hs hn boundary hp _ had (hm a ha) (hp a ha)]
    change booleanValue r.observer a = booleanValue f a
    rw [← hv a ha]
    change booleanValue (restrictedObserver hs f) a = booleanValue f a
    rw [restrictedObserver_booleanValue hs f (representable hn had), restrictedType_fixed (hm a ha)]

theorem bounded_descriptions {Δ : Bounds} {names : Finset ModVar}
    (hs : Δ.modVars ⊆ names) (hn : ¬ ∃ρ, ComparisonShape.Models Δ ρ)
    (hΔ : Δ.TypeBoundsDefined) (types : List TypeVar) (boundary : List CompareTy)
    (hp : ComparisonObserverRepresentatives.PortsClosed boundary)
    (hd : ComparisonObserverGluing.DeclaredIn Δ boundary)
    (hm : ∀a ∈ boundary, Supports (fun _ => True) (· ∈ names) a)
    (ht : ∀a ∈ boundary, Supports (· ∈ types) (fun _ => True) a) :
    ∃count ≤ 2 ^ (2 * (8 + 10 * names.card) + 2 + boundary.length),
      ∃data : Fin count → Description (Fin count), check Δ types names.toList data = true ∧
      ∀f : LatticeHom (Order Δ .unit) Bool, ∃i : Fin count,
        ∀a ∈ boundary, a.DefinedUnder Δ →
          value (nodes types names.toList data) a i = booleanValue f a :=
  bounded_descriptions_on hs hn hΔ types names.toList (by simp) boundary hp hd hm ht

end ModalityInference.ComparisonObserverMachineSerialization
