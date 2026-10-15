import ModalityInference.Proofs.ComparisonBasisReflection
import ModalityInference.Proofs.ComparisonEndpointReflection

/-! Reflection of successful opaque-group propagation into guarded algebraic
subtyping for the reconstructed witnesses. -/
namespace ModalityInference.ComparisonElimination

open ComparisonAlgebra ComparisonControls ComparisonPropagation

def firstCoordinateBit : Coordinate → Bool
  | .unaffected | .locality => false
  | .affinity | .uniqueness => true

def secondCoordinateBit : Coordinate → Bool
  | .unaffected | .affinity => false
  | .locality | .uniqueness => true

def groupValuation (basis : Basis) (value : CompareTy → Bool) (c : Coordinate)
    (η : ModVar → Mode) (i : Nat) : Bool :=
  if i < basis.types.length then basisValue basis.types value i
  else if i = basis.types.length then firstCoordinateBit c
  else if i = basis.types.length + 1 then secondCoordinateBit c
  else encodeModes η (i - (basis.types.length + 2))

theorem groupValuation_prefix (basis : Basis) (value : CompareTy → Bool) (c : Coordinate)
    (η : ModVar → Mode) (i : Nat) (hi : i < basis.types.length) :
    groupValuation basis value c η i = basisValue basis.types value i := by
  simp only [groupValuation, if_pos hi]

@[simp] theorem groupValuation_first (basis : Basis) (value : CompareTy → Bool) (c : Coordinate)
    (η : ModVar → Mode) :
    groupValuation basis value c η basis.types.length = firstCoordinateBit c := by
  simp [groupValuation]

@[simp] theorem groupValuation_second (basis : Basis) (value : CompareTy → Bool) (c : Coordinate)
    (η : ModVar → Mode) :
    groupValuation basis value c η (basis.types.length + 1) = secondCoordinateBit c := by
  simp [groupValuation]

@[simp] theorem groupValuation_tail (basis : Basis) (value : CompareTy → Bool) (c : Coordinate)
    (η : ModVar → Mode) (i : Nat) :
    groupValuation basis value c η (basis.types.length + 2 + i) = encodeModes η i := by
  simp [groupValuation, show ¬basis.types.length + 2 + i < basis.types.length by omega,
    show basis.types.length + 2 + i ≠ basis.types.length by omega,
    show basis.types.length + 2 + i ≠ basis.types.length + 1 by omega]

theorem groupValuation_selected (basis : Basis) (value : CompareTy → Bool) (c : Coordinate)
    (η : ModVar → Mode) {pair : Coordinate × BoolExpr}
    (hp : pair ∈ coordinateCases basis.types.length)
    (he : pair.2.eval (groupValuation basis value c η) = true) : pair.1 = c := by
  simp only [coordinateCases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    cases c <;> simp_all [BoolExpr.eval, firstCoordinateBit, secondCoordinateBit]

theorem Basis.types_head_prefix (basis : Basis) (i : Nat) (hi : i < basis.heads.length) :
    basis.types[i]? = some basis.heads[i] := by
  simp [Basis.types, Basis.keys, List.getElem?_append, hi, Function.comp_def, Basis.term]

theorem groupValuation_heads (basis : Basis) (value : CompareTy → Bool) (c : Coordinate)
    (η : ModVar → Mode) (i : Nat) (hi : i < basis.heads.length) :
    groupValuation basis value c η i = value basis.heads[i] := by
  have hi' : i < basis.types.length := by
    simp only [Basis.types, Basis.keys, List.length_map, List.length_append] at *
    omega
  rw [groupValuation_prefix _ _ _ _ _ hi']
  simp only [basisValue, Basis.types_head_prefix basis i hi, Option.map_some, Option.getD_some]

theorem groupValuation_basis (basis : Basis) (value : CompareTy → Bool) (c : Coordinate)
    (η : ModVar → Mode) (i : Nat) (hi : i < basis.types.length) :
    groupValuation basis value c η i = value basis.types[i] := by
  rw [groupValuation_prefix _ _ _ _ _ hi]
  simp only [basisValue, List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

theorem GroupTrace.guards_hold {fuel assumptions required g output}
    (trace : GroupTrace fuel assumptions required g output) (value : CompareTy → Bool)
    (c : Coordinate) (η : ModVar → Mode)
    (hη : c = .unaffected ∨ ModeModels assumptions η ∧ ModeModels required η) :
    CNFHolds (groupValuation (groupBasis assumptions required g trace.first trace.rest) value c η)
      trace.guards := by
  apply (CompactCNF.toCNF_correct trace.guards_eq _).mpr
  simp only [BoolExpr.eval, SymbolicCNF.substitute_eval, groupValuation_first,
    groupValuation_second, groupValuation_tail]
  rcases hη with rfl | ⟨ha, hr⟩
  · rfl
  · have ha' := (boundsModeFormula_correct assumptions (encodeModes η)).mpr
      (by simpa only [projectedModes_encodeModes] using ha)
    have hr' := (boundsModeFormula_correct required (encodeModes η)).mpr
      (by simpa only [projectedModes_encodeModes] using hr)
    simp only [ha', hr', Bool.and_self, Bool.or_true]

theorem leaf_interval {basis : Basis} {names : List Nat} {v : TypeVar} {result : Leaf names.length}
    (h : leaf basis names v = .success result) (types : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (lower upper : Carrier Δ shape)
    (hfixed : ∀ v, (.var v : CompareTy) ∈ basis.heads → types v = .var v)
    (hheads : ∀ t ∈ basis.heads, InInterval lower upper (t.subst CompareTy.var ms))
    (himages : ∀ i : Fin names.length,
      InInterval lower upper ((types (.flex names[i])).subst CompareTy.var ms)) :
    InInterval lower upper ((types v).subst CompareTy.var ms) := by
  have hs := leaf_spec h
  cases result with
  | fixed clauses =>
    obtain ⟨i, hi, _⟩ := hs
    have hv := basis_index_head hi
    rw [hfixed v hv]
    exact hheads _ hv
  | flex i =>
    rw [hs]
    exact himages i

def instantiatedAtom (types : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (a : ComparisonGroups.Atom) : CompareTy :=
  .modal ((types a.head).subst CompareTy.var ms) (a.mode.subst ms)

theorem pair_labels {g : ComparisonGroups.Group} {pair : ComparisonGroups.Inequality}
    (hp : pair ∈ g.assumptions ++ g.goals) :
    pair.1.mode ∈ groupLabels g ∧ pair.2.mode ∈ groupLabels g := by
  constructor <;> apply List.mem_dedup.mpr <;>
    exact List.mem_flatMap.mpr ⟨pair, hp, by simp⟩

theorem booleanValue_mono (f : LatticeHom (Order Δ shape) Bool) {a b : CompareTy}
    (ha : Representable Δ shape a) (hb : Representable Δ shape b) (h : AlgebraSubtype Δ a b) :
    booleanValue f a = true → booleanValue f b = true := by
  simpa only [booleanValue_represented f a ha, booleanValue_represented f b hb] using
    observer_mono f (a := represented ha) (b := represented hb) h

theorem GroupTrace.sound {Δ : Bounds} {shape : ComparisonShape}
    {fuel assumptions required g output}
    (trace : GroupTrace fuel assumptions required g output)
    (types : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    (actual : (ModVar → Mode) → ModVar → Mode)
    (hactual : ∀ η v, (ms v).eval (some ∘ η) = some (actual η v))
    (hfixed : ∀ v ∈ g.heads, types v = .var v)
    (himages : ∀ i : Fin g.leaves.length, types (.flex g.leaves[i]) = trace.reduction.images[i])
    (hshape : ∀ v ∈ g.heads, Representable Δ shape (.var v))
    (hdefined : ∀ m ∈ groupLabels g, DefinedMode Δ (m.subst ms))
    (hquery : ∀ η, output.query.eval (encodeModes (actual η)) = true)
    (hguards : ∀ η, ModeModels Δ η →
      ModeModels assumptions (actual η) ∧ ModeModels required (actual η))
    (hassumptions : ∀ pair ∈ g.assumptions,
      AlgebraSubtype Δ (instantiatedAtom types ms pair.1) (instantiatedAtom types ms pair.2)) :
    ∀ pair ∈ g.goals,
      AlgebraSubtype Δ (instantiatedAtom types ms pair.1) (instantiatedAtom types ms pair.2) := by
  let basis := groupBasis assumptions required g trace.first trace.rest
  have hheads : basis.heads = g.heads.map CompareTy.var := by rw [trace.heads]; rfl
  have hfixed' : ∀ v, (.var v : CompareTy) ∈ basis.heads → types v = .var v := by
    intro v hv
    rw [hheads] at hv
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hv
    cases he
    exact hfixed v hw
  have hh : ∀ t ∈ basis.heads, Representable Δ shape (t.subst CompareTy.var ms) := by
    intro t ht
    rw [hheads] at ht
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
    exact hshape v hv
  have hm : ∀ v ∈ basis.modes, DefinedMode Δ (ms v) := by
    intro v _ η _
    simp only [ModExpr.WellFormed, hactual η v]
    rfl
  obtain ⟨lower, upper, hlo, hhi, hlu, hhead, hbasis, hpairs⟩ :=
    basis.carrier_interval CompareTy.var ms hh hm
  have himage : ∀ i : Fin g.leaves.length,
      InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top)
        ((types (.flex g.leaves[i])).subst CompareTy.var ms) := by
    intro i
    rw [himages i]
    exact InInterval.reify ((reduce_correct trace.reduction_eq).2.1 i) CompareTy.var ms hbasis
  intro pair hp
  obtain ⟨compiled, hcompiled, hc⟩ := trace.goal_compiled hp
  obtain ⟨hcL, hcR⟩ := bound_spec hc
  have hlabels := pair_labels (List.mem_append_right _ hp)
  have hleft := leaf_interval (endpoint_spec hcL).1 types ms _ _ hfixed' hhead himage
  have hright := leaf_interval (endpoint_spec hcR).1 types ms _ _ hfixed' hhead himage
  obtain ⟨ha, hla, hau⟩ := InInterval.modal hleft (hdefined _ hlabels.1)
  obtain ⟨hb, hlb, hbu⟩ := InInterval.modal hright (hdefined _ hlabels.2)
  apply (subtype_iff_boolean_observers (represented ha) (represented hb)).mpr
  intro f
  cases hbottom : observer f (lower.atMode Mode.bottom) with
  | true =>
    exact Bool.le_iff_imp.mpr fun _ => observer_mono f hlb hbottom
  | false =>
    cases htop : observer f (upper.atMode Mode.top) with
    | false =>
      exact Bool.le_iff_imp.mpr fun h => Bool.noConfusion (htop.symm.trans (observer_mono f hau h))
    | true =>
      obtain ⟨c, η, hη, hmodel⟩ := basis.observer_model f lower upper hlu hbottom htop
        ms actual hactual hm hpairs (groupLabels g) hdefined
      let value := fun t : CompareTy => booleanValue f (t.subst CompareTy.var ms)
      let τ := groupValuation basis value c (actual η)
      have hprefix : ∀ i < basis.types.length, τ i = basisValue basis.types value i :=
        groupValuation_prefix basis value c (actual η)
      have htail : ∀ i, τ (basis.types.length + 2 + i) = encodeModes (actual η) i :=
        groupValuation_tail basis value c (actual η)
      obtain ⟨htheory, hmodal⟩ := hmodel τ id id (basis.types.length + 2 + ·)
        (groupValuation_heads basis value c (actual η))
        (groupValuation_basis basis value c (actual η)) htail
      have hcontrols : CNFHolds τ trace.controls := by
        apply (controlsTheory_correct trace.controls_eq τ).mpr
        intro p hp hs
        have he := groupValuation_selected basis value c (actual η) hp hs
        simpa only [he] using htheory
      have hguard : CNFHolds τ trace.guards := by
        apply trace.guards_hold value c (actual η)
        exact hη.elim Or.inl (fun h => Or.inr (hguards η h))
      have hkey (k : Key) (hk : k ∈ basis.keys) :
          (basis.formula id (basis.types.length + 2 + ·) c k).eval τ = value (basis.term k) := by
        obtain ⟨i, hi⟩ := index_exists hk
        have he := theoryAt_index htheory hi
        rw [show id i = i from rfl, hprefix i (index_bound hi)] at he
        simpa only [basisValue, Basis.types, List.getElem?_map, index_lookup hi,
          Option.map_some, Option.getD_some] using he.symm
      have hbottom' : (basis.formula id (basis.types.length + 2 + ·) c .bottom).eval τ = false := by
        rw [hkey .bottom (by simp [Basis.keys])]
        change booleanValue f (basis.bottom.subst CompareTy.var ms) = false
        simpa only [Carrier.atMode_type, hlo, Basis.bottom, CompareTy.subst, ModExpr.subst] using
          (booleanValue_carrier f (lower.atMode Mode.bottom)).trans hbottom
      have htop' : (basis.formula id (basis.types.length + 2 + ·) c .top).eval τ = true := by
        rw [hkey .top (by simp [Basis.keys])]
        change booleanValue f (basis.top.subst CompareTy.var ms) = true
        simpa only [Carrier.atMode_type, hhi, Basis.top, CompareTy.subst, ModExpr.subst] using
          (booleanValue_carrier f (upper.atMode Mode.top)).trans htop
      let action := fun label => (trace.actions.lookup label).getD ⟨[[]], []⟩
      have hend {names : List Nat} (values : Fin names.length → Prop)
          (hvalues : ∀ i : Fin names.length,
            values i ↔ value (types (.flex names[i])) = true)
          (hinterval : ∀ i : Fin names.length,
            InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top)
              ((types (.flex names[i])).subst CompareTy.var ms))
          {atom : ComparisonGroups.Atom} {ep : Endpoint names.length}
          (he : endpoint basis names atom = .success ep) (hl : atom.mode ∈ groupLabels g) :
          ep.Holds action τ values ↔ booleanValue f (instantiatedAtom types ms atom) = true := by
        obtain ⟨hleaf, hmode⟩ := endpoint_spec he
        have hleafValue := leaf_holds_at hleaf value types values τ hprefix
          (fun i hi => congrArg value (hfixed' atom.head (basis_index_head hi)).symm) hvalues
        have hcompiled := trace.action_compiled hl
        have hcoordinate := endpoint_holds_coordinate
          (action := action) (by simpa only [hmode] using hcompiled.1)
          (by simpa only [hmode] using hcompiled.2) htheory hbottom' htop' hleafValue
        rw [hmode, ← hmodal (types atom.head)
          (leaf_interval hleaf types ms _ _ hfixed' hhead hinterval) atom.mode hl] at hcoordinate
        exact hcoordinate
      have hfull : CNFHolds τ trace.theory := by
        apply (trace.theory_correct τ).mpr
        refine ⟨hcontrols, hguard, ?_⟩
        intro assumption ham a b hea heb hva
        have hamodes := pair_labels (List.mem_append_left _ ham)
        have hva' := (hend (names := []) (fun i => nomatch i) (fun i => Fin.elim0 i)
          (fun i => Fin.elim0 i) hea hamodes.1).mp hva
        obtain ⟨hA, _, _⟩ := InInterval.modal
          (leaf_interval (endpoint_spec hea).1 types ms _ _ hfixed' hhead (fun i => Fin.elim0 i))
          (hdefined _ hamodes.1)
        obtain ⟨hB, _, _⟩ := InInterval.modal
          (leaf_interval (endpoint_spec heb).1 types ms _ _ hfixed' hhead (fun i => Fin.elim0 i))
          (hdefined _ hamodes.2)
        exact (hend (names := []) (fun i => nomatch i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
          heb hamodes.2).mpr (booleanValue_mono f hA hB (hassumptions assumption ham) hva')
      let values := fun i : Fin g.leaves.length => CNFHolds τ trace.reduction.store[i]
      have hvalues : ∀ i : Fin g.leaves.length,
          values i ↔ value (types (.flex g.leaves[i])) = true := by
        intro i
        rw [himages i]
        exact reduce_observer_at trace.reduction_eq f ms τ hprefix i
      have hL := hend values hvalues himage hcL hlabels.1
      have hR := hend values hvalues himage hcR hlabels.2
      apply Bool.le_iff_imp.mpr
      intro h
      have hleft := hL.mpr ((booleanValue_represented f _ ha).trans h)
      have hright := trace.goal_holds (hquery η) htail hfull hcompiled hleft
      exact (booleanValue_represented f _ hb).symm.trans (hR.mp hright)

end ModalityInference.ComparisonElimination
