import ModalityInference.ComparisonRankedJoint
import ModalityInference.Proofs.ComparisonRankedModesReconstruction
import ModalityInference.Proofs.ComparisonRankedPrepared
import ModalityInference.Proofs.ComparisonPreparedModeWitness
import ModalityInference.Proofs.ComparisonPreparedModeSupport

/-! Arbitrary original-context comparison witnesses supply one shared ranked
image family and one common, existentially synthesized modality strategy. -/
namespace ModalityInference.ComparisonRankedJoint

open ComparisonPreparation ComparisonSelectedBases ComparisonRankedBasis
  ComparisonControls ComparisonAlgebra ComparisonInterpolation

theorem mem_fixedNames {p : SchemePreparation.Prepared} {v : ModVar} :
    v ∈ fixedNames p ↔ v ∈ inputModes p ∧ v.index < p.firstMode := by
  simp [fixedNames]

theorem mem_modeIds {p : SchemePreparation.Prepared} {k : Nat} :
    k ∈ modeIds p ↔ ModVar.flex k ∈ inputModes p ∧ p.firstMode ≤ k := by
  simp only [modeIds,List.mem_filterMap]
  constructor
  · rintro ⟨v,hv,he⟩
    cases v with
    | rigid => cases he
    | flex j =>
      change (if p.firstMode ≤ j then some j else none) = some k at he
      split at he <;> try contradiction
      cases he
      exact ⟨hv,by assumption⟩
  · rintro ⟨hv,hk⟩
    exact ⟨.flex k,hv,by simp [hk]⟩

theorem fixed_mem_retained {p : SchemePreparation.Prepared} {n : Nat} {v : ModVar}
    (hv : v ∈ fixedNames p) : v ∈ modeNames p n := by
  apply (ComparisonObserverBoundary.mem_retainedModes _ _ _).mpr
  apply Finset.mem_union_right
  apply ComparisonObserverBoundary.modes_subset (a :=
    (imageBasis p (n + ComparisonRankedDecision.endpointRank
      (ComparisonSignedObservation.endpoints p))).term (.control (.locality v true)))
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨.control (.locality v true),List.mem_append_right _ ?_,rfl⟩
    apply List.mem_map.mpr
    refine ⟨.locality v true,List.mem_flatMap.mpr ⟨v,?_,by simp [controls]⟩,rfl⟩
    simpa only [imageBasis,basis_modes] using hv
  · simp [Basis.term,ComparisonObserverBoundary.modes,control_vars,Control.name]

theorem assumptions_fixed {ambient : Bounds} {source target : Scheme} {v : ModVar}
    (hv : v ∈ (SchemePreparation.prepare ambient source target).assumptions.modVars) :
    v ∈ fixedNames (SchemePreparation.prepare ambient source target) := by
  apply mem_fixedNames.mpr
  constructor
  · apply (mem_inputModes _ _).mpr
    simp only [ComparisonWitnessRestriction.inputModes,Finset.mem_union]
    tauto
  · exact ((Bounds.bounded_iff _ _ _).mp
      (SchemePreparation.prepare_assumptions_bounded_first ambient source target)).2 v hv

theorem retained_mem_fixed {ambient : Bounds} {source target : Scheme} {n : Nat} {v : ModVar}
    (hv : v ∈ modeNames (SchemePreparation.prepare ambient source target) n) :
    v ∈ fixedNames (SchemePreparation.prepare ambient source target) := by
  let p := SchemePreparation.prepare ambient source target
  rcases Finset.mem_union.mp ((ComparisonObserverBoundary.mem_retainedModes _ _ _).mp hv) with
    hdecl | hgen
  · exact assumptions_fixed hdecl
  obtain ⟨a,ha,hva⟩ := (ComparisonObserverBoundary.mem_allModes _ _).mp hgen
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨c,hc,ha⟩ := List.mem_flatMap.mp ha
    cases c <;> simp only [List.not_mem_nil] at ha
    case sub left right =>
      have hm : left.modVars ∪ right.modVars ⊆ p.assumptions.modVars := by
        intro v hv
        exact (p.assumptions.mem_modVars_iff v).mpr ⟨.sub left right,hc,hv⟩
      rcases List.mem_cons.mp ha with rfl | ha
      · apply assumptions_fixed
        exact hm (Finset.mem_union_left _ ((ComparisonObserverBoundary.support_iff _).mp
          ((ComparisonStructuralEndpoints.ofTy_supported left (fun _ _ => trivial)
            (fun _ hv => hv))) _ hva))
      · have he : a = .ofTy right := by simpa using ha
        subst a
        apply assumptions_fixed
        exact hm (Finset.mem_union_right _ ((ComparisonObserverBoundary.support_iff _).mp
          ((ComparisonStructuralEndpoints.ofTy_supported right (fun _ _ => trivial)
            (fun _ hv => hv))) _ hva))
  · exact (ComparisonObserverBoundary.support_iff _).mp
      ((types_support (inputNames p) (fixedNames p)
        (n + ComparisonRankedDecision.endpointRank (ComparisonSignedObservation.endpoints p))
        a ha).mono (fun _ _ => trivial) (fun _ h => h)) v hva

theorem input_extended {ambient : Bounds} {source target : Scheme} {n : Nat} {v : ModVar}
    (hv : v ∈ inputModes (SchemePreparation.prepare ambient source target)) :
    v ∈ ComparisonRankedModes.extended
      (modeNames (SchemePreparation.prepare ambient source target) n)
      (modeIds (SchemePreparation.prepare ambient source target)) := by
  let p := SchemePreparation.prepare ambient source target
  by_cases hlo : v.index < p.firstMode
  · exact List.mem_append_left _ (fixed_mem_retained (mem_fixedNames.mpr ⟨hv,hlo⟩))
  have hsrc : v ∈ p.sourceBounds.modVars ∪ p.sourceType.modVars := by
    have hi := (mem_inputModes p v).mp hv
    simp only [ComparisonWitnessRestriction.inputModes,Finset.mem_union] at hi
    rcases hi with ((ha | hb) | hc) | ht
    · exact False.elim (hlo (((Bounds.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_assumptions_bounded_first ambient source target)).2 v ha))
    · exact Finset.mem_union_left _ hb
    · exact Finset.mem_union_right _ hc
    · exact False.elim (hlo (((TypeExpr.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_targetType_bounded_first ambient source target)).2 v ht))
  have hrigid := ComparisonFixedModeWitness.prepared_rigidScoped ambient source target v hsrc
  apply List.mem_append_right
  cases v with
  | rigid k => exact False.elim (hlo hrigid)
  | flex k =>
    exact List.mem_map.mpr ⟨k,mem_modeIds.mpr ⟨hv,Nat.le_of_not_gt hlo⟩,rfl⟩

theorem project_keys {ambient : Bounds} {source target : Scheme} {k : Nat} :
    k ∈ ComparisonFixedModeWitness.keys
      (SchemePreparation.prepare ambient source target).firstMode
      (SchemePreparation.prepare ambient source target).sourceBounds
      (SchemePreparation.prepare ambient source target).sourceType ↔
    k ∈ modeIds (SchemePreparation.prepare ambient source target) := by
  let p := SchemePreparation.prepare ambient source target
  rw [ComparisonFixedModeWitness.mem_keys,mem_modeIds]
  constructor
  · rintro ⟨hl,hsrc⟩
    refine ⟨(mem_inputModes p _).mpr ?_,hl⟩
    simp only [ComparisonFixedModeWitness.inputModes,Finset.mem_union] at hsrc
    simp only [ComparisonWitnessRestriction.inputModes,Finset.mem_union]
    tauto
  · rintro ⟨hi,hl⟩
    refine ⟨hl,?_⟩
    have hi := (mem_inputModes p _).mp hi
    simp only [ComparisonWitnessRestriction.inputModes,Finset.mem_union] at hi
    rcases hi with ((ha | hb) | hc) | ht
    · have hlt := ((Bounds.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_assumptions_bounded_first ambient source target)).2 (.flex k) ha
      exact False.elim (Nat.not_lt_of_ge hl hlt)
    · exact Finset.mem_union_left _ hb
    · exact Finset.mem_union_right _ hc
    · have hlt := ((TypeExpr.bounded_iff _ _ _).mp
        (SchemePreparation.prepare_targetType_bounded_first ambient source target)).2 (.flex k) ht
      exact False.elim (Nat.not_lt_of_ge hl hlt)

theorem names_disjoint {ambient : Bounds} {source target : Scheme} {n : Nat} :
    ∀ v ∈ modeNames (SchemePreparation.prepare ambient source target) n,
      ∀ k ∈ modeIds (SchemePreparation.prepare ambient source target), v ≠ .flex k := by
  intro v hv k hk he
  have hl := (mem_fixedNames.mp (retained_mem_fixed hv)).2
  have hu := (mem_modeIds.mp hk).2
  subst v
  exact Nat.not_lt_of_ge hu hl

theorem endpoint_modes {ambient : Bounds} {source target : Scheme} {n : Nat} :
    let p := SchemePreparation.prepare ambient source target
    ∀ pair ∈ ComparisonSignedObservation.endpoints p,
      (∀ v ∈ pair.1.modVars, v ∈ ComparisonRankedModes.extended (modeNames p n) (modeIds p)) ∧
      (∀ v ∈ pair.2.modVars, v ∈ ComparisonRankedModes.extended (modeNames p n) (modeIds p)) := by
  intro p pair hp
  exact ⟨fun v hv => input_extended ((mem_inputModes p v).mpr
    ((ComparisonSignedObservation.endpoints_input hp).2.2.1 hv)),
    fun v hv => input_extended ((mem_inputModes p v).mpr
      ((ComparisonSignedObservation.endpoints_input hp).2.2.2 hv))⟩

theorem scalar_assembled {ambient : Bounds} {source target : Scheme} {fuel n : Nat}
    {scalar : ComparisonGuardedEndpointQueries.Source}
    {q : ComparisonSignedEndpointQueries.Source}
    {solution : ComparisonSignedQuerySolver.Solution} {assembled : Substitution}
    (hscalar : ComparisonPreparedScalar.run fuel (SchemePreparation.prepare ambient source target) =
      .success scalar)
    (hp : ComparisonRankedModes.prepare fuel
      (SchemePreparation.prepare ambient source target).assumptions
      (inputTypeKeys (SchemePreparation.prepare ambient source target))
      (typeNames (SchemePreparation.prepare ambient source target) n)
      (modeNames (SchemePreparation.prepare ambient source target) n)
      (modeIds (SchemePreparation.prepare ambient source target))
      (count (SchemePreparation.prepare ambient source target) n)
      (imageBasis (SchemePreparation.prepare ambient source target) n)
      (ComparisonSignedObservation.endpoints (SchemePreparation.prepare ambient source target)) =
        .success q)
    (hr : ComparisonSignedEndpointQueries.run fuel
      (ComparisonRankedModes.input (inputTypeKeys (SchemePreparation.prepare ambient source target))
        (imageBasis (SchemePreparation.prepare ambient source target) n))
      ModalSynthesis.locality (SchemeModeSynthesis.atoms
        (modeIds (SchemePreparation.prepare ambient source target))) [q,scalar.source] = .success solution)
    (ha : ComparisonRankedModes.assemble
      (modeNames (SchemePreparation.prepare ambient source target) n)
      (modeIds (SchemePreparation.prepare ambient source target))
      (ComparisonRankedModes.input (inputTypeKeys (SchemePreparation.prepare ambient source target))
        (imageBasis (SchemePreparation.prepare ambient source target) n))
      [q,scalar.source] (CNFPropagation.valuation solution.selectors) = some assembled) :
    EntailsAll (SchemePreparation.prepare ambient source target).assumptions
      ((ComparisonPreparedScalar.required (SchemePreparation.prepare ambient source target)).map
        (Constraint.subst TypeExpr.var assembled.mode)) := by
  let p := SchemePreparation.prepare ambient source target
  obtain ⟨_,r,_,_,_,_,_,hv⟩ := ComparisonSignedEndpointQueries.run_sound
    (by simpa [ComparisonRankedModes.input] using
      (And.intro (ComparisonRankedModes.prepare_allowed hp)
        (ComparisonPreparedScalar.run_allowed hscalar (inputTypeKeys p)))) hr
  have hvalid := (ComparisonPreparedScalar.run_valid hscalar
    (fun _ => (imageBasis p n).types.length) (fun _ => false) _ _).mp
      (fun _ => hv scalar.source (by simp))
  have hproject := ComparisonJointAssemblyReification.projected_scalar_guards ha
    (fun v hvar => ⟨fixed_mem_retained (assumptions_fixed hvar),fun axis haxis hmem => by
      obtain ⟨k,hk,he⟩ := (SchemeModeSynthesis.mem_atoms_iff haxis).mp hmem
      exact names_disjoint (n := n) _ (fixed_mem_retained (assumptions_fixed hvar)) _ hk he⟩)
    (fun v hv => by
      have he := input_extended (n := n) (ComparisonPreparedScalar.required_input hv)
      rcases List.mem_append.mp he with he | he
      · exact .inl he
      · obtain ⟨k,hk,he⟩ := List.mem_map.mp he
        exact .inr ⟨k,hk,he.symm⟩) hvalid
  apply (ComparisonPreparedScalar.required_entails_iff _ _ _).mpr
  intro η hη c hc
  obtain ⟨original,ho,rfl⟩ := List.mem_map.mp hc
  have hkind := ComparisonPreparedScalar.required_scalar p ho
  have he := hproject η hη _ (List.mem_map.mpr ⟨original,ho,rfl⟩)
  cases original <;> try contradiction
  · exact he
  · exact he

private theorem supports_inter {P : TypeVar → Prop} {Q R : ModVar → Prop} {a : CompareTy}
    (h : Supports P Q a) (h' : Supports (fun _ => True) R a) :
    Supports P (fun v => Q v ∧ R v) a := by
  induction a <;> simp_all [Supports]

theorem normalize_fixed {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models p.assumptions ρ)
    (hw : PreparedWitnessUnder p σ)
    (hs : ComparisonWitnessRestriction.Supported p σ)
    (hf : ComparisonFixedModeWitness.FixedImages p.firstMode σ) :
    ∃ n τ, PreparedWitnessUnder p τ ∧ τ.modes = σ.modes ∧
      ComparisonWitnessRestriction.Supported p τ ∧
      ∀ v ∈ ComparisonWitnessRestriction.inputTypes p,
        LatticeForm (imageBasis p n).types (τ.type v) := by
  classical
  let n := (ComparisonWitnessRestriction.inputTypes p).sup (fun v => rank (σ.type v))
  have hnormal (v : TypeVar) (hv : v ∈ ComparisonWitnessRestriction.inputTypes p) :
      Normal p.assumptions (inputNames p) (fixedNames p) n (σ.type v) := by
    apply (normal_of_supported hn _ _ (hw.2.1.types v) ?_).mono
      (Finset.le_sup (f := fun v => rank (σ.type v)) hv)
    exact (supports_inter (hs.type hv) (hf.1 v)).mono
      (fun v hv => (mem_inputNames p v).mpr hv)
      (fun v hv => mem_fixedNames.mpr ⟨(mem_inputModes p v).mpr hv.1,hv.2⟩)
  have hchoose : ∀ v, ∃ a, ComparisonStructuralLattice.Equiv p.assumptions (σ.type v) a ∧
      a.DefinedUnder p.assumptions ∧
      (v ∈ ComparisonWitnessRestriction.inputTypes p →
        LatticeForm (imageBasis p n).types a) ∧
      (v ∉ ComparisonWitnessRestriction.inputTypes p → a = σ.type v) := by
    intro v
    by_cases hv : v ∈ ComparisonWitnessRestriction.inputTypes p
    · obtain ⟨a,ha,har,he⟩ := hnormal v hv
      exact ⟨a,he,har.2.1,fun _ => ha,fun h => (h hv).elim⟩
    · exact ⟨σ.type v,.refl (hw.1.2.1.type v),hw.2.1.types v,
        fun h => (hv h).elim,fun _ => rfl⟩
  choose images hi using hchoose
  let τ := ComparisonPartialCarrier.reimage σ images
  have hreplace : ComparisonStructuralBasis.Replacement p.assumptions σ τ := by
    refine ⟨?_,?_,fun v => by cases v <;> rfl⟩
    · intro v
      rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
      · exact he ▸ (hi v).1
      · change ComparisonStructuralLattice.Equiv p.assumptions (σ.type v)
          ((ComparisonPartialCarrier.reimage σ images).type v)
        rw [he.1]
        exact .refl (hw.1.2.1.type v)
    · intro v
      rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
      · exact he ▸ (hi v).2.1
      · exact he.1 ▸ hw.2.1.types v
  have hshaped : τ.WellShaped p.assumptions :=
    ComparisonPartialCarrier.reimage_wellShaped (fun v => (hi v).1.1.wellShaped_right)
  refine ⟨n,τ,hreplace.prepared rfl hw
    (ComparisonPartialCarrier.reimage_domainsAbove hw.1.1 images) hshaped,rfl,?_,?_⟩
  · refine ⟨?_,hs.2⟩
    intro entry he
    change entry ∈ (σ.types.map Prod.fst).map (fun n => (n,images (.flex n))) at he
    obtain ⟨key,hkey,rfl⟩ := List.mem_map.mp he
    by_cases hv : TypeVar.flex key ∈ ComparisonWitnessRestriction.inputTypes p
    · exact (ComparisonStructuralBasis.lattice_support ((hi (.flex key)).2.2.1 hv)
        (types_support (inputNames p) (fixedNames p) n)).mono
        (fun v hv => (mem_inputNames p v).mp hv)
        (fun v hv => (mem_inputModes p v).mp (mem_fixedNames.mp hv).1)
    · change Supports _ _ (images (.flex key))
      rw [(hi (.flex key)).2.2.2 hv]
      exact ComparisonStructuralBasis.supported_type_of_key hs hkey
  · intro v hv
    rcases ComparisonPartialCarrier.reimage_type_cases σ images v with he | he
    · change LatticeForm (imageBasis p n).types ((ComparisonPartialCarrier.reimage σ images).type v)
      rw [he]
      exact (hi v).2.2.1 hv
    · change LatticeForm (imageBasis p n).types ((ComparisonPartialCarrier.reimage σ images).type v)
      rw [he.1,he.2]
      apply LatticeForm.atom
      exact types_mono (Nat.zero_le n) (head_mem_types (by
        simp only [basis,Basis.heads,List.mem_cons,List.mem_map]
        exact .inr (.inr ⟨v,(mem_inputNames p v).mpr hv,rfl⟩)))

theorem action_forms {p : SchemePreparation.Prepared} {n : Nat} {σ : CompareSubstitution}
    (hforms : ∀ image ∈ σ.types, LatticeForm (imageBasis p n).types image.2) :
    ∀ v ∈ inputNames p, LatticeForm (imageBasis p n).types (σ.type v) := by
  intro v hv
  have hvar : LatticeForm (imageBasis p n).types (.var v) := by
    apply LatticeForm.atom
    exact types_mono (Nat.zero_le n) (head_mem_types (by
      simp only [basis,Basis.heads,List.mem_cons,List.mem_map]
      exact .inr (.inr ⟨v,hv,rfl⟩)))
  cases v with
  | rigid => exact hvar
  | flex k =>
    cases he : σ.types.lookup k with
    | none => simpa only [CompareSubstitution.type,he,Option.getD_none] using hvar
    | some a =>
      obtain ⟨left,right,hlist,_⟩ := List.lookup_eq_some_iff.mp he
      simpa only [CompareSubstitution.type,he,Option.getD_some] using
        hforms (k,a) (by simp [hlist])

theorem machine_prepared {ambient : Bounds} {source target : Scheme}
    {n : Nat} {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (hkeys : σ.types.map Prod.fst = inputTypeKeys (SchemePreparation.prepare ambient source target))
    (hforms : ∀ image ∈ σ.types,
      LatticeForm (imageBasis (SchemePreparation.prepare ambient source target) n).types image.2)
    (hmodeKeys : ∀ entry ∈ σ.modes,
      entry.1 ∈ modeIds (SchemePreparation.prepare ambient source target))
    (htotal : ∀ v, Entails
      (SchemePreparation.prepare ambient source target).assumptions (.defined (σ.mode v)))
    (hmodes : ∀ v ∈ inputModes (SchemePreparation.prepare ambient source target),
      ∀ w ∈ (σ.mode v).vars, w ∈ fixedNames (SchemePreparation.prepare ambient source target))
    (hscalar : EntailsAll (SchemePreparation.prepare ambient source target).assumptions
      ((ComparisonPreparedScalar.required (SchemePreparation.prepare ambient source target)).map
        (Constraint.subst TypeExpr.var σ.mode)))
    (hmachine : ComparisonRankedDecision.MachineValid
      (SchemePreparation.prepare ambient source target).assumptions
      (inputTypeKeys (SchemePreparation.prepare ambient source target))
      (typeNames (SchemePreparation.prepare ambient source target) n)
      (modeNames (SchemePreparation.prepare ambient source target) n)
      (count (SchemePreparation.prepare ambient source target) n) σ.mode
      (ComparisonSignedObservation.endpoints (SchemePreparation.prepare ambient source target))
      (ComparisonRankedDecision.selected σ.types)) :
    PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ := by
  let p := SchemePreparation.prepare ambient source target
  have hreps : ∀ image ∈ σ.types, Representable p.assumptions .unit image.2 :=
    fun image hi => (hforms image hi).representable
      (types_representable hn (inputNames p) (fixedNames p) n)
  have hdefined : σ.WellFormedUnder p.assumptions :=
    ⟨(CompareSubstitution.wellFormedUnder_of_images
      (σ := {types := σ.types}) (fun image hi => (hreps image hi).2.1) (by simp)).types,htotal⟩
  have hinst : ∀ a, ComparisonRankedDecision.instantiate (inputTypeKeys p)
      (ComparisonRankedDecision.selected σ.types) σ.mode a = σ.ty a := by
    intro a
    have ht := ComparisonRankedPrepared.selected_type (modes := σ.modes) hkeys
    simpa only [ComparisonRankedDecision.instantiate,CompareSubstitution.ty] using
      congrArg (fun ts => (CompareTy.ofTy a).subst ts σ.mode) ht
  have hformsAll := action_forms hforms
  have hsupport : ∀ pair ∈ ComparisonSignedObservation.endpoints p,
      Supports (· ∈ inputNames p) (· ∈ fixedNames p) (σ.ty pair.1) ∧
      Supports (· ∈ inputNames p) (· ∈ fixedNames p) (σ.ty pair.2) := by
    intro pair hp
    have hpair := ComparisonRankedPrepared.endpoint_support p pair hp
    exact ⟨hpair.1.subst
      (fun v hv => ComparisonStructuralBasis.lattice_support (hformsAll v hv)
        (types_support (inputNames p) (fixedNames p) n)) hmodes,
      hpair.2.subst
      (fun v hv => ComparisonStructuralBasis.lattice_support (hformsAll v hv)
        (types_support (inputNames p) (fixedNames p) n)) hmodes⟩
  have hpair (pair : Ty × Ty) (hp : pair ∈ ComparisonSignedObservation.endpoints p) :
      AlgebraSubtype p.assumptions (σ.ty pair.1) (σ.ty pair.2) := by
    have hg := ComparisonPreparedScalar.endpoint_guards hscalar hp
    have hl := ComparisonSignedClosedAlignment.defined_of_annotations hdefined.types pair.1
      (hg _ (by simp))
    have hr := ComparisonSignedClosedAlignment.defined_of_annotations hdefined.types pair.2
      (hg _ (by simp))
    have hnames := ComparisonSignedObservation.endpoints_input hp
    have hleft := (rank_ty σ pair.1 n (fun v hv => lattice_rank
      (hformsAll v ((mem_inputNames p v).mpr (hnames.1 hv))))).trans
        (Nat.add_le_add_left (ComparisonRankedDecision.endpointRank_bounds hp).1 n)
    have hright := (rank_ty σ pair.2 n (fun v hv => lattice_rank
      (hformsAll v ((mem_inputNames p v).mpr (hnames.2.1 hv))))).trans
        (Nat.add_le_add_left (ComparisonRankedDecision.endpointRank_bounds hp).2 n)
    apply (ComparisonRankedObservers.subtype_iff_machines hn hΔ (inputNames p) (fixedNames p)
      (n + ComparisonRankedDecision.endpointRank (ComparisonSignedObservation.endpoints p))
      hl hr (hsupport pair hp).1 (hsupport pair hp).2 hleft hright).mpr
    intro data hc i
    have hvalid := (ComparisonRankedDecision.machineValid_iff_machines
      p.assumptions (inputTypeKeys p) (typeNames p n) (modeNames p n) (count p n)
      σ.mode (ComparisonSignedObservation.endpoints p)
      (ComparisonRankedDecision.selected σ.types)).mp hmachine
    simpa only [hinst] using hvalid data hc pair hp i
  apply ComparisonPreparedWitness.prepared_of_endpoints
  · refine ⟨?_,fun entry he => (mem_modeIds.mp (hmodeKeys entry he)).2⟩
    intro image hi
    exact ((mem_inputTypeKeys p image.1).mp
      (hkeys ▸ List.mem_map.mpr ⟨image,hi,rfl⟩)).2
  · exact fun image hi => (hreps image hi).1
  · exact hdefined
  · exact hscalar
  · exact fun pair hp => hpair pair (List.mem_append_right _ hp)

theorem prepared_complete {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    ∃ n threshold result, ∀ fuel ≥ threshold,
      run fuel (SchemePreparation.prepare ambient source target) n = .success result := by
  let p := SchemePreparation.prepare ambient source target
  obtain ⟨σ',hσ',_,_,hsp⟩ := ComparisonWitnessRestriction.prepared_supported_under hw
  let core := ComparisonFixedModeWitness.project p.firstMode p.sourceBounds p.sourceType σ'
  have hcore := ComparisonFixedModeWitness.prepared_project hσ'
  obtain ⟨n,τ,hτ,hmodes,hs,hi⟩ := normalize_fixed hn hcore.1
    (ComparisonFixedModeWitness.project_supported hsp) hcore.2
  change τ.modes = core.modes at hmodes
  have heq : τ.mode = core.mode := by
    funext v
    cases v <;> simp only [CompareSubstitution.mode,hmodes]
  have hfixed : ∀ v ∈ modeNames p n, τ.mode v = .var v := by
    intro v hv
    exact hτ.1.1.mode_fixed v (mem_fixedNames.mp (retained_mem_fixed hv)).2
  have hdomain : ∀ v, (∀ k ∈ modeIds p, v ≠ .flex k) → τ.mode v = .var v := by
    intro v hv
    rw [heq]
    cases v with
    | rigid => rfl
    | flex k =>
      have hk : k ∉ ComparisonFixedModeWitness.keys p.firstMode p.sourceBounds p.sourceType :=
        fun hk => hv k (project_keys.mp hk) rfl
      have hl : core.modes.lookup k = none := by
        apply List.lookup_eq_none_iff.mpr
        intro entry he
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp he
        exact bne_iff_ne.mpr (fun h => hk (h ▸ hj))
      simp only [CompareSubstitution.mode,hl,Option.getD_none]
  have himages : ∀ v ∈ ComparisonRankedModes.extended (modeNames p n) (modeIds p),
      ∀ w ∈ (τ.mode v).vars, w ∈ modeNames p n := by
    intro v hv w hw
    rcases List.mem_append.mp hv with hv | hv
    · simp only [hfixed v hv,ModExpr.vars,Finset.mem_singleton] at hw
      exact hw ▸ hv
    · obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hv
      have hi := hs.mode ((mem_inputModes p _).mp (mem_modeIds.mp hk).1) hw
      have hm : (τ.mode (.flex k)) =
          (σ'.mode (.flex k)).subst
            (ComparisonModeRestriction.restrict (ComparisonFixedModeWitness.names p.firstMode)) := by
        rw [heq]
        exact ComparisonFixedModeWitness.project_mode_at σ' (project_keys.mpr hk)
      rw [hm] at hw
      have hl := (ComparisonFixedModeWitness.mem_names w p.firstMode).mp
        (ComparisonModeRestriction.restrict_support _ _ w hw)
      exact fixed_mem_retained (mem_fixedNames.mpr ⟨(mem_inputModes p w).mpr hi,hl⟩)
  obtain ⟨scalarFuel,scalar,hscalar⟩ := ComparisonPreparedScalar.run_complete p
  have hscalarAt := hscalar scalarFuel le_rfl
  have scalarValid (family : Nat → (Nat → Bool) → Bool) :
      scalar.source.Valid (fun _ => (imageBasis p n).types.length) family
        (SchemeModeSynthesis.strategy τ.mode) := by
    have hvalid := (ComparisonPreparedScalar.run_valid_entails hscalarAt
      (fun _ => (imageBasis p n).types.length) (fun _ => false) family
      (ComparisonPreparedScalar.prepared_fixed hτ)).mpr
      (ComparisonRankedPrepared.prepared_required hτ hs hΔ)
    apply hvalid
    obtain ⟨_,_,_,_,he⟩ := ComparisonPreparedScalar.run_spec hscalarAt
    simp [he,ComparisonPreparedScalar.source,ClauseHolds]
  obtain ⟨jointFuel,result,hjoint⟩ := ComparisonRankedModes.run_complete p.assumptions
    (inputTypeKeys p) (typeNames p n) (modeNames p n) (modeIds p) (count p n)
    (imageBasis p n) (ComparisonSignedObservation.endpoints p) [scalar.source] hΔ
    τ.mode (fun k => τ.type (.flex k))
    (fun k hk => hi (.flex k) ((mem_inputNames p _).mp ((mem_inputTypeKeys p k).mp hk).1))
    hfixed hdomain
    (fun _ hv => fixed_mem_retained (assumptions_fixed hv)) himages
    (fun η hη v => hτ.2.1.modes v η hη)
    (fun pair hp => ⟨fun v hv => input_extended ((mem_inputModes p v).mpr
        ((ComparisonSignedObservation.endpoints_input hp).2.2.1 hv)),
      fun v hv => input_extended ((mem_inputModes p v).mpr
        ((ComparisonSignedObservation.endpoints_input hp).2.2.2 hv))⟩)
    (fun pair hp => let hh := ComparisonRankedDecision.prepared_witness_endpoints hτ hs hΔ pair hp
      ⟨hh.2.1,hh.2.2,hh.1⟩)
    (by simpa using ComparisonPreparedScalar.run_binary hscalarAt)
    (by simpa using ComparisonPreparedScalar.run_allowed hscalarAt (inputTypeKeys p))
    (fun family _ => by simpa using scalarValid family)
  refine ⟨n,max scalarFuel jointFuel,result,?_⟩
  intro fuel hf
  change run fuel p n = _
  simp only [run,hscalar fuel ((Nat.le_max_left _ _).trans hf),bind,RunResult.bind]
  exact hjoint fuel ((Nat.le_max_right _ _).trans hf)

theorem synthesize_spec {fuel p n result} (h : synthesize fuel p n = .success result) :
    ∃ scalar, ComparisonPreparedScalar.run fuel p = .success scalar ∧
      ComparisonRankedModes.synthesize fuel p.assumptions (inputTypeKeys p)
        (typeNames p n) (modeNames p n) (modeIds p) (count p n) (imageBasis p n)
        (ComparisonSignedObservation.endpoints p) [scalar.source] = .success result := by
  cases hs : ComparisonPreparedScalar.run fuel p <;>
    simp [synthesize,hs,bind,RunResult.bind] at h
  exact ⟨_,rfl,h⟩

theorem synthesize_sound {ambient : Bounds} {source target : Scheme}
    {fuel n : Nat} {result : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (h : synthesize fuel (SchemePreparation.prepare ambient source target) n = .success result) :
    PreparedWitnessUnder (SchemePreparation.prepare ambient source target) result := by
  let p := SchemePreparation.prepare ambient source target
  obtain ⟨scalar,hscalar,hr⟩ := synthesize_spec h
  have hallowed : ∀ s ∈ [scalar.source], s.Allowed (inputTypeKeys p) := by
    simpa using ComparisonPreparedScalar.run_allowed hscalar (inputTypeKeys p)
  obtain ⟨hkeys,hforms,hmachine⟩ := ComparisonRankedModes.synthesize_sound hr hallowed
    names_disjoint (fun _ hv => fixed_mem_retained (assumptions_fixed hv)) endpoint_modes
  obtain ⟨hmodeKeys,htotal,_,hmodeSupport⟩ := ComparisonRankedModes.synthesize_modes hr
  have hscalarOriginal : EntailsAll p.assumptions
      ((ComparisonPreparedScalar.required p).map (Constraint.subst TypeExpr.var result.mode)) := by
    obtain ⟨q,solution,assembled,hp,hs,ha,rfl⟩ := ComparisonRankedModes.synthesize_spec hr
    exact scalar_assembled hscalar hp hs ha
  apply machine_prepared hn hΔ hkeys hforms
  · intro entry he
    exact hmodeKeys ▸ List.mem_map.mpr ⟨entry,he,rfl⟩
  · exact fun v η _ => htotal η v
  · exact fun v hv w hw => retained_mem_fixed (hmodeSupport v (input_extended hv) w hw)
  · exact hscalarOriginal
  · exact hmachine

theorem synthesize_complete {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    ∃ n threshold result, ∀ fuel ≥ threshold,
      synthesize fuel (SchemePreparation.prepare ambient source target) n = .success result := by
  let p := SchemePreparation.prepare ambient source target
  obtain ⟨n,threshold,raw,hraw⟩ := prepared_complete hn hΔ hw
  obtain ⟨scalarFuel,scalar,hscalar⟩ := ComparisonPreparedScalar.run_complete p
  have hrawCore : ∃ threshold result, ∀ fuel ≥ threshold,
      ComparisonRankedModes.run fuel p.assumptions (inputTypeKeys p)
        (typeNames p n) (modeNames p n) (modeIds p) (count p n) (imageBasis p n)
        (ComparisonSignedObservation.endpoints p) [scalar.source] = .success result := by
    refine ⟨max threshold scalarFuel,raw,?_⟩
    intro fuel hf
    have hh := hraw fuel ((Nat.le_max_left _ _).trans hf)
    change run fuel p n = _ at hh
    simpa only [run,hscalar fuel ((Nat.le_max_right _ _).trans hf),bind,RunResult.bind] using hh
  obtain ⟨jointFuel,result,hjoint⟩ := ComparisonRankedModes.synthesize_eventual hrawCore
  refine ⟨n,max scalarFuel jointFuel,result,?_⟩
  intro fuel hf
  change synthesize fuel p n = _
  simp only [synthesize,hscalar fuel ((Nat.le_max_left _ _).trans hf),bind,RunResult.bind]
  exact hjoint fuel ((Nat.le_max_right _ _).trans hf)

theorem synthesize_success_iff {ambient : Bounds} {source target : Scheme}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    (∃ n fuel result,
      synthesize fuel (SchemePreparation.prepare ambient source target) n = .success result) ↔
      ∃ σ, PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ := by
  constructor
  · rintro ⟨n,fuel,result,h⟩
    exact ⟨result,synthesize_sound hn hΔ h⟩
  · rintro ⟨σ,hw⟩
    obtain ⟨n,threshold,result,h⟩ := synthesize_complete hn hΔ hw
    exact ⟨n,threshold,result,h threshold le_rfl⟩

theorem compare_sound {ambient : Bounds} {source target : Scheme}
    {fuel n : Nat} {result : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (h : compare fuel ambient source target n = .success result) :
    let p := SchemePreparation.prepare ambient source target
    CompareInstantiatesUnder p.assumptions source result ∧ result.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (result.bounds source.bounds) ∧
      AlgebraSubtype p.assumptions (result.ty source.body) (.ofTy p.targetType) := by
  cases hr : synthesize fuel (SchemePreparation.prepare ambient source target) n with
  | rejected _ => simp [compare,hr,bind,RunResult.bind] at h
  | exhausted => simp [compare,hr,bind,RunResult.bind] at h
  | success action =>
    simp only [compare,hr,bind,RunResult.bind,pure,RunResult.success.injEq] at h
    subst result
    exact ComparisonPreparedDriver.reconstruct_result (synthesize_sound hn hΔ hr)

theorem compare_complete {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (hw : PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ) :
    ∃ n threshold result, ∀ fuel ≥ threshold,
      compare fuel ambient source target n = .success result := by
  obtain ⟨n,threshold,result,h⟩ := synthesize_complete hn hΔ hw
  exact ⟨n,threshold,ComparisonPreparation.reconstruct
    (SchemePreparation.prepare ambient source target) result,
    fun fuel hf => by simp only [compare,h fuel hf,bind,RunResult.bind,pure]⟩

end ModalityInference.ComparisonRankedJoint
