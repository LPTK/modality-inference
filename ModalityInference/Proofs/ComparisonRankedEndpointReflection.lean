import ModalityInference.ComparisonRankedDecision
import ModalityInference.Proofs.ComparisonRankedObservers
import ModalityInference.Proofs.ComparisonRankedSubstitution
import ModalityInference.Proofs.ComparisonRankedDecision
import ModalityInference.Proofs.ComparisonRankedWitness
import ModalityInference.Proofs.ComparisonSignedPreparedEndpoints
import Mathlib.Data.List.MinMax

/-! Fixed-rank observer reflection for the original public endpoint templates.
One finite image family and one modality action are shared by every occurrence.
The machine bound depends on the rank and written templates, while endpoint
guards must hold under the original assumptions. -/
namespace ModalityInference.ComparisonRankedDecision

open ComparisonAlgebra ComparisonControls ComparisonInterpolation
  ComparisonRankedBasis ComparisonObserverBoundary ComparisonObserverMachine
  ComparisonObserverMachineCheck ComparisonObserverMachineSerialization
  ComparisonStructuralLattice

theorem imageTypes_rank (keys : List Nat) (images : Nat → CompareTy) (n : Nat)
    (hi : ∀ k ∈ keys, rank (images k) ≤ n) (v : TypeVar) :
    rank (imageTypes keys images v) ≤ n := by
  cases v with
  | rigid => exact Nat.zero_le _
  | flex k => by_cases hk : k ∈ keys <;> simp [imageTypes, hk, rank, hi k]

theorem instantiate_rank {keys : List Nat} {images : Nat → CompareTy}
    {types : List TypeVar} {names : List ModVar} {n : Nat}
    (hi : ∀ k ∈ keys, LatticeForm (basis types names n).types (images k))
    (modes : ModVar → ModExpr) (a : Ty) :
    rank (instantiate keys images modes a) ≤ n + rank (.ofTy a) :=
  rank_subst_ofTy (imageTypes keys images) modes a n
    (fun v _ => imageTypes_rank keys images n (fun k hk => lattice_rank (hi k hk)) v)

theorem imageTypes_support {keys : List Nat} {images : Nat → CompareTy}
    {types : List TypeVar} {names : List ModVar} {n : Nat}
    (hi : ∀ k ∈ keys, LatticeForm (basis types names n).types (images k))
    {v : TypeVar} (hv : v ∈ types) :
    Supports (· ∈ types) (· ∈ names) (imageTypes keys images v) := by
  cases v with
  | rigid => exact hv
  | flex k =>
    by_cases hk : k ∈ keys
    · simpa only [imageTypes, List.contains_iff_mem.mpr hk, if_true] using
        ComparisonStructuralBasis.lattice_support (hi k hk) (types_support types names n)
    · simpa [imageTypes, hk] using hv

theorem instantiate_support {keys : List Nat} {images : Nat → CompareTy}
    {types : List TypeVar} {names : List ModVar} {n : Nat}
    (hi : ∀ k ∈ keys, LatticeForm (basis types names n).types (images k))
    {modes : ModVar → ModExpr}
    (hm : ∀ v ∈ names, ∀ w ∈ (modes v).vars, w ∈ names)
    {a : Ty} (ha : Supports (· ∈ types) (· ∈ names) (.ofTy a)) :
    Supports (· ∈ types) (· ∈ names) (instantiate keys images modes a) :=
  ha.subst (fun _ hv => imageTypes_support hi hv) hm

theorem endpointRank_bounds {endpoints : List (Ty × Ty)} {pair : Ty × Ty}
    (hp : pair ∈ endpoints) :
    rank (.ofTy pair.1) ≤ endpointRank endpoints ∧
      rank (.ofTy pair.2) ≤ endpointRank endpoints := by
  have hmax : max (rank (.ofTy pair.1)) (rank (.ofTy pair.2)) ≤ endpointRank endpoints :=
    List.le_max_of_le (List.mem_map.mpr ⟨pair, hp, rfl⟩) le_rfl
  exact ⟨(le_max_left _ _).trans hmax, (le_max_right _ _).trans hmax⟩

/-- Fixed-rank synthesis may use one machine size for the entire endpoint
family. The finite polynomials may have arbitrary lattice size, and every
occurrence is evaluated using the same image and modality functions. -/
theorem endpoints_iff_machines {Δ : Bounds}
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (typeNames : List TypeVar) (modeNames : List ModVar) (n : Nat)
    (keys : List Nat) (images : Nat → CompareTy) (modes : ModVar → ModExpr)
    (endpoints : List (Ty × Ty))
    (hi : ∀ k ∈ keys, LatticeForm (basis typeNames modeNames n).types (images k))
    (hm : ∀ v ∈ modeNames, ∀ w ∈ (modes v).vars, w ∈ modeNames)
    (he : ∀ pair ∈ endpoints,
      Supports (· ∈ typeNames) (· ∈ modeNames) (.ofTy pair.1) ∧
      Supports (· ∈ typeNames) (· ∈ modeNames) (.ofTy pair.2))
    (hd : ∀ pair ∈ endpoints,
      (instantiate keys images modes pair.1).DefinedUnder Δ ∧
      (instantiate keys images modes pair.2).DefinedUnder Δ) :
    let generators := (basis typeNames modeNames (n + endpointRank endpoints)).types
    let types := retainedTypes Δ generators
    let names := retainedModes Δ generators
    let count := sizeBound Δ generators
    (∀ pair ∈ endpoints, AlgebraSubtype Δ
      (instantiate keys images modes pair.1) (instantiate keys images modes pair.2)) ↔
      ∀ data : Fin count → Description (Fin count), check Δ types names data = true →
        ∀ pair ∈ endpoints, ∀ i,
          value (nodes types names data) (instantiate keys images modes pair.1) i ≤
          value (nodes types names data) (instantiate keys images modes pair.2) i := by
  have hpair (pair : Ty × Ty) (hp : pair ∈ endpoints) :=
    ComparisonRankedObservers.subtype_iff_machines hn hΔ typeNames modeNames
      (n + endpointRank endpoints) (hd pair hp).1 (hd pair hp).2
      (instantiate_support hi hm (he pair hp).1)
      (instantiate_support hi hm (he pair hp).2)
      ((instantiate_rank hi modes pair.1).trans
        (Nat.add_le_add_left (endpointRank_bounds hp).1 n))
      ((instantiate_rank hi modes pair.2).trans
        (Nat.add_le_add_left (endpointRank_bounds hp).2 n))
  exact ⟨fun h data hc pair hp i => (hpair pair hp).mp (h pair hp) data hc i,
    fun h pair hp => (hpair pair hp).mpr (fun data hc i => h data hc pair hp i)⟩

theorem prepared_endpoints_support (p : SchemePreparation.Prepared) :
    ∀ pair ∈ ComparisonSignedObservation.endpoints p,
      Supports (· ∈ (ComparisonWitnessRestriction.inputTypes p).toList)
        (· ∈ (ComparisonWitnessRestriction.inputModes p).toList) (.ofTy pair.1) ∧
      Supports (· ∈ (ComparisonWitnessRestriction.inputTypes p).toList)
        (· ∈ (ComparisonWitnessRestriction.inputModes p).toList) (.ofTy pair.2) := by
  intro pair hp
  have h := ComparisonSignedObservation.endpoints_input hp
  exact ⟨ComparisonStructuralEndpoints.ofTy_supported pair.1
    (fun _ hv => Finset.mem_toList.mpr (h.1 hv))
    (fun _ hv => Finset.mem_toList.mpr (h.2.2.1 hv)),
    ComparisonStructuralEndpoints.ofTy_supported pair.2
      (fun _ hv => Finset.mem_toList.mpr (h.2.1 hv))
      (fun _ hv => Finset.mem_toList.mpr (h.2.2.2 hv))⟩

theorem imageTypes_inputAction (p : SchemePreparation.Prepared) (σ : CompareSubstitution) :
    imageTypes (ComparisonSelectedBases.inputTypeKeys p) (fun n => σ.type (.flex n)) =
      (ComparisonSelectedBases.inputAction p σ).type := by
  funext v
  cases v with
  | rigid => rfl
  | flex k =>
    by_cases hk : k ∈ ComparisonSelectedBases.inputTypeKeys p
    · simp only [imageTypes, List.contains_iff_mem.mpr hk, if_true,
        ComparisonSelectedBases.inputAction, CompareSubstitution.type]
      simp only [List.lookup_graph _ hk, Option.getD_some]
    · have hf := ComparisonSignedObservation.inputAction_fixed p σ (.flex k)
        (fun n hn he => hk ((TypeVar.flex.inj he).symm ▸ hn))
      simpa [imageTypes, hk] using hf.symm

theorem instantiate_inputAction (p : SchemePreparation.Prepared)
    (σ : CompareSubstitution) (a : Ty) :
    instantiate (ComparisonSelectedBases.inputTypeKeys p) (fun n => σ.type (.flex n))
      σ.mode a = (ComparisonSelectedBases.inputAction p σ).ty a := by
  simp only [instantiate, imageTypes_inputAction, CompareSubstitution.ty]
  rfl

/-- The admissible prepared witness supplies all original endpoint guards,
including the target body's guard. No target guard is added to the context. -/
theorem prepared_witness_endpoints {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder
      (SchemePreparation.prepare ambient source target) σ)
    (hs : ComparisonWitnessRestriction.Supported
      (SchemePreparation.prepare ambient source target) σ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    let p := SchemePreparation.prepare ambient source target
    let realized := instantiate (ComparisonSelectedBases.inputTypeKeys p)
      (fun n => σ.type (.flex n)) σ.mode
    ∀ pair ∈ ComparisonSignedObservation.endpoints p,
      AlgebraSubtype p.assumptions (realized pair.1) (realized pair.2) ∧
      (realized pair.1).DefinedUnder p.assumptions ∧
      (realized pair.2).DefinedUnder p.assumptions := by
  intro p realized pair hp
  have hinput := ComparisonSelectedBases.inputAction_prepared hw
  have hg := ComparisonStructuralEndpoints.all_guarded_of_boundsDefined hinput
    (ComparisonSelectedBases.inputAction_supported hs) hΔ _
    (ComparisonSignedObservation.prepared_interpreted_mem hinput hp)
  exact (show realized pair.1 = (ComparisonSelectedBases.inputAction p σ).ty pair.1 from
    instantiate_inputAction p σ pair.1) ▸
    (show realized pair.2 = (ComparisonSelectedBases.inputAction p σ).ty pair.2 from
      instantiate_inputAction p σ pair.2) ▸
        And.intro hg.subtype ⟨hg.left_defined, hg.right_defined⟩

theorem machineValid_iff_machines (Δ : Bounds) (keys : List Nat)
    (types : List TypeVar) (names : List ModVar) (count : Nat)
    (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) (images : Nat → CompareTy) :
    MachineValid Δ keys types names count modes endpoints images ↔
      ∀ data : Fin count → Description (Fin count), check Δ types names data = true →
        ∀ pair ∈ endpoints, ∀ i,
          value (nodes types names data) (instantiate keys images modes pair.1) i ≤
          value (nodes types names data) (instantiate keys images modes pair.2) i := by
  constructor
  · intro h data hc pair hp i
    have hv := h (ComparisonObserverMachineEncoding.encode data)
      ((ComparisonObserverMachineEncoding.query_encode Δ types names data).trans hc) pair hp i
    change (ComparisonObserverMachineEncoding.observation types names count
      (instantiate keys images modes pair.1) i).eval (ComparisonObserverMachineEncoding.encode data) ≤
      (ComparisonObserverMachineEncoding.observation types names count
        (instantiate keys images modes pair.2) i).eval (ComparisonObserverMachineEncoding.encode data) at hv
    simpa only [ComparisonObserverMachineEncoding.observation_encode] using hv
  · intro h world hw pair hp i
    rw [ComparisonObserverMachineFormula.value_eval, ComparisonObserverMachineFormula.value_eval]
    exact h _ ((ComparisonObserverMachineFormula.query_eval _ _ _ _ _) ▸ hw) pair hp i

theorem endpoints_iff_machineValid {Δ : Bounds}
    (hn : ¬ ∃ ρ, ComparisonShape.Models Δ ρ) (hΔ : Δ.TypeBoundsDefined)
    (typeNames : List TypeVar) (modeNames : List ModVar) (n : Nat)
    (keys : List Nat) (images : Nat → CompareTy) (modes : ModVar → ModExpr)
    (endpoints : List (Ty × Ty))
    (hi : ∀ k ∈ keys, LatticeForm (basis typeNames modeNames n).types (images k))
    (hm : ∀ v ∈ modeNames, ∀ w ∈ (modes v).vars, w ∈ modeNames)
    (he : ∀ pair ∈ endpoints,
      Supports (· ∈ typeNames) (· ∈ modeNames) (.ofTy pair.1) ∧
      Supports (· ∈ typeNames) (· ∈ modeNames) (.ofTy pair.2))
    (hd : ∀ pair ∈ endpoints,
      (instantiate keys images modes pair.1).DefinedUnder Δ ∧
      (instantiate keys images modes pair.2).DefinedUnder Δ) :
    let generators := (basis typeNames modeNames (n + endpointRank endpoints)).types
    (∀ pair ∈ endpoints, AlgebraSubtype Δ
      (instantiate keys images modes pair.1) (instantiate keys images modes pair.2)) ↔
      MachineValid Δ keys (retainedTypes Δ generators) (retainedModes Δ generators)
        (sizeBound Δ generators) modes endpoints images :=
  (endpoints_iff_machines hn hΔ typeNames modeNames n keys images modes endpoints
    hi hm he hd).trans (machineValid_iff_machines _ _ _ _ _ _ _ _).symm

theorem machineValid_of_endpoints {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (keys : List Nat) (types : List TypeVar) (names : List ModVar) (count : Nat)
    (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) (images : Nat → CompareTy)
    (h : ∀ pair ∈ endpoints,
      AlgebraSubtype Δ (instantiate keys images modes pair.1) (instantiate keys images modes pair.2) ∧
      (instantiate keys images modes pair.1).DefinedUnder Δ ∧
      (instantiate keys images modes pair.2).DefinedUnder Δ) :
    MachineValid Δ keys types names count modes endpoints images :=
  (machineValid_iff_machines Δ keys types names count modes endpoints images).mpr
    (fun _ hc pair hp i => checked_subtype hc hΔ (h pair hp).2.1 (h pair hp).2.2 (h pair hp).1 i)

/-- An arbitrary admissible witness supplies a shared rank and mode action for
which the actual finite-rank solver eventually succeeds. The rank is derived
from the witness; this does not provide an input-only stopping bound or execute
the search for its common modality action. -/
theorem prepared_run_eventual {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (hw : ComparisonPreparation.PreparedWitnessUnder
      (SchemePreparation.prepare ambient source target) σ) :
    let p := SchemePreparation.prepare ambient source target
    let typeNames := (ComparisonWitnessRestriction.inputTypes p).toList
    let modeNames := (ComparisonWitnessRestriction.inputModes p).toList
    let endpoints := ComparisonSignedObservation.endpoints p
    let generators := fun n => (basis typeNames modeNames (n + endpointRank endpoints)).types
    ∃ n τ, ComparisonPreparation.PreparedWitnessUnder p τ ∧
      τ.types.map Prod.fst = σ.types.map Prod.fst ∧
      τ.modes.map Prod.fst = σ.modes.map Prod.fst ∧
      ∃ threshold result, ∀ fuel ≥ threshold,
        run fuel p.assumptions
          ⟨ComparisonSelectedBases.inputTypeKeys p, fun _ => (basis typeNames modeNames n).types⟩
          (retainedTypes p.assumptions (generators n))
          (retainedModes p.assumptions (generators n))
          (sizeBound p.assumptions (generators n)) τ.mode endpoints = .success result := by
  intro p typeNames modeNames endpoints generators
  obtain ⟨n, τ, hτ, ht, hm, hs, himages⟩ := prepared_ranked_complete hn hw
  have hi (k : Nat) (hk : k ∈ ComparisonSelectedBases.inputTypeKeys p) :
      LatticeForm (basis typeNames modeNames n).types (τ.type (.flex k)) :=
    (himages (.flex k) ((ComparisonSelectedBases.mem_inputNames p _).mp
      ((ComparisonSelectedBases.mem_inputTypeKeys p k).mp hk).1)).1
  have hv := machineValid_of_endpoints hΔ (ComparisonSelectedBases.inputTypeKeys p)
    (retainedTypes p.assumptions (generators n))
    (retainedModes p.assumptions (generators n))
    (sizeBound p.assumptions (generators n)) τ.mode endpoints
    (fun k => τ.type (.flex k)) (prepared_witness_endpoints hτ hs hΔ)
  obtain ⟨threshold, result, hr⟩ := run_complete p.assumptions
    (ComparisonSelectedBases.inputTypeKeys p) (fun _ => basis typeNames modeNames n)
    (retainedTypes p.assumptions (generators n))
    (retainedModes p.assumptions (generators n))
    (sizeBound p.assumptions (generators n)) τ.mode endpoints
    (fun k => τ.type (.flex k)) hi hv
  exact ⟨n, τ, hτ, ht, hm, threshold, result, hr⟩

end ModalityInference.ComparisonRankedDecision
