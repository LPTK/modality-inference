import ModalityInference.Proofs.ComparisonWindowRank
import ModalityInference.Proofs.ComparisonWindowReflection
import ModalityInference.Proofs.ComparisonRankedJoint
import ModalityInference.Proofs.ComparisonRankedJointTermination

/-! Assemble the same positive image at every occurrence of each input key.
The scalar action and every original body guard are checked against the prepared
assumptions. Positive windows reconstruct a common admissible substitution. -/
namespace ModalityInference.ComparisonWindowWitness

open ComparisonWindowPumping ComparisonWindowEndpoints ComparisonWindowObservers
  ComparisonWindowTerms ComparisonWindowReflection ComparisonSelectedBases ComparisonRankedDecision
  ComparisonRankedBasis ComparisonInterpolation ComparisonObserverMachine ComparisonStructuralLayout

private def assemble (keys : List Nat) (images : Nat → CompareTy) (σ : CompareSubstitution) :
    CompareSubstitution := { types := keys.map (fun k => (k,images k)), modes := σ.modes }

private theorem assemble_types (keys : List Nat) (images : Nat → CompareTy) (σ : CompareSubstitution) :
    (assemble keys images σ).type = imageTypes keys images := by
  funext v
  cases v with
  | rigid => rfl
  | flex k =>
    by_cases h : k ∈ keys
    · simp [assemble, CompareSubstitution.type, imageTypes, h, List.lookup_graph _ h]
    · have e : (keys.map (fun n => (n,images n))).lookup k = none := by
        apply List.lookup_eq_none_iff.mpr
        rintro entry he
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
        exact bne_iff_ne.mpr (fun hki => h (hki ▸ hi))
      simp [assemble, CompareSubstitution.type, imageTypes, h, e]

private theorem eval_image_congr {A T : Type} (s : Trees T A Constructor) (l : Fields A)
    (keys : List Nat) (modes : ModVar → ModExpr) (v w : T → Nat → Bool)
    (agree : ∀ k ∈ keys, ∀ t, v t k = w t k) (a : Ty) (t : T) :
    eval s l keys modes v a t = eval s l keys modes w a t := by
  induction a generalizing t with
  | var name =>
    cases name with
    | rigid => rfl
    | flex k => by_cases hk : k ∈ keys <;> simp [eval, hk, agree]
  | _ => simp_all [eval]

/-- All modality conditions are checked under the original prepared assumptions. -/
structure ModeObligations (p : SchemePreparation.Prepared) (ms : List (Nat × ModExpr)) : Prop where
  domain : ∀ e ∈ ms, p.firstMode ≤ e.1
  support : ∀ e ∈ ms, e.2.vars ⊆ ComparisonWitnessRestriction.inputModes p
  defined : ∀ v, Entails p.assumptions (.defined (({modes := ms} : CompareSubstitution).mode v))
  required : EntailsAll p.assumptions ((ComparisonPreparedScalar.required p).map
    (Constraint.subst TypeExpr.var ({modes := ms} : CompareSubstitution).mode))

private theorem mode_obligations {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hs : ComparisonWitnessRestriction.Supported (SchemePreparation.prepare ambient source target) σ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    ModeObligations (SchemePreparation.prepare ambient source target) σ.modes :=
  ⟨hw.1.1.2, hs.2, hw.2.1.modes, ComparisonRankedPrepared.prepared_required (σ := σ) hw hs hΔ⟩

theorem prepared_of_realizers {ambient : Bounds} {source target : Scheme}
    {σ : CompareSubstitution}
    (hn : ¬ ∃ ρ, ComparisonShape.Models
      (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (scalar : ModeObligations (SchemePreparation.prepare ambient source target) σ.modes)
    (K : Nat) :
    let p := SchemePreparation.prepare ambient source target
    let Δ := p.assumptions
    let keys := inputTypeKeys p
    let types := (ComparisonWitnessRestriction.inputTypes p).toList
    let modes := (ComparisonWitnessRestriction.inputModes p).toList
    let s := observerTrees Δ types modes
    let l := observerFields Δ types modes
    ∀ bits : Observer Δ types modes → Nat → Bool,
      (∀ a b, (a,b) ∈ ComparisonSignedObservation.endpoints p → ∀ t,
        eval s l keys σ.mode bits a t ≤ eval s l keys σ.mode bits b t) →
      (∀ k ∈ keys, ∃ a, Allowed Δ types modes a ∧ rank a ≤ K ∧
        ∀ t, value (observerNodes Δ types modes) a t = bits t k) →
      ∃ τ, ComparisonPreparation.PreparedWitnessUnder p τ ∧
        ComparisonWitnessRestriction.Supported p τ ∧
        τ.types.map Prod.fst = keys ∧ τ.modes = σ.modes ∧
        ∀ k ∈ keys, rank (τ.type (.flex k)) ≤ K ∧
          ∀ t, value (observerNodes Δ types modes) (τ.type (.flex k)) t = bits t k := by
  intro p Δ keys types modes s l bits he hreal
  let images (k : Nat) := if h : k ∈ keys then (hreal k h).choose else .unit
  have spec (k) (hk : k ∈ keys) : Allowed Δ types modes (images k) ∧ rank (images k) ≤ K ∧
      ∀ t, value (observerNodes Δ types modes) (images k) t = bits t k := by
    simpa only [images, dif_pos hk] using (hreal k hk).choose_spec
  let τ := assemble keys images σ
  have hkeys : τ.types.map Prod.fst = keys := by simp [τ, assemble, List.map_map, Function.comp_def]
  have hsel (k) (hk : k ∈ keys) : τ.type (.flex k) = images k := by
    simp only [τ, assemble_types, imageTypes, List.contains_iff_mem.mpr hk, if_true]
  have ws : ComparisonWitnessRestriction.Supported p τ := by
    refine ⟨?_, scalar.support⟩
    intro entry hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    exact (spec k hk).1.2.mono (fun _ h => Finset.mem_toList.mp h) (fun _ h => Finset.mem_toList.mp h)
  have formed : τ.WellFormedUnder Δ := by
    refine ⟨?_, scalar.defined⟩
    apply (CompareSubstitution.wellFormedUnder_of_images (σ := {types := τ.types}) ?_ (by simp)).types
    intro entry hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    exact (spec k hk).1.1
  have val_eq (a : Ty) (t : Observer Δ types modes) :
      value (observerNodes Δ types modes) (τ.ty a) t = eval s l keys σ.mode bits a t := by
    have inst : instantiate keys images σ.mode a = τ.ty a := by
      simp only [instantiate, τ, CompareSubstitution.ty, assemble_types]
      rfl
    simp only [← inst, ← eval_instantiated]
    exact eval_image_congr s l keys σ.mode _ bits (fun k hk => (spec k hk).2.2) a t
  have witnesses : ComparisonPreparation.PreparedWitnessUnder p τ := by
    apply ComparisonPreparedWitness.prepared_of_endpoints
    · refine ⟨?_, scalar.domain⟩
      intro entry he
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
      exact ((mem_inputTypeKeys p k).mp hk).2
    · exact fun entry _ => entry.2.wellShaped_of_no_models hn
    · exact formed
    · exact scalar.required
    · intro q hq
      have heq : q ∈ ComparisonSignedObservation.endpoints p := List.mem_append_right _ hq
      have guards := ComparisonPreparedScalar.endpoint_guards scalar.required heq
      have defined (a : Ty) (ha : a = q.1 ∨ a = q.2) : (τ.ty a).DefinedUnder Δ := by
        apply ComparisonSignedClosedAlignment.defined_of_annotations formed.types
        exact guards _ (by rcases ha with rfl | rfl <;> simp)
      have supportedTerm : ∀ a, Supports (· ∈ types) (· ∈ modes) (.ofTy a) →
          Supports (· ∈ types) (· ∈ modes) (τ.ty a) := by
        intro a hs
        exact hs.subst (fun _ hv => (ws.type (Finset.mem_toList.mp hv)).mono
          (fun _ h => Finset.mem_toList.mpr h) (fun _ h => Finset.mem_toList.mpr h))
          (fun _ hv _ hm => Finset.mem_toList.mpr (ws.mode (Finset.mem_toList.mp hv) hm))
      obtain ⟨sa, sb⟩ := prepared_endpoints_support p q heq
      apply (subtype_iff_observers hn hΔ types modes ?_ ?_ (defined _ (Or.inl rfl))
        (defined _ (Or.inr rfl)) (supportedTerm _ sa) (supportedTerm _ sb)).mpr
      · exact fun t => (val_eq q.1 t) ▸ (val_eq q.2 t) ▸ he q.1 q.2 heq t
      · intro v hv
        simpa only [types, Finset.toList_toFinset] using
          (show v ∈ ComparisonWitnessRestriction.inputTypes p from
            Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hv)))
      · intro v hv
        simpa only [modes, Finset.toList_toFinset] using
          (show v ∈ ComparisonWitnessRestriction.inputModes p from
            Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hv)))
  exact ⟨τ, witnesses, ws, hkeys, rfl, fun k hk => hsel k hk ▸ (spec k hk).2⟩

open ComparisonWindowRank ComparisonDefiniteTreeMachines

noncomputable abbrev typeNames (p : SchemePreparation.Prepared) := (ComparisonWitnessRestriction.inputTypes p).toList
noncomputable abbrev modeNames (p : SchemePreparation.Prepared) := (ComparisonWitnessRestriction.inputModes p).toList
abbrev States (p : SchemePreparation.Prepared) := Observer p.assumptions (typeNames p) (modeNames p)
abbrev trees (p : SchemePreparation.Prepared) := observerTrees p.assumptions (typeNames p) (modeNames p)
noncomputable abbrev fields (p : SchemePreparation.Prepared) := observerFields p.assumptions (typeNames p) (modeNames p)

/-- One common, ordered local assignment and its independently entailed mode action. -/
structure PositiveWindow (p : SchemePreparation.Prepared) (d : Nat) where
  modes : List (Nat × ModExpr)
  scalars : ModeObligations p modes
  bits : States p → Nat → Bool
  reads : (trees p).Reads d bits
  positive : ∀ k ∈ inputTypeKeys p, Positive (trees p) (fields p) p.assumptions
    (typeNames p) (modeNames p) (fun t => bits t k)
  endpoints : ∀ a b, (a,b) ∈ ComparisonSignedObservation.endpoints p → ∀ t,
    eval (trees p) (fields p) (inputTypeKeys p) ({modes := modes} : CompareSubstitution).mode bits a t ≤
    eval (trees p) (fields p) (inputTypeKeys p) ({modes := modes} : CompareSubstitution).mode bits b t

private def windowCount (letters : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => letters * (windowCount letters n)^3

private theorem card_window {A : Type} [Fintype A] (n : Nat) :
    Fintype.card (Window A Constructor n) = windowCount (Fintype.card A) n := by
  have constructors : Fintype.card Constructor = 3 := by decide
  induction n with
  | zero => exact Fintype.card_punit
  | succ n ih =>
    change Fintype.card (A × (Constructor → Window A Constructor n)) = _
    simp only [Fintype.card_prod, Fintype.card_fun, ih, constructors, windowCount]

private def letterCount (p : SchemePreparation.Prepared) : Nat :=
  2^(ComparisonWitnessRestriction.inputTypes p).card * (8^(ComparisonWitnessRestriction.inputModes p).card * 512)

private theorem card_letter (p : SchemePreparation.Prepared) :
    Fintype.card (Letter (typeNames p) (modeNames p)) = letterCount p := by
  have hMode : Fintype.card Mode = 8 := by decide
  have hCoord : Fintype.card ComparisonControls.Coordinate = 4 := by decide
  have hKinds : Fintype.card Constructor = 3 := by decide
  simp only [Letter, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe,
    typeNames, modeNames, Finset.toList_toFinset, hMode, hCoord, hKinds, letterCount]
  rfl

def rootLabelCount (p : SchemePreparation.Prepared) : Nat :=
  windowCount (letterCount p) (radius p.assumptions + 1)

/-- Compute the local-clause radius without enumerating the observer alphabet. -/
def rawRadius (p : SchemePreparation.Prepared) : Nat :=
  Trees.windowBound (rootLabelCount p) (2 ^ (written (ComparisonSignedObservation.endpoints p)).card)

theorem raw_window {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    let p := SchemePreparation.prepare ambient source target
    ∃ bits : States p → Nat → Bool, (trees p).Reads (rawRadius p) bits ∧
      ∀ a b, (a,b) ∈ ComparisonSignedObservation.endpoints p → ∀ t,
        eval (trees p) (fields p) (inputTypeKeys p) σ.mode bits a t ≤
          eval (trees p) (fields p) (inputTypeKeys p) σ.mode bits b t := by
  intro p
  have count : rootLabelCount p =
      Fintype.card (Window (Letter (typeNames p) (modeNames p)) Constructor (radius p.assumptions + 1)) := by
    simp only [card_window, card_letter, rootLabelCount]
  simpa only [rawRadius, count, observationBound, typeNames, modeNames] using prepared_window hw hΔ

def imageRank (p : SchemePreparation.Prepared) (d : Nat) : Nat :=
  pairBound (rootLabelCount p) + d

theorem PositiveWindow.witness {ambient : Bounds} {source target : Scheme}
    (hn : ¬ ∃ ρ, ComparisonShape.Models (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    {d} (w : PositiveWindow (SchemePreparation.prepare ambient source target) d) :
    let p := SchemePreparation.prepare ambient source target
    ∃ τ, ComparisonPreparation.PreparedWitnessUnder p τ ∧ ComparisonWitnessRestriction.Supported p τ ∧
      τ.types.map Prod.fst = inputTypeKeys p ∧ τ.modes = w.modes ∧
      ∀ k ∈ inputTypeKeys p, rank (τ.type (.flex k)) ≤ imageRank p d ∧
        ∀ t, value ((fields p).nodes (trees p)) (τ.type (.flex k)) t = w.bits t k := by
  intro p
  apply prepared_of_realizers (σ := {modes := w.modes}) hn hΔ w.scalars _ _ w.endpoints
  intro k hk
  have read : (trees p).Reads d (fun t => w.bits t k) :=
    fun x y eq => congrFun (w.reads x y eq) k
  obtain ⟨a, ha, hr, _, he⟩ := (positive_iff_bounded _ (fields p) _ _ _ hn read).mp (w.positive k hk)
  exact ⟨a, ha, by simpa only [imageRank, card_window, card_letter, rootLabelCount] using hr, he⟩

private theorem window_of_prepared {ambient : Bounds} {source target : Scheme} {σ : CompareSubstitution}
    (hw : ComparisonPreparation.PreparedWitnessUnder (SchemePreparation.prepare ambient source target) σ)
    (hs : ComparisonWitnessRestriction.Supported (SchemePreparation.prepare ambient source target) σ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    ∃ d, Nonempty (PositiveWindow (SchemePreparation.prepare ambient source target) d) := by
  let p := SchemePreparation.prepare ambient source target
  let keys := inputTypeKeys p
  let images (k : Nat) := σ.type (.flex k)
  let bits (x : States p) (k : Nat) := if k ∈ keys then value ((fields p).nodes (trees p)) (images k) x else false
  let d := keys.toFinset.sup (fun k => rank (images k))
  have read (k) (hk : k ∈ keys) : (trees p).Reads d (value ((fields p).nodes (trees p)) (images k)) :=
    (value_reads _ _ _).mono _ (Finset.le_sup (f := fun k => rank (images k)) (List.mem_toFinset.mpr hk))
  have atKey (k) (hk : k ∈ keys) (t) :
      bits t k = value ((fields p).nodes (trees p)) (images k) t := by simp only [bits, if_pos hk]
  refine ⟨d, ⟨⟨σ.modes, mode_obligations hw hs hΔ, bits, ?_, ?_, ?_⟩⟩⟩
  · intro x y eq
    funext k
    by_cases hk : k ∈ keys
    · exact (atKey k hk x).trans ((read k hk x y eq).trans (atKey k hk y).symm)
    · simp only [bits, if_neg hk]
  · intro k hk
    have allowed : Allowed p.assumptions (typeNames p) (modeNames p) (images k) :=
      ⟨hw.2.1.types _, (hs.type ((mem_inputNames p _).mp ((mem_inputTypeKeys p k).mp hk).1)).mono
        (fun _ h => Finset.mem_toList.mpr h) (fun _ h => Finset.mem_toList.mpr h)⟩
    exact ⟨fun x y rel => atKey k hk x ▸ atKey k hk y ▸ rel _ allowed,
      fun x _ all => (atKey k hk x).trans (all _ allowed)⟩
  · intro a b hab t
    obtain ⟨hab', ha, hb⟩ := prepared_witness_endpoints hw hs hΔ (a,b) hab
    have hc := certified p.assumptions (typeNames p) (modeNames p)
    have eq (a : Ty) :
        eval (trees p) (fields p) keys σ.mode bits a t =
        value ((fields p).nodes (trees p)) (instantiate keys images σ.mode a) t :=
      (eval_image_congr _ _ _ _ bits _ atKey a t).trans (eval_instantiated ..)
    exact (eq a) ▸ (eq b) ▸ subtype_mono hc.modal hc.range hc.coherent hc.bounds hΔ ha hb hab' t

/-- On the recursive defined-bound branch, the original scheme comparison is
equivalent to a shared positive assignment of some finite radius. Each such
assignment reconstructs one admissible substitution at the computed image rank. -/
theorem subsumes_iff_positive_window {ambient : Bounds} {source target : Scheme}
    (hn : ¬ ∃ ρ, ComparisonShape.Models (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined) :
    AlgebraSubsumesUnder ambient source target ↔
      ∃ d, Nonempty (PositiveWindow (SchemePreparation.prepare ambient source target) d) := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := ComparisonPreparation.prepare_algebra_under_complete h
    obtain ⟨τ, ht, _, _, hs⟩ := ComparisonWitnessRestriction.prepared_supported_under hσ
    exact window_of_prepared ht hs hΔ
  · rintro ⟨_, ⟨w⟩⟩
    obtain ⟨_, h, _⟩ := w.witness hn hΔ
    exact h.subsumes

/-- The joint comparator reconstructs the public binder domain at the rank
computed from the input and the radius of this shared positive solution. -/
theorem PositiveWindow.compare_at {ambient : Bounds} {source target : Scheme}
    (hn : ¬ ∃ ρ, ComparisonShape.Models (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    {d} (w : PositiveWindow (SchemePreparation.prepare ambient source target) d) :
    ∃ threshold result, ∀ fuel ≥ threshold, ComparisonRankedJoint.compare fuel ambient source target
      (imageRank (SchemePreparation.prepare ambient source target) d) = .success result := by
  obtain ⟨τ, hw, hs, _, _, rank⟩ := w.witness hn hΔ
  exact ComparisonRankedJoint.compare_complete_at hn hΔ hw hs _ (fun k hk => (rank k hk).1)

/-- A completed rejection at this rank rules out every shared positive window
of radius at most the one used in the rank calculation. -/
theorem refutes_window {ambient : Bounds} {source target : Scheme} {fuel d : Nat} {reason : String}
    (hn : ¬ ∃ ρ, ComparisonShape.Models (SchemePreparation.prepare ambient source target).assumptions ρ)
    (hΔ : (SchemePreparation.prepare ambient source target).assumptions.TypeBoundsDefined)
    (reject : ComparisonRankedJoint.compare fuel ambient source target
      (imageRank (SchemePreparation.prepare ambient source target) d) = .rejected reason) :
    ∀ e ≤ d, ¬ Nonempty (PositiveWindow (SchemePreparation.prepare ambient source target) e) := by
  rintro e he ⟨w⟩
  let v : PositiveWindow (SchemePreparation.prepare ambient source target) d :=
    ⟨w.modes, w.scalars, w.bits, w.reads.mono _ he, w.positive, w.endpoints⟩
  obtain ⟨threshold, result, yes⟩ := v.compare_at hn hΔ
  have no := ComparisonRankedJoint.compare_stable reject (by simp) (Nat.le_max_left fuel threshold)
  rw [yes _ (Nat.le_max_right fuel threshold)] at no
  contradiction

end ModalityInference.ComparisonWindowWitness
