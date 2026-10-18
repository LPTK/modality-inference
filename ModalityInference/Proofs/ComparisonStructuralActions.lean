import ModalityInference.ComparisonStructuralActions
import ModalityInference.Proofs.ComparisonStructuralFamily

/-! The executable signed-control action compiler reconstructs a type algebraically
equivalent to each guarded modal input and supplies the finite certificates used
by the common-parent structural family theory. -/
namespace ModalityInference.ComparisonStructuralActions

open ComparisonAlgebra ComparisonControls ComparisonPropagation ComparisonStructuralLattice
open ComparisonStructuralFamily

theorem prepareAction_spec {fuel : Nat} {b : Basis} {m : ModExpr} {a : Action}
    (h : prepareAction fuel b m = .success a) :
    low fuel b m = .success a.lower ∧ high fuel b m = .success a.upper := by
  cases hl : low fuel b m <;> simp [prepareAction, hl, bind, RunResult.bind] at h
  rename_i lower
  cases hu : high fuel b m <;> simp [hu, pure] at h
  subst a
  exact ⟨rfl,rfl⟩

theorem Action.polynomial {fuel : Nat} {b : Basis} {m : ModExpr} {a : Action}
    (hl : low fuel b m = .success a.lower) (hu : high fuel b m = .success a.upper)
    {input : CNF} (hp : Polynomial b input) : Polynomial b (a.apply input) :=
  (hp.join (Polynomial.of_shape (low_shape hl))).meet (Polynomial.of_shape (high_shape hu))

theorem Action.theory {fuel : Nat} {b : Basis} {m : ModExpr} {a : Action}
    (hl : low fuel b m = .success a.lower) (hu : high fuel b m = .success a.upper)
    {input : CNF} {basisAtom headAtom modeAtom : Nat → Nat}
    {coordinate : Coordinate} {σ : Nat → Bool} {value : BoolExpr}
    (ht : (b.theoryAt basisAtom headAtom modeAtom coordinate).eval σ = true)
    (hi : CNFHolds (σ ∘ basisAtom) input ↔ value.eval σ = true)
    (hlo : (b.formula headAtom modeAtom coordinate .bottom).eval σ = true → value.eval σ = true)
    (hhi : value.eval σ = true → (b.formula headAtom modeAtom coordinate .top).eval σ = true) :
    CNFHolds (σ ∘ basisAtom) (a.apply input) ↔
      (coordinate.modalWith modeAtom value m).eval σ = true := by
  rw [Action.apply, meet_correct, join_correct, low_theory hl ht, high_theory hu ht, hi,
    modalWith_clamp hlo hhi m]
  simp only [Bool.and_eq_true, Bool.or_eq_true]


private def interleave (basis heads modes : Nat → Bool) (i : Nat) : Bool :=
  if i % 3 = 0 then basis (i / 3)
  else if i % 3 = 1 then heads (i / 3)
  else modes (i / 3)

@[simp] private theorem interleave_basis (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3 * i) = basis i := by
  simp [interleave, Nat.mul_comm]

@[simp] private theorem interleave_heads (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3 * i + 1) = heads i := by
  have hd : (3 * i + 1) / 3 = i := by omega
  have hm : (3 * i + 1) % 3 = 1 := by omega
  simp [interleave, hd, hm]

@[simp] private theorem interleave_modes (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3 * i + 2) = modes i := by
  have hd : (3 * i + 2) / 3 = i := by omega
  have hm : (3 * i + 2) % 3 = 2 := by omega
  simp [interleave, hd, hm]

private theorem formula_value {b : Basis} {basisAtom headAtom modeAtom : Nat → Nat}
    {coordinate : Coordinate} {σ : Nat → Bool} {value : CompareTy → Bool}
    (ht : (b.theoryAt basisAtom headAtom modeAtom coordinate).eval σ = true)
    (hb : ∀i, σ (basisAtom i) = basisValue b.types value i)
    {key : Key} (hk : key∈b.keys) :
    (b.formula headAtom modeAtom coordinate key).eval σ = value (b.term key) := by
  obtain ⟨i,hi⟩ := index_exists hk
  rw [← theoryAt_index ht hi, hb]
  simp only [basisValue, Basis.types, List.getElem?_map, index_lookup hi, Option.map_some,
    Option.getD_some]


theorem Action.correct {Δ : Bounds} {shape : ComparisonShape} {fuel : Nat}
    {b : Basis} {m : ModExpr} {a : Action}
    (hl : low fuel b m = .success a.lower) (hu : high fuel b m = .success a.upper)
    (hh : ∀x∈b.heads, Representable Δ shape x) (hm : DefinedMode Δ m)
    {input : CNF} {t : CompareTy} (hp : Polynomial b input)
    (ht : reify b.types input = some t) :
    ∃u, reify b.types (a.apply input) = some u ∧
      Representable Δ shape u ∧ Equiv Δ u (.modal t m) := by
  obtain ⟨u,hu'⟩ := (a.polynomial hl hu hp).reify
  obtain ⟨lower,upper,hle,hue,hlu,hheads,htypes,hpairs⟩ := b.carrier_interval
    CompareTy.var ModExpr.var (by simpa only [CompareTy.subst_id] using hh)
    (fun _ _ _ _ => rfl)
  simp only [CompareTy.subst_id] at hle hue hheads htypes hpairs
  have hti := InInterval.reify ht CompareTy.var ModExpr.var
    (by simpa only [CompareTy.subst_id] using htypes)
  have hui := InInterval.reify hu' CompareTy.var ModExpr.var
    (by simpa only [CompareTy.subst_id] using htypes)
  simp only [CompareTy.subst_id] at hti hui
  obtain ⟨htr,hlt,htu⟩ := hti
  obtain ⟨hur,hlu',huu⟩ := hui
  obtain ⟨hmr,hlm,hmu⟩ := (show InInterval (lower.atMode Mode.bottom)
    (upper.atMode Mode.top) t from ⟨htr,hlt,htu⟩).modal hm
  have he : ∀f : LatticeHom (Order Δ shape) Bool,
      booleanValue f u = booleanValue f (.modal t m) := by
    intro f
    cases hlo : observer f (lower.atMode Mode.bottom) with
    | true =>
      have hvu := observer_mono f hlu' hlo
      have hvm := observer_mono f hlm hlo
      simpa only [booleanValue_represented f u hur, booleanValue_represented f _ hmr] using
        hvu.trans hvm.symm
    | false =>
      cases hhi : observer f (upper.atMode Mode.top) with
      | false =>
        have hvu : observer f (represented hur) = false := by
          cases hx : observer f (represented hur)
          · rfl
          · have := observer_mono f huu hx
            simp_all
        have hvm : observer f (represented hmr) = false := by
          cases hx : observer f (represented hmr)
          · rfl
          · have := observer_mono f hmu hx
            simp_all
        simpa only [booleanValue_represented f u hur, booleanValue_represented f _ hmr] using
          hvu.trans hvm.symm
      | true =>
        obtain ⟨c,η,_,hmodel⟩ := b.observer_model f lower upper hlu hlo hhi
          ModExpr.var (fun η => η) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
          (by simpa only [CompareTy.subst_id] using hpairs) [m]
          (by simpa only [List.forall_mem_singleton, ModExpr.subst_id] using hm)
        let σ := interleave (basisValue b.types (booleanValue f))
          (basisValue b.heads (booleanValue f)) (encodeModes η)
        have hhead : ∀i (hi : i < b.heads.length),
            σ (3*i+1) = booleanValue f b.heads[i] := by
          intro i hi
          simp [σ, basisValue, List.getElem?_eq_getElem hi]
        have hbases : ∀i (hi : i < b.types.length),
            σ (3*i) = booleanValue f b.types[i] := by
          intro i hi
          simp [σ, basisValue, List.getElem?_eq_getElem hi]
        obtain ⟨htheory,hmodal⟩ := hmodel σ (fun i => 3*i) (fun i => 3*i+1) (fun i => 3*i+2)
          (by simpa only [CompareTy.subst_id] using hhead)
          (by simpa only [CompareTy.subst_id] using hbases) (by intro i; simp [σ])
        simp only [CompareTy.subst_id] at hmodal
        have hσ : σ ∘ (fun i => 3*i) = basisValue b.types (booleanValue f) := by
          funext i
          simp [σ]
        have hbvalue := formula_value htheory (fun i => congrFun hσ i)
          (show Key.bottom∈b.keys by simp [Basis.keys])
        have htvalue := formula_value htheory (fun i => congrFun hσ i)
          (show Key.top∈b.keys by simp [Basis.keys])
        have hbendpoint : booleanValue f b.bottom = observer f (lower.atMode Mode.bottom) := by
          rw [Basis.bottom, ← hle]
          exact booleanValue_carrier f (lower.atMode Mode.bottom)
        have htendpoint : booleanValue f b.top = observer f (upper.atMode Mode.top) := by
          rw [Basis.top, ← hue]
          exact booleanValue_carrier f (upper.atMode Mode.top)
        have hs : CNFHolds (σ ∘ (fun i => 3*i)) input ↔
            (BoolExpr.const (booleanValue f t)).eval σ = true := by
          rw [hσ]
          simpa only [CompareTy.subst_id, BoolExpr.eval] using
            (reify_booleanValue ht f CompareTy.var ModExpr.var).symm
        have hboundlo : (b.formula (fun i => 3*i+1) (fun i => 3*i+2) c .bottom).eval σ = true →
            (BoolExpr.const (booleanValue f t)).eval σ = true := by
          rw [hbvalue, show b.term .bottom = b.bottom from rfl, hbendpoint]
          intro h
          simpa only [BoolExpr.eval, booleanValue_represented f t htr] using observer_mono f hlt h
        have hboundhi : (BoolExpr.const (booleanValue f t)).eval σ = true →
            (b.formula (fun i => 3*i+1) (fun i => 3*i+2) c .top).eval σ = true := by
          rw [htvalue, show b.term .top = b.top from rfl, htendpoint]
          intro h
          apply observer_mono f htu
          simpa only [BoolExpr.eval, booleanValue_represented f t htr] using h
        have hsem := a.theory hl hu htheory hs hboundlo hboundhi
        rw [hσ, ← hmodal t ⟨htr,hlt,htu⟩ m (by simp)] at hsem
        apply Bool.eq_iff_iff.mpr
        have hv := reify_booleanValue hu' f CompareTy.var ModExpr.var
        simp only [CompareTy.subst_id] at hv
        exact hv.trans hsem
  refine ⟨u,hu',hur,?_,?_⟩
  · apply (subtype_iff_boolean_observers (represented hur) (represented hmr)).mpr
    intro f
    have h := he f
    rw [booleanValue_represented f _ hur, booleanValue_represented f _ hmr] at h
    exact le_of_eq h
  · apply (subtype_iff_boolean_observers (represented hmr) (represented hur)).mpr
    intro f
    have h := he f
    rw [booleanValue_represented f _ hur, booleanValue_represented f _ hmr] at h
    exact le_of_eq h.symm


theorem prepareAction_complete {b : Basis} {m : ModExpr}
    (hm : ∀v∈m.freeVariables, v∈b.modes) :
    ∃ threshold a, ∀fuel≥threshold, prepareAction fuel b m = .success a := by
  obtain ⟨n,lower,hl⟩ := low_complete hm
  obtain ⟨k,upper,hu⟩ := high_complete hm
  refine ⟨max n k,⟨lower,upper⟩,?_⟩
  intro fuel hf
  simp [prepareAction, hl fuel ((le_max_left _ _).trans hf),
    hu fuel ((le_max_right _ _).trans hf), bind, pure, RunResult.bind]

theorem prepareAction_monotone {small large : Nat} {b : Basis} {m : ModExpr} {a : Action}
    (hle : small≤large) (h : prepareAction small b m = .success a) :
    prepareAction large b m = .success a := by
  obtain ⟨hl,hu⟩ := prepareAction_spec h
  simp [prepareAction, low_monotone hle hl, high_monotone hle hu, bind, pure, RunResult.bind]

theorem prepare_spec {fuel : Nat} {left right : Basis} {m : ModExpr}
    {a : Absorption left.types.length right.types.length}
    (h : prepare fuel left right m = .success a) :
    ∃l r, prepareAction fuel left m = .success l ∧ prepareAction fuel right m = .success r ∧
      a = ⟨m,Vector.ofFn (fun i => l.apply [[(i.val,true)]]),
        Vector.ofFn (fun j => r.apply [[(j.val,true)]])⟩ := by
  cases hl : prepareAction fuel left m <;> simp [prepare, hl, bind, RunResult.bind] at h
  rename_i l
  cases hr : prepareAction fuel right m <;> simp [hr, pure] at h
  rename_i r
  exact ⟨l,r,rfl,rfl,h.symm⟩

theorem prepare_certified {Δ : Bounds} {s t : ComparisonShape} {fuel : Nat}
    {left right : Basis} {m : ModExpr} {a : Absorption left.types.length right.types.length}
    (h : prepare fuel left right m = .success a)
    (hl : ∀x∈left.heads, Representable Δ s x)
    (hr : ∀y∈right.heads, Representable Δ t y) (hm : DefinedMode Δ m) :
    a.Certified Δ left.types right.types := by
  obtain ⟨l,r,hleft,hright,rfl⟩ := prepare_spec h
  obtain ⟨hll,hlu⟩ := prepareAction_spec hleft
  obtain ⟨hrl,hru⟩ := prepareAction_spec hright
  refine ⟨hm,?_,?_⟩
  · intro i
    obtain ⟨u,hu,_,he⟩ := l.correct hll hlu hl hm (Polynomial.atom i.isLt)
      (reify_singleton left.types i)
    exact ⟨u,by simpa using hu,he⟩
  · intro j
    obtain ⟨u,hu,_,he⟩ := r.correct hrl hru hr hm (Polynomial.atom j.isLt)
      (reify_singleton right.types j)
    exact ⟨u,by simpa using hu,he⟩

theorem prepare_complete {left right : Basis} {m : ModExpr}
    (hl : ∀v∈m.freeVariables, v∈left.modes) (hr : ∀v∈m.freeVariables, v∈right.modes) :
    ∃ threshold a, ∀fuel≥threshold, prepare fuel left right m = .success a := by
  obtain ⟨n,l,hl⟩ := prepareAction_complete hl
  obtain ⟨k,r,hr⟩ := prepareAction_complete hr
  refine ⟨max n k,⟨m,Vector.ofFn (fun i => l.apply [[(i.val,true)]]),
    Vector.ofFn (fun j => r.apply [[(j.val,true)]])⟩,?_⟩
  intro fuel hf
  simp [prepare, hl fuel ((le_max_left _ _).trans hf), hr fuel ((le_max_right _ _).trans hf),
    bind, pure, RunResult.bind]

theorem prepare_monotone {small large : Nat} {left right : Basis} {m : ModExpr}
    {a : Absorption left.types.length right.types.length}
    (hle : small≤large) (h : prepare small left right m = .success a) :
    prepare large left right m = .success a := by
  obtain ⟨l,r,hl,hr,rfl⟩ := prepare_spec h
  simp [prepare, prepareAction_monotone hle hl, prepareAction_monotone hle hr,
    bind, pure, RunResult.bind]

end ModalityInference.ComparisonStructuralActions
