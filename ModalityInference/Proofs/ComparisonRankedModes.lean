import ModalityInference.ComparisonRankedModes
import ModalityInference.Proofs.ComparisonRankedDecision
import ModalityInference.Proofs.ComparisonSignedEndpointQueries
import ModalityInference.Proofs.ComparisonLayoutWorlds
import ModalityInference.Proofs.ComparisonPreparedScalar
import ModalityInference.Proofs.ComparisonJointAssemblyModes

namespace ModalityInference.ComparisonRankedModes

open ComparisonObserverMachineFormula ComparisonSignedEndpoints
  ComparisonStructuralLayout ComparisonSignedObservation

abbrev raw (strategy : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool) :=
  ComparisonSignedPoints.raw ComparisonLayoutWorlds.decode strategy world

abbrev localWorld (world : Nat → Nat → Bool) (state : Nat) :=
  world (ComparisonLayoutWorlds.routeCode (route state) + 1)

@[simp] theorem nominal_eval (strategy : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (state field index : Nat) :
    (nominal state field index).eval (raw strategy world) =
      world 0 (routeAtom (route state) (choiceAtom (Nat.pair field index))) := by
  simp [nominal, raw, ComparisonSignedPoints.raw, BoolExpr.eval]

@[simp] theorem scalarField_eval (strategy : (Nat → Bool) → Nat → Bool)
    (world : Nat → Nat → Bool) (state : Nat) (v : ModVar) (axis : Nat) :
    (scalarField state v axis).eval (raw strategy world) =
      strategy (localWorld world state) (v.atomIndex axis) := by
  simp [scalarField, raw, ComparisonSignedPoints.raw, BoolExpr.eval, localWorld]

private theorem getElem_idxOf_mem {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} {a : α} (ha : a ∈ xs) : xs[xs.idxOf a]? = some a := by
  have hi := List.idxOf_lt_length_of_mem ha
  rw [List.getElem?_eq_getElem hi]
  congr 1
  simpa only [List.idxOf, beq_iff_eq] using
    (List.findIdx_getElem (xs := xs) (p := (· == a)) (w := hi))

theorem fields_mode {types names count} (i : Fin count) {v : ModVar} (hv : v ∈ names) :
    mode names (fields types names count i) v =
      (scalarField i v 0, scalarField i v 1, scalarField i v 2) := by
  simp [mode, fields, hv, List.getElem?_map, getElem_idxOf_mem hv]

theorem fields_modeValue {types names count} (i : Fin count) {v : ModVar} (hv : v ∈ names)
    (strategy : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool) :
    ComparisonObserverMachineCheck.modeValue names
        (decode (fields types names count) (raw strategy world) i) v =
      projectedModes (strategy (localWorld world i)) v := by
  rw [← mode_eval, fields_mode i hv]
  simp [scalar, projectedModes]

theorem fields_branch (types : List TypeVar) (left right : List ModVar) (count : Nat)
    (i : Fin count) (s t : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool)
    (k : Constructor) :
    (decode (fields types left count) (raw s world) i).branch k =
      (decode (fields types right count) (raw t world) i).branch k := by
  simp [decode, fields]

theorem fields_coordinate (types : List TypeVar) (left right : List ModVar) (count : Nat)
    (i : Fin count) (s t : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool) :
    (decode (fields types left count) (raw s world) i).coordinate =
      (decode (fields types right count) (raw t world) i).coordinate := by
  simp [decode, fields]

theorem fields_atom (types : List TypeVar) (left right : List ModVar) (count : Nat)
    (i : Fin count) (s t : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool)
    (v : TypeVar) :
    (atom types (fields types left count i) v).eval (raw s world) =
      (atom types (fields types right count i) v).eval (raw t world) := by
  simp only [atom]
  split
  · simp only [fields, List.getElem?_map]
    cases (List.range types.length)[types.idxOf v]? <;> simp
  · simp [fields]

theorem fields_decode_congr {types names count}
    (s t : (Nat → Bool) → Nat → Bool) (world : Nat → Nat → Bool)
    (h : ∀ i : Fin count, ∀ v ∈ names,
      projectedModes (s (localWorld world i)) v = projectedModes (t (localWorld world i)) v) :
    decode (fields types names count) (raw s world) =
      decode (fields types names count) (raw t world) := by
  have hscalar (f : (Nat → Bool) → Nat → Bool) (i : Fin count) (v : ModVar) :
      scalar (scalarField i v 0, scalarField i v 1, scalarField i v 2) (raw f world) =
        projectedModes (f (localWorld world i)) v := by
    simp [scalar, projectedModes]
  funext i
  simp only [decode, fields, List.map_map, Function.comp_def, nominal_eval, hscalar]
  congr 1
  exact List.map_congr_left fun v hv => h i v hv

theorem core_decode {types names count} (modes : ModVar → ModExpr)
    (hfixed : ∀ v ∈ names, modes v = .var v) (world : Nat → Nat → Bool) :
    decode (fields types names count) (raw (SchemeModeSynthesis.strategy modes) world) =
      decode (fields types names count) (raw id world) := by
  funext i
  have hm : (names.map fun v =>
      scalar (scalarField i v 0, scalarField i v 1, scalarField i v 2)
        (raw (SchemeModeSynthesis.strategy modes) world)) =
      names.map fun v => scalar (scalarField i v 0, scalarField i v 1, scalarField i v 2)
        (raw id world) := by
    apply List.map_congr_left
    intro v hv
    simp [scalar, SchemeModeSynthesis.strategy_coordinate, hfixed v hv,
      SchemeModeSynthesis.coordinate, ModExpr.project, BoolExpr.eval]
  simpa only [decode, fields, List.map_map, Function.comp_def, nominal_eval] using
    congrArg (fun ms : List Mode =>
      ({ atoms := ((List.range types.length).map fun n =>
          (nominal i 0 n).eval (raw id world))
         modes := ms
         coordinate := coordinate ((nominal i 1 0).eval (raw id world))
           ((nominal i 1 1).eval (raw id world))
         unitValue := (nominal i 2 0).eval (raw id world)
         creditValue := (nominal i 2 1).eval (raw id world)
         branch := fun k => ⟨(nominal i 3 (constructorCode k)).eval (raw id world),
           firstTrue i (fun j => (nominal i (4 + constructorCode k) j).eval
             (raw id world)) (List.finRange count)⟩
         range := fun b => (nominal i 7 (if b then 1 else 0)).eval (raw id world) } :
        ComparisonObserverMachineCheck.Description (Fin count))) hm

theorem scalar_models {Δ types names count} {i : Fin count}
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (world : Nat → Nat → Bool)
    (hs : (scalarOK Δ names (fields types names count i)).eval (raw id world) = true) :
    (decode (fields types names count) (raw id world) i).coordinate = .unaffected ∨
      ModeModels Δ (projectedModes (localWorld world i)) := by
  rw [scalarOK_eval, ComparisonObserverMachineCheck.scalarOK_correct] at hs
  exact hs.imp_right fun hm => (ModeModels.congr Δ
    (fun v hv => fields_modeValue i (hscope v hv) id world)).mp hm

theorem action_subst {Δ types names count} {modeIds : List Nat}
    (modes : ModVar → ModExpr)
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (himages : ∀ v ∈ extended names modeIds, ∀ w ∈ (modes v).vars, w ∈ names)
    (htotal : ∀ η, ModeModels Δ η → ∀ v, (modes v).WellFormed η)
    (world : Nat → Nat → Bool) (i : Fin count)
    (hs : (scalarOK Δ names (fields types names count i)).eval (raw id world) = true)
    (m : ModExpr) (hm : ∀ v ∈ m.vars, v ∈ extended names modeIds) (x : Bool) :
    ComparisonObserverMachineCheck.action (extended names modeIds)
        (decode (fields types (extended names modeIds) count)
          (raw (SchemeModeSynthesis.strategy modes) world) i) m x =
      ComparisonObserverMachineCheck.action names
        (decode (fields types names count) (raw id world) i) (m.subst modes) x := by
  have hc := fields_coordinate types (extended names modeIds) names count i
    (SchemeModeSynthesis.strategy modes) id world
  rcases scalar_models hscope world hs with hu | hη
  · simp [ComparisonObserverMachineCheck.action, hc, hu,
      ComparisonObserverMachineCheck.act]
  · unfold ComparisonObserverMachineCheck.action
    rw [hc]
    congr 2
    rw [ModExpr.eval_subst]
    apply m.eval_congr
    intro v hv
    simp only [Function.comp_apply]
    rw [fields_modeValue i (hm v hv)]
    have he : (modes v).eval
        (some ∘ ComparisonObserverMachineCheck.modeValue names
          (decode (fields types names count) (raw id world) i)) =
        (modes v).eval (some ∘ projectedModes (localWorld world i)) :=
      (modes v).eval_congr (fun w hw => congrArg some
        (fields_modeValue i (himages v (hm v hv) w hw) id world))
    exact (he.trans (SchemeModeSynthesis.strategy_eval modes (localWorld world i) v
      (htotal _ hη v))).symm

theorem action_subst_with {Δ types names count} {modeIds : List Nat}
    (modes : ModVar → ModExpr)
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (himages : ∀ v ∈ extended names modeIds, ∀ w ∈ (modes v).vars, w ∈ names)
    (htotal : ∀ η, ModeModels Δ η → ∀ v, (modes v).WellFormed η)
    (world : Nat → Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    (he : ∀ i : Fin count, ∀ v ∈ extended names modeIds,
      projectedModes (strategy (localWorld world i)) v =
        projectedModes (SchemeModeSynthesis.strategy modes (localWorld world i)) v)
    (i : Fin count)
    (hs : (scalarOK Δ names (fields types names count i)).eval (raw id world) = true)
    (m : ModExpr) (hm : ∀ v ∈ m.vars, v ∈ extended names modeIds) (x : Bool) :
    ComparisonObserverMachineCheck.action (extended names modeIds)
        (decode (fields types (extended names modeIds) count) (raw strategy world) i) m x =
      ComparisonObserverMachineCheck.action names
        (decode (fields types names count) (raw id world) i) (m.subst modes) x := by
  rw [fields_decode_congr strategy (SchemeModeSynthesis.strategy modes) world he]
  exact action_subst modes hscope himages htotal world i hs m hm x

theorem observe_reads {Δ types names count} {keys modeIds : List Nat}
    (modes : ModVar → ModExpr)
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (himages : ∀ v ∈ extended names modeIds, ∀ w ∈ (modes v).vars, w ∈ names)
    (htotal : ∀ η, ModeModels Δ η → ∀ v, (modes v).WellFormed η)
    (world : Nat → Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    (hstrategy : ∀ i : Fin count, ∀ v ∈ extended names modeIds,
      projectedModes (strategy (localWorld world i)) v =
        projectedModes (SchemeModeSynthesis.strategy modes (localWorld world i)) v)
    (hs : ∀ i : Fin count,
      (scalarOK Δ names (fields types names count i)).eval (raw id world) = true)
    (images : Nat → CompareTy) (calls : Call → Bool)
    (hreads : ∀ name ∈ keys, ∀ i : Fin count, calls (ComparisonRankedDecision.call name i) =
      (value types names (fields types names count) (images name) i).eval (raw id world))
    (a : Ty) (ha : ∀ v ∈ a.modVars, v ∈ extended names modeIds) (i : Fin count) :
    Represents (raw strategy world) calls
      (ComparisonRankedDecision.observe keys types (extended names modeIds)
        (fields types (extended names modeIds) count) ModExpr.var a i)
      ((value types names (fields types names count)
        (ComparisonRankedDecision.instantiate keys images modes a) i).eval (raw id world)) := by
  induction a generalizing i with
  | var v =>
    cases v with
    | rigid n =>
      simpa only [ComparisonRankedDecision.observe, ComparisonRankedDecision.reference,
        ComparisonRankedDecision.instantiate, ComparisonRankedDecision.imageTypes,
        CompareTy.ofTy, CompareTy.subst, value, Data.eval,
        fields_atom types (extended names modeIds) names count i
          strategy id world] using
        Represents.base (raw strategy world) calls
          (Data.fixed (atom types (fields types (extended names modeIds) count i) (.rigid n)))
    | flex n =>
      by_cases hn : n ∈ keys
      · simp [ComparisonRankedDecision.observe, ComparisonRankedDecision.reference,
          ComparisonRankedDecision.instantiate, ComparisonRankedDecision.imageTypes,
          CompareTy.ofTy, CompareTy.subst, Represents, hn, hreads, Data.eval, BoolExpr.eval]
      · simpa only [ComparisonRankedDecision.observe, ComparisonRankedDecision.reference,
          ComparisonRankedDecision.instantiate, ComparisonRankedDecision.imageTypes,
          CompareTy.ofTy, CompareTy.subst, value, List.contains_iff_mem, hn,
          if_false, Data.eval,
          fields_atom types (extended names modeIds) names count i
            strategy id world] using
          Represents.base (raw strategy world) calls
            (Data.fixed (atom types (fields types (extended names modeIds) count i) (.flex n)))
  | unit =>
    simpa only [ComparisonRankedDecision.observe, ComparisonRankedDecision.instantiate,
      CompareTy.ofTy, CompareTy.subst, value, fields, Data.eval, nominal_eval] using
      Represents.base (raw strategy world) calls
        (Data.fixed (nominal i 2 0))
  | credit =>
    simpa only [ComparisonRankedDecision.observe, ComparisonRankedDecision.instantiate,
      CompareTy.ofTy, CompareTy.subst, value, fields, Data.eval, nominal_eval] using
      Represents.base (raw strategy world) calls
        (Data.fixed (nominal i 2 1))
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    have hal : ∀ v ∈ a.modVars, v ∈ extended names modeIds := fun v hv =>
      ha v (Finset.mem_union_left _ hv)
    have har : ∀ v ∈ b.modVars, v ∈ extended names modeIds := fun v hv =>
      ha v (Finset.mem_union_right _ hv)
    have hl (k : Constructor) := ComparisonRankedDecision.choices_correct i
      ((fields types (extended names modeIds) count i).next k)
      _ _ (raw strategy world) calls
      (iha hal) (List.finRange count)
    have hr (k : Constructor) := ComparisonRankedDecision.choices_correct i
      ((fields types (extended names modeIds) count i).next k)
      _ _ (raw strategy world) calls
      (ihb har) (List.finRange count)
    all_goals
      first
      | simpa only [ComparisonRankedDecision.observe, ComparisonRankedDecision.choice,
          ComparisonRankedDecision.next, ComparisonRankedDecision.dual,
          ComparisonRankedDecision.instantiate, CompareTy.ofTy, CompareTy.subst,
          value, mux_eval, successor_eval, BoolExpr.eval, decode, fields, nominal_eval,
          Bool.or_false] using Represents.choice (hl .fn).dual (hr .fn)
            ((fields types (extended names modeIds) count i).left .fn)
      | simpa only [ComparisonRankedDecision.observe, ComparisonRankedDecision.choice,
          ComparisonRankedDecision.next, ComparisonRankedDecision.instantiate,
          CompareTy.ofTy, CompareTy.subst, value, mux_eval, successor_eval,
          decode, fields, nominal_eval] using Represents.choice (hl .prod) (hr .prod)
            ((fields types (extended names modeIds) count i).left .prod)
      | simpa only [ComparisonRankedDecision.observe, ComparisonRankedDecision.choice,
          ComparisonRankedDecision.next, ComparisonRankedDecision.instantiate,
          CompareTy.ofTy, CompareTy.subst, value, mux_eval, successor_eval,
          decode, fields, nominal_eval] using Represents.choice (hl .sum) (hr .sum)
            ((fields types (extended names modeIds) count i).left .sum)
  | modal a m ih =>
    have hal : ∀ v ∈ a.modVars, v ∈ extended names modeIds := fun v hv =>
      ha v (Finset.mem_union_left _ hv)
    have hml : ∀ v ∈ m.vars, v ∈ extended names modeIds := fun v hv =>
      ha v (Finset.mem_union_right _ hv)
    let x := (value types names (fields types names count)
      (ComparisonRankedDecision.instantiate keys images modes a) i).eval (raw id world)
    have he := action_subst_with modes hscope himages htotal world strategy hstrategy i (hs i) m hml x
    have hv : (value types names (fields types names count)
        (ComparisonRankedDecision.instantiate keys images modes (.modal a m)) i).eval
        (raw id world) =
      (action (extended names modeIds) (fields types (extended names modeIds) count i)
        m (.const x)).eval (raw strategy world) := by
      simpa only [ComparisonRankedDecision.instantiate, CompareTy.ofTy, CompareTy.subst,
        value, action_eval, BoolExpr.eval] using he.symm
    rw [hv, ComparisonRankedDecision.action_clamp]
    simpa only [ComparisonRankedDecision.observe, ComparisonRankedDecision.acted,
      ModExpr.subst_id, BoolExpr.eval] using (ih hal i).act
      (action (extended names modeIds) (fields types (extended names modeIds) count i)
        m (.const false))
      (action (extended names modeIds) (fields types (extended names modeIds) count i)
        m (.const true))

theorem compile_reads {Δ types names count} {keys modeIds : List Nat}
    (modes : ModVar → ModExpr)
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (himages : ∀ v ∈ extended names modeIds, ∀ w ∈ (modes v).vars, w ∈ names)
    (htotal : ∀ η, ModeModels Δ η → ∀ v, (modes v).WellFormed η)
    (world : Nat → Nat → Bool) (strategy : (Nat → Bool) → Nat → Bool)
    (hstrategy : ∀ i : Fin count, ∀ v ∈ extended names modeIds,
      projectedModes (strategy (localWorld world i)) v =
        projectedModes (SchemeModeSynthesis.strategy modes (localWorld world i)) v)
    (hs : ∀ i : Fin count,
      (scalarOK Δ names (fields types names count i)).eval (raw id world) = true)
    (images : Nat → CompareTy) (calls : Call → Bool)
    (hreads : ∀ name ∈ keys, ∀ i : Fin count, calls (ComparisonRankedDecision.call name i) =
      (value types names (fields types names count) (images name) i).eval (raw id world))
    (a b : Ty) (ha : ∀ v ∈ a.modVars, v ∈ extended names modeIds)
    (hb : ∀ v ∈ b.modVars, v ∈ extended names modeIds) (i : Fin count) :
    (∀ c ∈ ComparisonRankedDecision.compile keys types (extended names modeIds)
      (fields types (extended names modeIds) count) ModExpr.var a b i,
      c.Holds (raw strategy world) calls) ↔
    (value types names (fields types names count)
      (ComparisonRankedDecision.instantiate keys images modes a) i).eval (raw id world) ≤
    (value types names (fields types names count)
      (ComparisonRankedDecision.instantiate keys images modes b) i).eval (raw id world) := by
  simp only [ComparisonRankedDecision.compile, List.forall_mem_flatMap, compare_correct,
    BoolExpr.eval, Bool.and_eq_true, Bool.le_iff_imp]
  have hl := observe_reads modes hscope himages htotal world strategy hstrategy hs images calls hreads a ha i
  have hr := observe_reads modes hscope himages htotal world strategy hstrategy hs images calls hreads b hb i
  constructor
  · intro h hleft
    obtain ⟨l, hll, hla⟩ := hl.1
    obtain ⟨r, hrr, hra⟩ := hr.1
    have hh := h l hll r hrr ⟨hla, hra⟩
    rw [hl.2 l hll hla, hr.2 r hrr hra] at hh
    exact hh hleft
  · intro h l hll r hrr hactive
    rw [hl.2 l hll hactive.1, hr.2 r hrr hactive.2]
    exact h

theorem aliases_correct (types : List TypeVar) (names : List ModVar) (count : Nat)
    (basis : ComparisonControls.Basis) (world : Nat → Bool) :
    (aliases types names count basis).eval world = true ↔
      ∀ i : Fin count, ∀ index, ∀ h : index < basis.types.length,
        world (routeAtom (route i) (basisAtom index)) =
          (value types names (fields types names count) basis.types[index] i).eval world := by
  have hall (es : List BoolExpr) : (BoolExpr.all es).eval world = true ↔
      ∀ e ∈ es, e.eval world = true := by
    induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]
  rw [aliases, hall]
  simp only [List.forall_mem_flatMap, List.mem_finRange, forall_const, List.forall_mem_map,
    List.forall_mem_zipIdx', equal_eval, BoolExpr.eval, beq_iff_eq]

theorem aliases_reads {keys types names count basis}
    {family : Nat → (Nat → Bool) → Bool} {images : Nat → CompareTy}
    (hf : ComparisonSignedSynthesis.Family (input keys basis) family)
    (hr : ComparisonRankedDecision.Realizes (input keys basis) family images)
    {world : Nat → Bool} (ht : (aliases types names count basis).eval world = true)
    {name : Nat} (hn : name ∈ keys) (i : Fin count) :
    ComparisonSignedPoints.basisImages (fun _ => basis.types.length) family world
      (ComparisonRankedDecision.call name i) =
      (value types names (fields types names count) (images name) i).eval world := by
  unfold ComparisonSignedPoints.basisImages
  change family name _ = _
  rw [hf.congr hn (b := ComparisonPropagation.basisValue basis.types
    (fun a => (value types names (fields types names count) a i).eval world)) (fun index h => by
      change index < basis.types.length at h
      simpa [input, ComparisonSignedPoints.basisPoint, ComparisonRankedDecision.call, route,
        ComparisonPropagation.basisValue, List.getElem?_eq_getElem h, h] using
        (aliases_correct types names count basis world).mp ht i index h)]
  exact hr name hn _ (fun _ _ => rfl) (fun _ _ => rfl)

theorem prepare_spec {fuel Δ keys types names modeIds count basis endpoints q}
    (h : prepare fuel Δ keys types names modeIds count basis endpoints = .success q) :
    ∃ original required,
      CompactCNF.toCNF fuel true (theory Δ types names count basis) = .success original ∧
      compileGuards fuel (clauses keys types names modeIds count endpoints) = .success required ∧
      q = ⟨ComparisonLayoutWorlds.decode, original, required⟩ := by
  cases ht : CompactCNF.toCNF fuel true (theory Δ types names count basis) <;>
    simp [prepare, ht, bind, RunResult.bind] at h
  cases hc : compileGuards fuel (clauses keys types names modeIds count endpoints) <;>
    simp [hc, pure] at h
  exact ⟨_, _, rfl, rfl, h.symm⟩

theorem prepare_complete (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty)) :
    ∃ threshold q, ∀ fuel ≥ threshold,
      prepare fuel Δ keys types names modeIds count basis endpoints = .success q := by
  obtain ⟨n, original, ht⟩ := CompactCNF.toCNF_complete (theory Δ types names count basis) true
  obtain ⟨k, required, hc⟩ :=
    compileGuards_complete (clauses keys types names modeIds count endpoints)
  exact ⟨max n k, ⟨ComparisonLayoutWorlds.decode, original, required⟩, fun fuel hf => by
    simp [prepare, ht fuel ((le_max_left _ _).trans hf),
      hc fuel ((le_max_right _ _).trans hf), bind, pure, RunResult.bind]⟩

theorem prepare_binary {fuel Δ keys types names modeIds count basis endpoints q}
    (h : prepare fuel Δ keys types names modeIds count basis endpoints = .success q) :
    q.Binary := by
  obtain ⟨_, _, _, hr, rfl⟩ := prepare_spec h
  intro c hc
  obtain ⟨c, hc, he⟩ := compileGuards_origin hr hc
  obtain ⟨pair, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  rw [he]
  exact ComparisonRankedDecision.compile_binary hc

theorem prepare_allowed {fuel Δ keys types names modeIds count basis endpoints q}
    (h : prepare fuel Δ keys types names modeIds count basis endpoints = .success q) :
    q.Allowed keys := by
  obtain ⟨_, _, _, hr, rfl⟩ := prepare_spec h
  intro c hc literal hl
  obtain ⟨c, hc, he⟩ := compileGuards_origin hr hc
  obtain ⟨pair, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  exact ComparisonRankedDecision.compile_allowed hc (he ▸ hl)

theorem prepare_valid {fuel Δ keys types names modeIds count basis endpoints q}
    (h : prepare fuel Δ keys types names modeIds count basis endpoints = .success q)
    (family : Nat → (Nat → Bool) → Bool) (strategy : (Nat → Bool) → Nat → Bool) :
    q.Valid (fun _ => basis.types.length) family strategy ↔
      ∀ world, (theory Δ types names count basis).eval (raw strategy world) = true →
        ∀ c ∈ clauses keys types names modeIds count endpoints,
          c.Holds (raw strategy world)
            (ComparisonSignedPoints.basisImages (fun _ => basis.types.length)
              family (raw strategy world)) := by
  obtain ⟨original, required, ht, hr, rfl⟩ := prepare_spec h
  simp only [ComparisonSignedEndpointQueries.Source.Valid,
    ComparisonSignedStrategySynthesis.Valid]
  change (∀ world, ∀ c ∈ required, CNFHolds (raw strategy world) original →
      c.Holds (raw strategy world)
        (ComparisonSignedPoints.basisImages (fun _ => basis.types.length)
          family (raw strategy world))) ↔ _
  constructor
  · intro hv world hh
    apply (compileGuards_correct hr (raw strategy world) _).mp
    intro c hc
    exact hv world c hc ((CompactCNF.toCNF_correct ht (raw strategy world)).mpr hh)
  · intro hv world c hc hh
    exact (compileGuards_correct hr (raw strategy world) _).mpr
      (hv world ((CompactCNF.toCNF_correct ht (raw strategy world)).mp hh)) c hc

theorem prepare_valid_witness {fuel Δ keys types names modeIds count basis endpoints q}
    (h : prepare fuel Δ keys types names modeIds count basis endpoints = .success q)
    (hΔ : Δ.TypeBoundsDefined)
    (modes : ModVar → ModExpr) (images : Nat → CompareTy)
    (hfixed : ∀ v ∈ names, modes v = .var v)
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (himages : ∀ v ∈ extended names modeIds, ∀ w ∈ (modes v).vars, w ∈ names)
    (htotal : ∀ η, ModeModels Δ η → ∀ v, (modes v).WellFormed η)
    (he : ∀ pair ∈ endpoints,
      (∀ v ∈ pair.1.modVars, v ∈ extended names modeIds) ∧
      (∀ v ∈ pair.2.modVars, v ∈ extended names modeIds))
    (hw : ∀ pair ∈ endpoints,
      (ComparisonRankedDecision.instantiate keys images modes pair.1).DefinedUnder Δ ∧
      (ComparisonRankedDecision.instantiate keys images modes pair.2).DefinedUnder Δ ∧
      AlgebraSubtype Δ (ComparisonRankedDecision.instantiate keys images modes pair.1)
        (ComparisonRankedDecision.instantiate keys images modes pair.2))
    {family : Nat → (Nat → Bool) → Bool}
    (hf : ComparisonSignedSynthesis.Family (input keys basis) family)
    (hr : ComparisonRankedDecision.Realizes (input keys basis) family images) :
    q.Valid (fun _ => basis.types.length) family (SchemeModeSynthesis.strategy modes) := by
  rw [prepare_valid h]
  intro world ht
  have hcore := core_decode modes hfixed world (types := types) (count := count)
  have hq : (query Δ types names (fields types names count)).eval (raw id world) = true := by
    have hh := (Bool.and_eq_true_iff.mp ht).1
    simpa only [query_eval, hcore] using hh
  have hp : (aliases types names count basis).eval
      (raw (SchemeModeSynthesis.strategy modes) world) = true := (Bool.and_eq_true_iff.mp ht).2
  have hs (i : Fin count) :
      (scalarOK Δ names (fields types names count i)).eval (raw id world) = true := by
    rw [scalarOK_eval]
    exact (ComparisonObserverMachineCheck.check_correct.mp
      ((query_eval Δ types names _ _).symm.trans hq) i).scalar
  have hreads (name : Nat) (hn : name ∈ keys) (i : Fin count) :
      ComparisonSignedPoints.basisImages (fun _ => basis.types.length) family
        (raw (SchemeModeSynthesis.strategy modes) world) (ComparisonRankedDecision.call name i) =
      (value types names (fields types names count) (images name) i).eval (raw id world) := by
    rw [aliases_reads hf hr hp hn, value_eval, hcore, ← value_eval]
  simp only [clauses, ComparisonRankedDecision.clauses, List.forall_mem_flatMap,
    List.mem_finRange, forall_const]
  intro pair hp i
  apply (compile_reads modes hscope himages htotal world (SchemeModeSynthesis.strategy modes)
    (fun _ _ _ => rfl) hs images _ hreads
    pair.1 pair.2 (he pair hp).1 (he pair hp).2 i).mpr
  simp only [value_eval]
  exact ComparisonObserverMachineCheck.checked_subtype
    ((query_eval Δ types names _ _).symm.trans hq) hΔ (hw pair hp).1 (hw pair hp).2.1
      (hw pair hp).2.2 i

theorem family_exists {keys : List Nat} {basis : ComparisonControls.Basis}
    (images : Nat → CompareTy)
    (hi : ∀ name ∈ keys, ComparisonControls.LatticeForm basis.types (images name)) :
    ∃ family, ComparisonSignedSynthesis.Family (input keys basis) family ∧
      ComparisonRankedDecision.Realizes (input keys basis) family images := by
  let polys (name : Nat) : CNF :=
    (ComparisonLatticeCompiler.compile basis (images name)).getD []
  have hc (name : Nat) (hn : name ∈ keys) :
      ComparisonLatticeCompiler.compile basis (images name) = some (polys name) := by
    obtain ⟨cs, hcs⟩ := ComparisonLatticeCompiler.compile_complete (hi name hn)
    simp [polys, hcs]
  refine ⟨fun name => ComparisonSignedSynthesis.polynomialValue (polys name), ?_, ?_⟩
  · exact ComparisonSignedSynthesis.polynomial_family (input keys basis) polys
      (fun name hn => (ComparisonLatticeCompiler.compile_polynomial (hc name hn)).2.positive)
      (fun name hn => (ComparisonLatticeCompiler.compile_polynomial (hc name hn)).2.supported)
      (fun name hn => (ComparisonLatticeCompiler.compile_polynomial (hc name hn)).2.zero)
      (fun name hn => (ComparisonLatticeCompiler.compile_polynomial (hc name hn)).2.one)
  · intro name hn v hj hm
    exact Bool.eq_iff_iff.mpr
      ((ComparisonSignedSynthesis.polynomialValue_correct _ _).trans
        (ComparisonLatticeCompiler.compile_value (hc name hn) v hj hm))

/-- An actual shared image family and an original-context modality witness
make the executable simultaneous synthesis succeed. The mode action is only
used in the proof; the executable receives its quantified names, not its terms. -/
theorem run_complete (Δ : Bounds) (keys : List Nat) (types : List TypeVar)
    (names : List ModVar) (modeIds : List Nat) (count : Nat)
    (basis : ComparisonControls.Basis) (endpoints : List (Ty × Ty))
    (scalarSources : List ComparisonSignedEndpointQueries.Source)
    (hΔ : Δ.TypeBoundsDefined)
    (modes : ModVar → ModExpr) (images : Nat → CompareTy)
    (hi : ∀ name ∈ keys, ComparisonControls.LatticeForm basis.types (images name))
    (hfixed : ∀ v ∈ names, modes v = .var v)
    (hdomain : ∀ v, (∀ n ∈ modeIds, v ≠ .flex n) → modes v = .var v)
    (hscope : ∀ v ∈ Δ.modVars, v ∈ names)
    (himages : ∀ v ∈ extended names modeIds, ∀ w ∈ (modes v).vars, w ∈ names)
    (htotal : ∀ η, ModeModels Δ η → ∀ v, (modes v).WellFormed η)
    (he : ∀ pair ∈ endpoints,
      (∀ v ∈ pair.1.modVars, v ∈ extended names modeIds) ∧
      (∀ v ∈ pair.2.modVars, v ∈ extended names modeIds))
    (hw : ∀ pair ∈ endpoints,
      (ComparisonRankedDecision.instantiate keys images modes pair.1).DefinedUnder Δ ∧
      (ComparisonRankedDecision.instantiate keys images modes pair.2).DefinedUnder Δ ∧
      AlgebraSubtype Δ (ComparisonRankedDecision.instantiate keys images modes pair.1)
        (ComparisonRankedDecision.instantiate keys images modes pair.2))
    (hb : ∀ source ∈ scalarSources, source.Binary)
    (ha : ∀ source ∈ scalarSources, source.Allowed keys)
    (hv : ∀ family, ComparisonSignedSynthesis.Family (input keys basis) family →
      ∀ source ∈ scalarSources,
        source.Valid (fun _ => basis.types.length) family (SchemeModeSynthesis.strategy modes)) :
    ∃ threshold result, ∀ fuel ≥ threshold,
      run fuel Δ keys types names modeIds count basis endpoints scalarSources = .success result := by
  obtain ⟨family, hf, hr⟩ := family_exists images hi
  obtain ⟨n, q, hq⟩ := prepare_complete Δ keys types names modeIds count basis endpoints
  have hvalid := prepare_valid_witness (hq n le_rfl) hΔ modes images hfixed hscope
    himages htotal he hw hf hr
  obtain ⟨k, result, hs⟩ := ComparisonSignedEndpointQueries.run_complete_stable
    (input keys basis) ModalSynthesis.locality (SchemeModeSynthesis.atoms modeIds)
    (q :: scalarSources)
    (by simpa using And.intro (prepare_binary (hq n le_rfl)) hb)
    (by simpa [input] using And.intro (prepare_allowed (hq n le_rfl)) ha)
    hf (SchemeModeSynthesis.strategy_uniform hdomain)
    (by simpa [input] using And.intro hvalid (hv family hf))
  exact ⟨max n k, result, fun fuel hfu => by
    simp only [run, hq fuel ((le_max_left _ _).trans hfu), bind, RunResult.bind]
    exact hs fuel ((le_max_right _ _).trans hfu)⟩

end ModalityInference.ComparisonRankedModes
