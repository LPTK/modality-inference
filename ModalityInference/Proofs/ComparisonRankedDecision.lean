import ModalityInference.ComparisonRankedDecision
import ModalityInference.Proofs.ComparisonSignedEndpoints
import ModalityInference.Proofs.ComparisonObserverMachineFormula
import ModalityInference.Proofs.ComparisonSignedQuerySolver
import ModalityInference.Proofs.ComparisonStructuralLayout
import ModalityInference.Proofs.ComparisonLatticeCompiler
import ModalityInference.Proofs.ComparisonRankedTermination

namespace ModalityInference.ComparisonRankedDecision

open ComparisonSignedEndpoints ComparisonObserverMachineFormula
  ComparisonStructuralLayout

theorem call_injective : Function.Injective (fun p : Nat × Nat => call p.1 p.2) := by
  intro p q h
  exact Prod.ext (congrArg Call.name h)
    (by simpa [call] using congrArg (fun c => c.route.length) h)

theorem choices_correct {α : Type} (fallback : α) (test : α → BoolExpr)
    (branches : α → List Branch) (values : α → Bool)
    (world : Nat → Bool) (images : Call → Bool)
    (h : ∀ i, Represents world images (branches i) (values i)) (xs : List α) :
    Represents world images (choices fallback test branches xs)
      (values (firstTrue fallback (fun i => (test i).eval world) xs)) := by
  induction xs with
  | nil => exact h fallback
  | cons i xs ih =>
    simpa only [choices, choice, firstTrue, apply_ite] using
      Represents.choice (h i) ih (test i)

theorem action_clamp {count} (names : List ModVar) (d : Fields count)
    (m : ModExpr) (x : BoolExpr) (world : Nat → Bool) :
    (action names d m x).eval world =
      ((x.eval world || (action names d m (.const false)).eval world) &&
        (action names d m (.const true)).eval world) := by
  simp only [action, mux_eval, BoolExpr.eval]
  cases (modesFormula names d m.project.defined).eval world <;>
    cases d.first.eval world <;> cases d.second.eval world <;> simp

theorem observe_reads {count} (keys : List Nat) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (modes : ModVar → ModExpr)
    (world : Nat → Bool) (images : Nat → CompareTy) (calls : Call → Bool)
    (hreads : ∀ name ∈ keys, ∀ i : Fin count, calls (call name i) =
      (value types names data (images name) i).eval world) (a : Ty) (i : Fin count) :
    Represents world calls
      (observe keys types names data modes a i)
      ((value types names data (instantiate keys images modes a) i).eval world) := by
  induction a generalizing i with
  | fn a b iha ihb =>
    simpa only [observe, choice, next, dual, instantiate, CompareTy.ofTy, CompareTy.subst,
      value, mux_eval, successor_eval, BoolExpr.eval, Bool.or_false, decode] using
      Represents.choice
        (choices_correct i ((data i).next .fn) _ _ world _ iha (List.finRange count)).dual
        (choices_correct i ((data i).next .fn) _ _ world _ ihb (List.finRange count))
        ((data i).left .fn)
  | var v =>
    cases v with
    | rigid n => exact Represents.base world _ _
    | flex n =>
      by_cases hn : n ∈ keys <;> simp [observe, reference, instantiate, imageTypes, CompareTy.ofTy,
        CompareTy.subst, Represents, value, Data.eval, BoolExpr.eval, hn, hreads]
  | unit => exact Represents.base world _ _
  | credit => exact Represents.base world _ _
  | prod a b iha ihb =>
    simpa only [observe, choice, next, instantiate, CompareTy.ofTy, CompareTy.subst,
      value, mux_eval, successor_eval, decode] using
      Represents.choice
        (choices_correct i ((data i).next .prod) _ _ world _ iha (List.finRange count))
        (choices_correct i ((data i).next .prod) _ _ world _ ihb (List.finRange count))
        ((data i).left .prod)
  | sum a b iha ihb =>
    simpa only [observe, choice, next, instantiate, CompareTy.ofTy, CompareTy.subst,
      value, mux_eval, successor_eval, decode] using
      Represents.choice
        (choices_correct i ((data i).next .sum) _ _ world _ iha (List.finRange count))
        (choices_correct i ((data i).next .sum) _ _ world _ ihb (List.finRange count))
        ((data i).left .sum)
  | modal a m ih =>
    change Represents _ _ _
      ((action names (data i) (m.subst modes)
        (value types names data (instantiate keys images modes a) i)).eval world)
    rw [action_clamp]
    exact (ih i).act _ _

theorem compile_reads {count} (keys : List Nat) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (modes : ModVar → ModExpr)
    (left right : Ty) (i : Fin count) (world : Nat → Bool) (images : Nat → CompareTy)
    (calls : Call → Bool) (hreads : ∀ name ∈ keys, ∀ i : Fin count, calls (call name i) =
      (value types names data (images name) i).eval world) :
    (∀ clause ∈ compile keys types names data modes left right i,
      clause.Holds world calls) ↔
      (value types names data (instantiate keys images modes left) i).eval world ≤
        (value types names data (instantiate keys images modes right) i).eval world := by
  simp only [compile, List.forall_mem_flatMap, compare_correct, BoolExpr.eval,
    Bool.and_eq_true, Bool.le_iff_imp]
  have hl := observe_reads keys types names data modes world images calls hreads left i
  have hr := observe_reads keys types names data modes world images calls hreads right i
  constructor
  · intro h hleft
    obtain ⟨l, hll, hla⟩ := hl.1
    obtain ⟨r, hrr, hra⟩ := hr.1
    have hh := h l hll r hrr ⟨hla, hra⟩
    rw [hl.2 l hll hla, hr.2 r hrr hra] at hh
    exact hh hleft
  · intro h l hll r hrr ha
    rw [hl.2 l hll ha.1, hr.2 r hrr ha.2]
    exact h

theorem choice_allowed {keys : List Nat} {test : BoolExpr} {left right : List Branch}
    (hl : ∀ b ∈ left, b.view.data.Allowed keys)
    (hr : ∀ b ∈ right, b.view.data.Allowed keys)
    {b : Branch} (hb : b ∈ choice test left right) : b.view.data.Allowed keys := by
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨b, ho, rfl⟩ := List.mem_map.mp h
    exact hl b ho
  · obtain ⟨b, ho, rfl⟩ := List.mem_map.mp h
    exact hr b ho

theorem choices_allowed {α : Type} {keys : List Nat} (fallback : α) (test : α → BoolExpr)
    (branches : α → List Branch) (h : ∀ i b, b ∈ branches i → b.view.data.Allowed keys)
    (xs : List α) {b : Branch} (hb : b ∈ choices fallback test branches xs) :
    b.view.data.Allowed keys := by
  induction xs generalizing b with
  | nil => exact h fallback b hb
  | cons i xs ih => exact choice_allowed (h i) (fun _ => ih) hb

theorem observe_allowed {count} {keys : List Nat} {types : List TypeVar} {names : List ModVar}
    {data : Fin count → Fields count} {modes : ModVar → ModExpr}
    {a : Ty} {i : Fin count} {b : Branch}
    (hb : b ∈ observe keys types names data modes a i) : b.view.data.Allowed keys := by
  induction a generalizing i b with
  | var v =>
    cases List.mem_singleton.mp hb
    cases v <;> simp only [reference, View.base]
    · split
      · simpa only [Data.Allowed, List.contains_iff_mem] using ‹keys.contains _ = true›
      · trivial
    · trivial
  | unit | credit => cases List.mem_singleton.mp hb; trivial
  | prod a c iha ihc | sum a c iha ihc =>
    exact choice_allowed
      (fun _ h => choices_allowed _ _ _ (fun _ _ => iha) _ h)
      (fun _ h => choices_allowed _ _ _ (fun _ _ => ihc) _ h) hb
  | fn a c iha ihc =>
    apply choice_allowed ?_ (fun _ h => choices_allowed _ _ _ (fun _ _ => ihc) _ h) hb
    intro b h
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp h
    exact Data.flip_allowed (choices_allowed _ _ _ (fun _ _ => iha) _ ho)
  | modal a m ih =>
    obtain ⟨original, ho, rfl⟩ := List.mem_map.mp hb
    exact ih (b := original) ho

theorem compile_binary {count} {keys : List Nat} {types : List TypeVar} {names : List ModVar}
    {data : Fin count → Fields count} {modes : ModVar → ModExpr} {left right : Ty}
    {i : Fin count} {c : ComparisonSignedEndpoints.Clause}
    (hc : c ∈ compile keys types names data modes left right i) : c.literals.length ≤ 2 := by
  obtain ⟨_, _, h⟩ := List.mem_flatMap.mp hc
  obtain ⟨_, _, h⟩ := List.mem_flatMap.mp h
  exact compare_binary h

theorem compile_allowed {count} {keys : List Nat} {types : List TypeVar} {names : List ModVar}
    {data : Fin count → Fields count} {modes : ModVar → ModExpr} {left right : Ty}
    {i : Fin count} {c : ComparisonSignedEndpoints.Clause}
    (hc : c ∈ compile keys types names data modes left right i)
    {literal : Call × Bool} (hl : literal ∈ c.literals) : literal.1.name ∈ keys := by
  obtain ⟨_, ha, h⟩ := List.mem_flatMap.mp hc
  obtain ⟨_, hb, h⟩ := List.mem_flatMap.mp h
  exact compare_allowed (observe_allowed ha) (observe_allowed hb) h hl

theorem decode_mapFields {count} (data : Fin count → Fields count) (f : Nat → Nat)
    (world : Nat → Bool) :
    decode (fun i => mapFields (ComparisonStructuralLayout.rename f) (data i)) world =
      decode data (world ∘ f) := by
  funext i
  simp [decode, mapFields, scalar, rename_eval, List.map_map, Function.comp_def]

theorem machineData_value {count} (types : List TypeVar) (names : List ModVar)
    (world : Nat → Bool) (a : CompareTy) (i : Fin count) :
    (value types names (machineData types names count) a i).eval world =
      (value types names
        (ComparisonObserverMachineEncoding.allocate types.length names.length count) a i).eval
        (world ∘ (2 * ·)) := by
  simpa only [value_eval] using congrArg
    (fun d => ComparisonObserverMachine.value (ComparisonObserverMachineCheck.nodes types names d) a i)
    (decode_mapFields
      (ComparisonObserverMachineEncoding.allocate types.length names.length count) (2 * ·) world)

def extend (input : ComparisonSignedSynthesis.Input) (types : List TypeVar)
    (names : List ModVar) (count : Nat) (world : Nat → Bool) (v : Nat) : Bool :=
  if v % 2 = 0 then world (v / 2) else
    let key := Nat.unpair (v / 2)
    let point := Nat.unpair key.2
    if h : point.1 < count then
      (value types names
        (ComparisonObserverMachineEncoding.allocate types.length names.length count)
        ((input.bases key.1)[point.2]?.getD .unit) ⟨point.1, h⟩).eval world
    else false

@[simp] theorem extend_even (input : ComparisonSignedSynthesis.Input) (types : List TypeVar)
    (names : List ModVar) (count : Nat) (world : Nat → Bool) (v : Nat) :
    extend input types names count world (2 * v) = world v := by
  simp [extend]

theorem extend_machine (input : ComparisonSignedSynthesis.Input) (types : List TypeVar)
    (names : List ModVar) (count : Nat) (world : Nat → Bool) :
    extend input types names count world ∘ (2 * ·) = world := by
  funext v
  exact extend_even input types names count world v

theorem extend_payload (input : ComparisonSignedSynthesis.Input) (types : List TypeVar)
    (names : List ModVar) (count : Nat) (world : Nat → Bool) (name index : Nat)
    (i : Fin count) :
    extend input types names count world (payload (call name i) index) =
      (value types names
        (ComparisonObserverMachineEncoding.allocate types.length names.length count)
        ((input.bases name)[index]?.getD .unit) i).eval world := by
  simp [extend, payload, call, i.isLt]

private theorem all_holds (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all es).eval world = true ↔ ∀ e ∈ es, e.eval world = true := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

theorem payloadTheory_correct {count} (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (data : Fin count → Fields count)
    (world : Nat → Bool) :
    (payloadTheory input types names data).eval world = true ↔
      ∀ name ∈ input.keys, ∀ i : Fin count, ∀ index, ∀ h : index < (input.bases name).length,
        world (payload (call name i) index) =
          (value types names data (input.bases name)[index] i).eval world := by
  rw [payloadTheory, all_holds]
  simp only [List.forall_mem_flatMap, List.forall_mem_map, List.forall_mem_zipIdx',
    List.mem_finRange, forall_const, equal_eval, BoolExpr.eval, beq_iff_eq]

theorem extend_theory (Δ : Bounds) (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (count : Nat) (world : Nat → Bool) :
    (theory Δ input types names (machineData types names count)).eval
      (extend input types names count world) =
    (query Δ types names
      (ComparisonObserverMachineEncoding.allocate types.length names.length count)).eval world := by
  have hp : (payloadTheory input types names (machineData types names count)).eval
      (extend input types names count world) = true := by
    apply (payloadTheory_correct _ _ _ _ _).mpr
    intro name _ i index h
    rw [extend_payload, machineData_value, extend_machine]
    simp [List.getElem?_eq_getElem h]
  simp only [theory, BoolExpr.eval, hp, Bool.and_true, query_eval]
  change ComparisonObserverMachineCheck.check Δ types names
    (decode (fun i => mapFields (rename (2 * ·))
      (ComparisonObserverMachineEncoding.allocate types.length names.length count i))
      (extend input types names count world)) = _
  rw [decode_mapFields, extend_machine]

theorem prepare_spec {fuel Δ input types names count modes endpoints q}
    (h : prepare fuel Δ input types names count modes endpoints = .success q) :
    ∃ original required,
      CompactCNF.toCNF fuel true (theory Δ input types names (machineData types names count)) =
        .success original ∧
      compileGuards fuel (clauses input.keys types names (machineData types names count)
        modes endpoints) = .success required ∧
      q = ⟨payload, Sum.inr, original, required⟩ := by
  cases ht : CompactCNF.toCNF fuel true
      (theory Δ input types names (machineData types names count)) <;>
    simp [prepare, ht, bind, RunResult.bind] at h
  rename_i original
  cases hc : compileGuards fuel (clauses input.keys types names (machineData types names count)
      modes endpoints) <;> simp [hc, pure] at h
  subst q
  exact ⟨original, _, rfl, rfl, rfl⟩

theorem prepare_complete (Δ : Bounds) (input : ComparisonSignedSynthesis.Input)
    (types : List TypeVar) (names : List ModVar) (count : Nat)
    (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) :
    ∃ threshold q, ∀ fuel ≥ threshold,
      prepare fuel Δ input types names count modes endpoints = .success q := by
  obtain ⟨n, original, ht⟩ := CompactCNF.toCNF_complete
    (theory Δ input types names (machineData types names count)) true
  obtain ⟨k, required, hc⟩ := compileGuards_complete
    (clauses input.keys types names (machineData types names count) modes endpoints)
  exact ⟨max n k, ⟨payload, Sum.inr, original, required⟩, fun fuel hf => by
    simp [prepare, ht fuel ((le_max_left _ _).trans hf),
      hc fuel ((le_max_right _ _).trans hf), bind, pure, RunResult.bind]⟩

theorem prepare_binary {fuel Δ input types names count modes endpoints q}
    (h : prepare fuel Δ input types names count modes endpoints = .success q)
    {c : CompiledClause} (hc : c ∈ q.clauses) : c.literals.length ≤ 2 := by
  obtain ⟨original, required, _, hr, rfl⟩ := prepare_spec h
  obtain ⟨c, hc, he⟩ := compileGuards_origin hr hc
  obtain ⟨pair, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  rw [he]
  exact compile_binary hc

theorem prepare_allowed {fuel Δ input types names count modes endpoints q}
    (h : prepare fuel Δ input types names count modes endpoints = .success q) :
    q.Allowed input.keys := by
  obtain ⟨original, required, _, hr, rfl⟩ := prepare_spec h
  intro c hc literal hl
  obtain ⟨c, hc, he⟩ := compileGuards_origin hr hc
  obtain ⟨pair, _, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨i, _, hc⟩ := List.mem_flatMap.mp hc
  exact compile_allowed hc (he ▸ hl)

theorem prepare_valid {fuel Δ input types names count modes endpoints q}
    (h : prepare fuel Δ input types names count modes endpoints = .success q)
    (p : Nat → Bool) (family : Nat → (Nat → Bool) → Bool) :
    q.Valid p family ↔
      ∀ world, (theory Δ input types names (machineData types names count)).eval world = true →
        ∀ c ∈ clauses input.keys types names (machineData types names count) modes endpoints,
          c.Holds world (fun call => family call.name (fun index => world (payload call index))) := by
  obtain ⟨original, required, ht, hr, rfl⟩ := prepare_spec h
  simp only [ComparisonSignedQueries.Query.Valid, ComparisonSignedEdges.decoded]
  exact forall_congr' fun world =>
    imp_congr (CompactCNF.toCNF_correct ht world)
      (compileGuards_correct hr world _)

/-- One polynomial family has the indicated image values under every lattice
evaluation. This is derived below from the finite image compiler. -/
def Realizes (input : ComparisonSignedSynthesis.Input)
    (family : Nat → (Nat → Bool) → Bool) (images : Nat → CompareTy) : Prop :=
  ∀ name ∈ input.keys, ∀ v : CompareTy → Bool,
    (∀ a b, v (.join a b) = (v a || v b)) →
    (∀ a b, v (.meet a b) = (v a && v b)) →
    family name (ComparisonPropagation.basisValue (input.bases name) v) = v (images name)

theorem theory_reads {count} {input : ComparisonSignedSynthesis.Input}
    {types : List TypeVar} {names : List ModVar} {data : Fin count → Fields count}
    {world : Nat → Bool} {family : Nat → (Nat → Bool) → Bool} {images : Nat → CompareTy}
    (hf : ComparisonSignedSynthesis.Family input family) (hr : Realizes input family images)
    (ht : (payloadTheory input types names data).eval world = true)
    {name : Nat} (hn : name ∈ input.keys) (i : Fin count) :
    family name (fun index => world (payload (call name i) index)) =
      (value types names data (images name) i).eval world := by
  rw [hf.congr hn (b := ComparisonPropagation.basisValue (input.bases name)
    (fun a => (value types names data a i).eval world)) (fun index h => by
      simpa [ComparisonPropagation.basisValue, List.getElem?_eq_getElem h] using
        (payloadTheory_correct input types names data world).mp ht name hn i index h)]
  exact hr name hn _ (fun _ _ => rfl) (fun _ _ => rfl)

theorem prepare_endpoints {fuel Δ input types names count modes endpoints q}
    (h : prepare fuel Δ input types names count modes endpoints = .success q)
    (p : Nat → Bool) {family : Nat → (Nat → Bool) → Bool} {images : Nat → CompareTy}
    (hf : ComparisonSignedSynthesis.Family input family) (hr : Realizes input family images) :
    q.Valid p family ↔ ∀ world,
      (theory Δ input types names (machineData types names count)).eval world = true →
      ∀ pair ∈ endpoints, ∀ i : Fin count,
        (value types names (machineData types names count)
          (instantiate input.keys images modes pair.1) i).eval world ≤
        (value types names (machineData types names count)
          (instantiate input.keys images modes pair.2) i).eval world := by
  rw [prepare_valid h]
  apply forall_congr' fun world => imp_congr_right fun ht => ?_
  have hp : (payloadTheory input types names (machineData types names count)).eval world = true := by
    simp only [theory, BoolExpr.eval, Bool.and_eq_true] at ht
    exact ht.2
  simp only [clauses, List.forall_mem_flatMap, List.mem_finRange, forall_const]
  exact forall_congr' fun pair => imp_congr_right fun _ => forall_congr' fun i =>
    compile_reads input.keys types names (machineData types names count) modes pair.1 pair.2 i
      world images _ (fun _ hn i => theory_reads hf hr hp hn i)

def MachineValid (Δ : Bounds) (keys : List Nat) (types : List TypeVar) (names : List ModVar)
    (count : Nat) (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty))
    (images : Nat → CompareTy) : Prop :=
  ∀ world,
    (query Δ types names
      (ComparisonObserverMachineEncoding.allocate types.length names.length count)).eval world = true →
    ∀ pair ∈ endpoints, ∀ i : Fin count,
      (value types names (ComparisonObserverMachineEncoding.allocate types.length names.length count)
        (instantiate keys images modes pair.1) i).eval world ≤
      (value types names (ComparisonObserverMachineEncoding.allocate types.length names.length count)
        (instantiate keys images modes pair.2) i).eval world

theorem prepare_machine_iff {fuel Δ input types names count modes endpoints q}
    (h : prepare fuel Δ input types names count modes endpoints = .success q)
    (p : Nat → Bool) {family : Nat → (Nat → Bool) → Bool} {images : Nat → CompareTy}
    (hf : ComparisonSignedSynthesis.Family input family) (hr : Realizes input family images) :
    q.Valid p family ↔ MachineValid Δ input.keys types names count modes endpoints images := by
  rw [prepare_endpoints h p hf hr]
  constructor
  · intro hv world hw pair hp i
    have ht := hv (extend input types names count world)
      ((extend_theory Δ input types names count world).trans hw) pair hp i
    simpa only [machineData_value, extend_machine] using ht
  · intro hv world ht pair hp i
    have hm : (query Δ types names
        (ComparisonObserverMachineEncoding.allocate types.length names.length count)).eval
        (world ∘ (2 * ·)) = true := by
      have hq : (query Δ types names (machineData types names count)).eval world = true := by
        simp only [theory, BoolExpr.eval, Bool.and_eq_true] at ht
        exact ht.1
      rw [query_eval] at hq
      simpa only [query_eval] using
        (show ComparisonObserverMachineCheck.check Δ types names
          (decode (ComparisonObserverMachineEncoding.allocate types.length names.length count)
            (world ∘ (2 * ·))) = true from
          (decode_mapFields _ (2 * ·) world) ▸ hq)
    simpa only [machineData_value] using hv (world ∘ (2 * ·)) hm pair hp i

/-- Every finite lattice-image witness at the supplied basis is accepted at
all sufficiently large fuel, with one unchanged modality substitution. -/
theorem run_complete (Δ : Bounds) (keys : List Nat)
    (bases : Nat → ComparisonControls.Basis) (types : List TypeVar) (names : List ModVar)
    (count : Nat) (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty))
    (images : Nat → CompareTy)
    (hi : ∀ name ∈ keys, ComparisonControls.LatticeForm (bases name).types (images name))
    (hv : MachineValid Δ keys types names count modes endpoints images) :
    ∃ threshold result, ∀ fuel ≥ threshold,
      run fuel Δ ⟨keys, fun name => (bases name).types⟩ types names count modes endpoints =
        .success result := by
  let input : ComparisonSignedSynthesis.Input := ⟨keys, fun name => (bases name).types⟩
  let polys (name : Nat) : CNF := (ComparisonLatticeCompiler.compile (bases name) (images name)).getD []
  have hc (name : Nat) (hn : name ∈ keys) :
      ComparisonLatticeCompiler.compile (bases name) (images name) = some (polys name) := by
    obtain ⟨cs, hcs⟩ := ComparisonLatticeCompiler.compile_complete (hi name hn)
    simp [polys, hcs]
  have hf : ComparisonSignedSynthesis.Family input
      (fun name => ComparisonSignedSynthesis.polynomialValue (polys name)) :=
    ComparisonSignedSynthesis.polynomial_family input polys
      (fun name hn => (ComparisonLatticeCompiler.compile_polynomial (hc name hn)).2.positive)
      (fun name hn => (ComparisonLatticeCompiler.compile_polynomial (hc name hn)).2.supported)
      (fun name hn => (ComparisonLatticeCompiler.compile_polynomial (hc name hn)).2.zero)
      (fun name hn => (ComparisonLatticeCompiler.compile_polynomial (hc name hn)).2.one)
  have hr : Realizes input
      (fun name => ComparisonSignedSynthesis.polynomialValue (polys name)) images := by
    intro name hn v hj hm
    exact Bool.eq_iff_iff.mpr
      ((ComparisonSignedSynthesis.polynomialValue_correct _ _).trans
        (ComparisonLatticeCompiler.compile_value (hc name hn) v hj hm))
  obtain ⟨n, q, hq⟩ := prepare_complete Δ input types names count modes endpoints
  have hvalid := (prepare_machine_iff (hq n le_rfl) (fun _ => false) hf hr).mpr hv
  obtain ⟨k, result, hs⟩ := ComparisonSignedQuerySolver.run_complete_stable input [q] []
    (by simpa using fun c hc => prepare_binary (hq n le_rfl) (c := c) hc)
    (by simpa using prepare_allowed (hq n le_rfl))
    hf (by simpa using hvalid) (by simp [CNFHolds])
  exact ⟨max n k, result, fun fuel hfu => by
    change run fuel Δ input types names count modes endpoints = _
    simp only [run, hq fuel ((le_max_left _ _).trans hfu), bind, RunResult.bind]
    exact hs fuel ((le_max_right _ _).trans hfu)⟩

theorem selected_mem {images : List (Nat × CompareTy)} {name : Nat}
    (hn : name ∈ images.map Prod.fst) : (name, selected images name) ∈ images := by
  cases hl : images.lookup name with
  | none =>
    obtain ⟨pair, hp, he⟩ := List.mem_map.mp hn
    have hh := List.lookup_eq_none_iff.mp hl pair hp
    simp [he] at hh
  | some a =>
    obtain ⟨before, after, he, _⟩ := List.lookup_eq_some_iff.mp hl
    simp only [selected, hl, Option.getD_some]
    simp [he]

theorem run_spec {fuel Δ input types names count modes endpoints result}
    (h : run fuel Δ input types names count modes endpoints = .success result) :
    ∃ q, prepare fuel Δ input types names count modes endpoints = .success q ∧
      ComparisonSignedQuerySolver.run fuel input [q] [] = .success result := by
  cases hp : prepare fuel Δ input types names count modes endpoints <;>
    simp [run, hp, bind, RunResult.bind] at h
  exact ⟨_, rfl, h⟩

/-- Returned images are finite lattice terms over their original bases and
jointly satisfy all machine endpoint obligations. No modality guard is added
to the original observation theory. -/
theorem run_sound {fuel Δ input types names count modes endpoints result}
    (h : run fuel Δ input types names count modes endpoints = .success result) :
    result.images.map Prod.fst = input.keys ∧
      (∀ image ∈ result.images, ComparisonControls.LatticeForm (input.bases image.1) image.2) ∧
      MachineValid Δ input.keys types names count modes endpoints (selected result.images) := by
  obtain ⟨q, hq, hs⟩ := run_spec h
  obtain ⟨r, _, hreconstruct, _, hkeys, hf, hv⟩ :=
    ComparisonSignedQuerySolver.run_sound (by simpa using prepare_allowed hq) hs
  have hr : Realizes input
      (input.imageValue r (CNFPropagation.valuation result.selectors)) (selected result.images) := by
    intro name hn v hj hm
    exact (input.reconstruct_value hreconstruct
      (selected_mem (hkeys.symm ▸ hn)) v hj hm).symm
  refine ⟨hkeys, ?_, (prepare_machine_iff hq _ hf hr).mp (hv q (by simp))⟩
  intro image hi
  exact ComparisonSignedPolynomials.reconstruct_property
    ((input.reconstruct_spec hreconstruct).2 image hi)
    (ComparisonControls.LatticeForm (input.bases image.1))
    (fun _ => ComparisonControls.LatticeForm.atom)
    (fun _ _ => ComparisonControls.LatticeForm.join)
    (fun _ _ => ComparisonControls.LatticeForm.meet)

theorem run_success_iff (Δ : Bounds) (keys : List Nat)
    (bases : Nat → ComparisonControls.Basis) (types : List TypeVar) (names : List ModVar)
    (count : Nat) (modes : ModVar → ModExpr) (endpoints : List (Ty × Ty)) :
    (∃ fuel result,
      run fuel Δ ⟨keys, fun name => (bases name).types⟩ types names count modes endpoints =
        .success result) ↔
    ∃ images : Nat → CompareTy,
      (∀ name ∈ keys, ComparisonControls.LatticeForm (bases name).types (images name)) ∧
      MachineValid Δ keys types names count modes endpoints images := by
  constructor
  · rintro ⟨fuel, result, h⟩
    obtain ⟨hkeys, hi, hv⟩ := run_sound h
    exact ⟨selected result.images, fun name hn => hi _ (selected_mem (hkeys.symm ▸ hn)), hv⟩
  · rintro ⟨images, hi, hv⟩
    obtain ⟨n, result, hn⟩ := run_complete Δ keys bases types names count modes endpoints images hi hv
    exact ⟨n, result, hn n le_rfl⟩

/-- Rejection excludes every finite polynomial family at this basis and
strategy, not merely the particular family attempted by reconstruction. -/
theorem run_rejects {fuel Δ keys types names count modes endpoints message}
    {bases : Nat → ComparisonControls.Basis}
    (h : run fuel Δ ⟨keys, fun name => (bases name).types⟩ types names count modes endpoints =
      .rejected message) :
    ¬ ∃ images : Nat → CompareTy,
      (∀ name ∈ keys, ComparisonControls.LatticeForm (bases name).types (images name)) ∧
      MachineValid Δ keys types names count modes endpoints images := by
  rintro ⟨images, hi, hv⟩
  obtain ⟨n, result, hn⟩ := run_complete Δ keys bases types names count modes endpoints images hi hv
  have hr := run_stable h (by simp) (le_max_left fuel n)
  have hs := hn (max fuel n) (le_max_right fuel n)
  rw [hr] at hs
  cases hs

end ModalityInference.ComparisonRankedDecision
