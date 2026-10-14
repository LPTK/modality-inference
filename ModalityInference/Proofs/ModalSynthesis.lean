import ModalityInference.ModalSynthesis
import ModalityInference.Proofs.SymbolicCNF
import ModalityInference.Proofs.SymbolicSchemeModes
import ModalityInference.Proofs.CompactCNF
import Mathlib.Data.List.Enum

/-! Uniform synthesis over two independent coordinate domains. Clause selectors
are constants, whereas each reconstructed flexible atom depends only on the
rigid inputs in its own component. -/
namespace ModalityInference.ModalSynthesis

@[simp] theorem selector_even (v : Nat) : selector (2 * v) = false := by
  simp [selector]

@[simp] theorem selector_odd (v : Nat) : selector (2 * v + 1) = true := by
  simp [selector]

def encode (σ ρ : Nat → Bool) (v : Nat) : Bool :=
  if selector v then σ v else ρ (v / 2)

@[simp] theorem encode_even (σ ρ : Nat → Bool) (v : Nat) :
    encode σ ρ (2 * v) = ρ v := by simp [encode]

@[simp] theorem encode_odd (σ ρ : Nat → Bool) (v : Nat) :
    encode σ ρ (2 * v + 1) = σ (2 * v + 1) := by simp [encode]

@[simp] theorem decode_eval (σ ρ : Nat → Bool) (v : Nat) :
    (decode σ v).eval ρ = encode σ ρ v := by
  unfold decode encode
  split <;> rfl

@[simp] theorem prepare_part (side : Nat → Bool) (flex : List Nat) (cs : CNF) (b : Bool) :
    (prepare side flex cs).part b =
      SymbolicCNF.solve (pivots side b flex) (component side b cs) := by
  cases b <;> rfl

@[simp] theorem mem_pivots {side : Nat → Bool} {b : Bool} {flex : List Nat} {v : Nat} :
    2 * v ∈ pivots side b flex ↔ v ∈ flex ∧ side v = b := by
  simp only [pivots, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨w, hw, he⟩
    have he : w = v := by omega
    simpa [he] using hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem selector_not_pivot {side : Nat → Bool} {b : Bool} {flex : List Nat} {v : Nat}
    (h : selector v = true) : v ∉ pivots side b flex := by
  intro hv
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
  simp at h

theorem clause_component (side : Nat → Bool) (b : Bool) (c : Clause) (i : Nat)
    (σ : Nat → Bool) :
    ClauseHolds σ ((2 * i + 1, !b) ::
      ((c.filter fun l => side l.1 == b).map fun l => (2 * l.1, l.2))) ↔
      σ (2 * i + 1) = !b ∨
        ClauseHolds (fun v => σ (2 * v)) (c.filter fun l => side l.1 == b) := by
  rw [clauseHolds_cons]
  simp [ClauseHolds, List.mem_map, Prod.exists]

theorem component_holds (side : Nat → Bool) (b : Bool) (cs : CNF) (σ : Nat → Bool) :
    CNFHolds σ (component side b cs) ↔
      ∀ i (hi : i < cs.length), σ (2 * i + 1) = !b ∨
        ClauseHolds (fun v => σ (2 * v)) (cs[i].filter fun l => side l.1 == b) := by
  simp only [CNFHolds, component, List.forall_mem_map, List.forall_mem_zipIdx',
    clause_component]

theorem component_atoms {side : Nat → Bool} {b : Bool} {cs : CNF} {v : Nat}
    (h : v ∈ CNFPropagation.atoms (component side b cs)) :
    selector v = true ∨
      ∃ w, v = 2 * w ∧ side w = b ∧ w ∈ CNFPropagation.atoms cs := by
  obtain ⟨c, hc, p, hp⟩ := CNFPropagation.mem_atoms.mp h
  obtain ⟨⟨d, i⟩, hd, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_cons.mp hp with he | hm
  · have he := congrArg Prod.fst he
    change v = 2 * i + 1 at he
    exact .inl (by rw [he]; exact selector_odd i)
  · obtain ⟨⟨w, q⟩, hw, he⟩ := List.mem_map.mp hm
    have hw := List.mem_filter.mp hw
    cases he
    exact .inr ⟨w, rfl, by simpa using hw.2,
      CNFPropagation.mem_atoms.mpr ⟨d, List.fst_mem_of_mem_zipIdx hd, q, hw.1⟩⟩

theorem image_fixed {side : Nat → Bool} {flex : List Nat} {cs : CNF}
    {σ : Nat → Bool} {v : Nat} (h : v ∉ flex) :
    image side (prepare side flex cs) σ v = .atom v := by
  simp only [image, prepare_part]
  rw [SymbolicCNF.solve_fixed (by simpa using h)]
  simp [SymbolicCNF.substitute, decode]

theorem witness_substitute (side : Nat → Bool) (flex : List Nat) (cs : CNF)
    (σ : Nat → Bool) (v : Nat) :
    (witness side flex (prepare side flex cs) σ).substitute v =
      image side (prepare side flex cs) σ v := by
  cases hi : ConcreteBackend.atomFin flex v with
  | none =>
    have hv : v ∉ flex := by
      intro hv
      obtain ⟨i, he⟩ := HornPropagation.atomFin_exists hv
      simp [hi] at he
    simp [SymbolicModes.Elimination.substitute, hi, image_fixed hv]
  | some i =>
    have hv : flex[i.val] = v := ConcreteBackend.atomFin_lookup hi
    simp [SymbolicModes.Elimination.substitute, hi, witness, Vector.get, hv]

theorem image_eval (side : Nat → Bool) (p : Prepared) (σ ρ : Nat → Bool) (v : Nat) :
    (image side p σ v).eval ρ =
      SymbolicCNF.interpret (p.part (side v)).values (encode σ ρ) (2 * v) := by
  simp [image, SymbolicCNF.interpret]

theorem query_part {p : Prepared} {σ : Nat → Bool} (h : CNFHolds σ p.query) (b : Bool) :
    CNFHolds σ (SymbolicCNF.abstract selector (p.part b).residual) := by
  cases b
  · exact (cnfHolds_append _ _ _).mp h |>.2
  · exact (cnfHolds_append _ _ _).mp h |>.1

theorem query_component {side : Nat → Bool} {flex : List Nat} {cs : CNF}
    {σ : Nat → Bool} (h : CNFHolds σ (prepare side flex cs).query)
    (ρ : Nat → Bool) (b : Bool) :
    CNFHolds (SymbolicCNF.interpret ((prepare side flex cs).part b).values (encode σ ρ))
      (component side b cs) := by
  rw [prepare_part]
  apply (SymbolicCNF.solve_correct _ _ _).mp
  have hp := query_part h b
  rw [prepare_part] at hp
  exact (SymbolicCNF.abstract_correct _ _ _).mp hp _
    (fun v hv => by simp [encode, hv])

theorem query_sound {side : Nat → Bool} {flex : List Nat} {cs : CNF}
    {σ : Nat → Bool} (h : CNFHolds σ (prepare side flex cs).query)
    (ρ : Nat → Bool) :
    CNFHolds (fun v => (image side (prepare side flex cs) σ v).eval ρ) cs := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  let b := σ (2 * i + 1)
  have hp := (component_holds side b cs _).mp (query_component h ρ b) i hi
  have hfixed :
      SymbolicCNF.interpret ((prepare side flex cs).part b).values (encode σ ρ)
        (2 * i + 1) = b := by
    rw [prepare_part]
    simp [SymbolicCNF.interpret,
      SymbolicCNF.solve_fixed (selector_not_pivot (selector_odd i)), BoolExpr.eval, b]
  rcases hp with hp | hp
  · rw [hfixed] at hp
    cases b <;> simp at hp
  · obtain ⟨v, p, hv, he⟩ := hp
    obtain ⟨hv, hs⟩ := List.mem_filter.mp hv
    have hs : side v = b := by simpa using hs
    exact ⟨v, p, hv, by simpa only [image_eval, hs] using he⟩

theorem image_atoms {side : Nat → Bool} {flex : List Nat} {cs : CNF}
    {σ : Nat → Bool} {v w : Nat}
    (h : w ∈ (image side (prepare side flex cs) σ v).atoms) :
    side w = side v ∧ (v ∈ flex → w ∉ flex) := by
  by_cases hv : v ∈ flex
  · obtain ⟨u, hu, hw⟩ := SymbolicCNF.substitute_atoms h
    have hup : 2 * v ∈ pivots side (side v) flex := mem_pivots.mpr ⟨hv, rfl⟩
    rw [prepare_part] at hu
    obtain ⟨hua, hun⟩ := SymbolicCNF.solve_atoms hup hu
    have hus : selector u = false := by
      cases hs : selector u with
      | false => rfl
      | true => simp [decode, hs, BoolExpr.atoms] at hw
    have hwu : w = u / 2 := by simpa [decode, hus, BoolExpr.atoms] using hw
    rcases component_atoms hua with hs | ⟨x, rfl, hs, _⟩
    · simp [hus] at hs
    · have hwx : w = x := by simpa using hwu
      rw [hwx]
      exact ⟨hs, fun _ hx => hun (mem_pivots.mpr ⟨hx, hs⟩)⟩
  · rw [image_fixed hv] at h
    have hwv : w = v := by simpa [BoolExpr.atoms] using h
    exact ⟨hwv ▸ rfl, fun h => (hv h).elim⟩

theorem witness_atoms {side : Nat → Bool} {flex : List Nat} {cs : CNF}
    {σ : Nat → Bool} {v w : Nat}
    (h : w ∈ ((witness side flex (prepare side flex cs) σ).substitute v).atoms) :
    side w = side v ∧ (v ∈ flex → w ∉ flex) := by
  rw [witness_substitute] at h
  exact image_atoms h

theorem synthesizeCNF_sound {fuel flex cs result}
    (h : synthesizeCNF fuel flex cs = .success result) (ρ : Nat → Bool) :
    CNFHolds (fun v => (result.substitute v).eval ρ) cs := by
  unfold synthesizeCNF at h
  cases hs : CNFPropagation.solve fuel (CompactCNF.clean (prepare locality flex cs).query) <;>
    simp [hs, bind, pure, RunResult.bind] at h
  cases h
  simpa only [witness_substitute] using query_sound ((CompactCNF.clean_correct _ _).mp (CNFPropagation.solve_sound hs)) ρ

theorem synthesize_sound {fuel flex e result}
    (h : synthesize fuel flex e = .success result) (ρ : Nat → Bool) :
    e.eval (fun v => (result.substitute v).eval ρ) = true := by
  unfold synthesize at h
  cases hc : CompactCNF.toCNF fuel true e <;> simp [hc, bind, RunResult.bind] at h
  exact (CompactCNF.toCNF_correct hc _).mp (synthesizeCNF_sound h ρ)

theorem synthesizeCNF_support {fuel flex cs result}
    (h : synthesizeCNF fuel flex cs = .success result) {v w : Nat}
    (hw : w ∈ (result.substitute v).atoms) :
    locality w = locality v ∧ (v ∈ flex → w ∉ flex) := by
  unfold synthesizeCNF at h
  cases hs : CNFPropagation.solve fuel (CompactCNF.clean (prepare locality flex cs).query) <;>
    simp [hs, bind, pure, RunResult.bind] at h
  cases h
  exact witness_atoms hw

theorem synthesize_support {fuel flex e result}
    (h : synthesize fuel flex e = .success result) {v w : Nat}
    (hw : w ∈ (result.substitute v).atoms) :
    locality w = locality v ∧ (v ∈ flex → w ∉ flex) := by
  unfold synthesize at h
  cases hc : CompactCNF.toCNF fuel true e <;> simp [hc, bind, RunResult.bind] at h
  exact synthesizeCNF_support h hw

@[simp] theorem locality_atom_zero (v : ModVar) : locality (v.atomIndex 0) = true := by
  cases v <;> simp [locality, ModVar.atomIndex]

@[simp] theorem locality_atom_one (v : ModVar) : locality (v.atomIndex 1) = false := by
  cases v <;> simp [locality, ModVar.atomIndex, Nat.add_mod]

@[simp] theorem locality_atom_two (v : ModVar) : locality (v.atomIndex 2) = false := by
  cases v <;> simp [locality, ModVar.atomIndex, Nat.add_mod]

/-- Reification cannot fail after successful synthesis: all three images have
their legal support, including the affinity/uniqueness connection through closure. -/
theorem synthesize_reifies {fuel flex e result}
    (h : synthesize fuel flex e = .success result) (v : ModVar) :
    ∃ m, result.mode v = some m := by
  have hl : ∀ w ∈ (result.substitute (v.atomIndex 0)).atoms,
      SymbolicModes.Axis.Supports .locality w := by
    intro w hw
    have hs := (synthesize_support h hw).1
    rw [locality_atom_zero] at hs
    simpa [locality, SymbolicModes.Axis.Supports] using hs
  have ha : ∀ w ∈ (result.substitute (v.atomIndex 1)).atoms,
      SymbolicModes.Axis.Supports .affinity w := by
    intro w hw
    have hs := (synthesize_support h hw).1
    rw [locality_atom_one] at hs
    simpa [locality, SymbolicModes.Axis.Supports] using hs
  have hu : ∀ w ∈ (result.substitute (v.atomIndex 2)).atoms,
      SymbolicModes.Axis.Supports .uniqueness w := by
    intro w hw
    have hs := (synthesize_support h hw).1
    rw [locality_atom_two] at hs
    simpa [locality, SymbolicModes.Axis.Supports] using hs
  obtain ⟨l, hl⟩ := (SymbolicModes.reify_supported _ _).mpr hl
  obtain ⟨a, ha⟩ := (SymbolicModes.reify_supported _ _).mpr ha
  obtain ⟨u, hu⟩ := (SymbolicModes.reify_supported _ _).mpr hu
  exact ⟨.compose l (.compose a u), by simp [SymbolicModes.Elimination.mode, hl, ha, hu]⟩

/-- A family of assignments respects fixed parameters and depends on each
component's inputs alone. These are uniform strategies, not pointwise choices. -/
def Uniform (side : Nat → Bool) (flex : List Nat)
    (s : (Nat → Bool) → Nat → Bool) : Prop :=
  (∀ ρ v, v ∉ flex → s ρ v = ρ v) ∧
  ∀ ρ τ v, (∀ w, side w = side v → ρ w = τ w) → s ρ v = s τ v

theorem clause_factor {side : Nat → Bool} {flex : List Nat}
    {s : (Nat → Bool) → Nat → Bool} (hs : Uniform side flex s) {c : Clause}
    (h : ∀ ρ, ClauseHolds (s ρ) c) :
    (∀ ρ, ClauseHolds (s ρ) (c.filter fun l => side l.1 == true)) ∨
      (∀ ρ, ClauseHolds (s ρ) (c.filter fun l => side l.1 == false)) := by
  classical
  by_cases hl : ∀ ρ, ClauseHolds (s ρ) (c.filter fun l => side l.1 == true)
  · exact .inl hl
  · right
    intro τ
    by_contra ht
    obtain ⟨ρ, hρ⟩ := not_forall.mp hl
    let mixed : Nat → Bool := fun v => if side v then ρ v else τ v
    obtain ⟨v, b, hv, he⟩ := h mixed
    cases hd : side v with
    | false =>
      have heq := hs.2 mixed τ v (fun w hw => by simp [mixed, hw, hd])
      exact ht ⟨v, b, List.mem_filter.mpr ⟨hv, by simp [hd]⟩, heq.symm.trans he⟩
    | true =>
      have heq := hs.2 mixed ρ v (fun w hw => by simp [mixed, hw, hd])
      exact hρ ⟨v, b, List.mem_filter.mpr ⟨hv, by simp [hd]⟩, heq.symm.trans he⟩

theorem factor_selectors {side : Nat → Bool} {flex : List Nat}
    {s : (Nat → Bool) → Nat → Bool} (hs : Uniform side flex s) {cs : CNF}
    (h : ∀ ρ, CNFHolds (s ρ) cs) :
    ∃ σ, ∀ b ρ, CNFHolds (encode σ (s ρ)) (component side b cs) := by
  classical
  let σ : Nat → Bool := fun i => decide (∀ ρ,
    ClauseHolds (s ρ) (((cs[i / 2]?).getD []).filter fun l => side l.1 == true))
  refine ⟨σ, ?_⟩
  intro b ρ
  rw [component_holds]
  intro i hi
  have hσ : σ (2 * i + 1) = decide
      (∀ τ, ClauseHolds (s τ) (cs[i].filter fun l => side l.1 == true)) := by
    simp [σ, show (2 * i + 1) / 2 = i by omega, List.getElem?_eq_getElem hi]
  have hf := clause_factor hs (fun τ => h τ _ (List.getElem_mem hi))
  simp only [encode_odd, encode_even]
  cases b with
  | false =>
    by_cases hl : ∀ τ, ClauseHolds (s τ) (cs[i].filter fun l => side l.1 == true)
    · exact .inl (hσ.trans (decide_eq_true hl))
    · exact .inr ((hf.resolve_left hl) ρ)
  | true =>
    by_cases hl : ∀ τ, ClauseHolds (s τ) (cs[i].filter fun l => side l.1 == true)
    · exact .inr (hl ρ)
    · exact .inl (hσ.trans (decide_eq_false hl))

/-- Every uniform strategy induces consistent constant selectors. Universal
abstraction then records exactly their remaining requirements. -/
theorem query_complete {side : Nat → Bool} {flex : List Nat}
    {s : (Nat → Bool) → Nat → Bool} (hs : Uniform side flex s) {cs : CNF}
    (h : ∀ ρ, CNFHolds (s ρ) cs) :
    ∃ σ, CNFHolds σ (prepare side flex cs).query := by
  obtain ⟨σ, hσ⟩ := factor_selectors hs h
  have hp (b : Bool) :
      CNFHolds σ (SymbolicCNF.abstract selector ((prepare side flex cs).part b).residual) := by
    rw [prepare_part]
    apply (SymbolicCNF.abstract_correct _ _ _).mpr
    intro η hη
    let ρ : Nat → Bool := fun v => η (2 * v)
    have hm := SymbolicCNF.solve_preserves (pivots side b flex) (hσ b ρ)
    apply (CNFPropagation.holds_congr (τ := η) ?_).mp hm
    intro u hu
    obtain ⟨hua, hun⟩ := SymbolicCNF.solve_residual_atoms hu
    rcases component_atoms hua with hu | ⟨v, rfl, hv, _⟩
    · simpa [encode, hu] using (hη u hu).symm
    · have hvf : v ∉ flex := fun hvf => hun (mem_pivots.mpr ⟨hvf, hv⟩)
      rw [encode_even, hs.1 ρ v hvf]
  exact ⟨σ, (cnfHolds_append _ _ _).mpr ⟨hp true, hp false⟩⟩

theorem image_uniform (side : Nat → Bool) (flex : List Nat) (cs : CNF)
    (σ : Nat → Bool) :
    Uniform side flex (fun ρ v => (image side (prepare side flex cs) σ v).eval ρ) := by
  constructor
  · intro ρ v hv
    simp [image_fixed hv, BoolExpr.eval]
  · intro ρ τ v h
    exact SymbolicModes.eval_congr _ (fun w hw => h w (image_atoms hw).1)

/-- Selector consistency is exactly the existence of a dependency-respecting
uniform Boolean strategy, for an arbitrary input CNF. -/
theorem query_iff (side : Nat → Bool) (flex : List Nat) (cs : CNF) :
    (∃ σ, CNFHolds σ (prepare side flex cs).query) ↔
      ∃ s, Uniform side flex s ∧ ∀ ρ, CNFHolds (s ρ) cs := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨_, image_uniform side flex cs σ, query_sound hσ⟩
  · rintro ⟨s, hs, h⟩
    exact query_complete hs h

theorem synthesizeCNF_complete {flex : List Nat} {cs : CNF}
    {s : (Nat → Bool) → Nat → Bool} (hs : Uniform locality flex s)
    (h : ∀ ρ, CNFHolds (s ρ) cs) :
    ∃ n, ∀ fuel ≥ n, ∃ result, synthesizeCNF fuel flex cs = .success result := by
  obtain ⟨σ, hσ⟩ := query_complete hs h
  obtain ⟨n, hn⟩ := CNFPropagation.solve_complete ((CompactCNF.clean_correct _ _).mpr hσ)
  refine ⟨n, fun fuel hf => ?_⟩
  obtain ⟨values, hv⟩ := hn fuel hf
  exact ⟨witness locality flex (prepare locality flex cs) (CNFPropagation.valuation values),
    by simp [synthesizeCNF, hv, bind, pure, RunResult.bind]⟩

theorem synthesize_complete {flex : List Nat} {e : BoolExpr}
    {s : (Nat → Bool) → Nat → Bool} (hs : Uniform locality flex s)
    (h : ∀ ρ, e.eval (s ρ) = true) :
    ∃ n, ∀ fuel ≥ n, ∃ result, synthesize fuel flex e = .success result := by
  obtain ⟨n, cs, hc⟩ := CompactCNF.toCNF_complete e true
  have hm : ∀ ρ, CNFHolds (s ρ) cs := fun ρ => (CompactCNF.toCNF_correct (hc n le_rfl) _).mpr (h ρ)
  obtain ⟨m, hm⟩ := synthesizeCNF_complete hs hm
  refine ⟨n + m, fun fuel hf => ?_⟩
  obtain ⟨result, hr⟩ := hm fuel (by omega)
  exact ⟨result, by simp [synthesize, hc fuel (by omega), hr, bind, RunResult.bind]⟩

theorem synthesizeCNF_uniform {fuel flex cs result}
    (h : synthesizeCNF fuel flex cs = .success result) :
    Uniform locality flex (fun ρ v => (result.substitute v).eval ρ) := by
  unfold synthesizeCNF at h
  cases hs : CNFPropagation.solve fuel (CompactCNF.clean (prepare locality flex cs).query) <;>
    simp [hs, bind, pure, RunResult.bind] at h
  cases h
  simpa only [witness_substitute] using image_uniform locality flex cs _

theorem synthesize_uniform {fuel flex e result}
    (h : synthesize fuel flex e = .success result) :
    Uniform locality flex (fun ρ v => (result.substitute v).eval ρ) := by
  unfold synthesize at h
  cases hc : CompactCNF.toCNF fuel true e <;> simp [hc, bind, RunResult.bind] at h
  exact synthesizeCNF_uniform h

/-- The executable procedure accepts exactly the formulas having a uniform
strategy in the modality coordinate domains. -/
theorem synthesize_iff (flex : List Nat) (e : BoolExpr) :
    (∃ fuel result, synthesize fuel flex e = .success result) ↔
      ∃ s, Uniform locality flex s ∧ ∀ ρ, e.eval (s ρ) = true := by
  constructor
  · rintro ⟨fuel, result, h⟩
    exact ⟨_, synthesize_uniform h, synthesize_sound h⟩
  · rintro ⟨s, hs, h⟩
    obtain ⟨n, hn⟩ := synthesize_complete hs h
    obtain ⟨result, hr⟩ := hn n le_rfl
    exact ⟨n, result, hr⟩

theorem synthesizeCNF_monotone {n flex cs result}
    (h : synthesizeCNF n flex cs = .success result) :
    ∀ fuel ≥ n, synthesizeCNF fuel flex cs = .success result := by
  intro fuel hf
  unfold synthesizeCNF at h ⊢
  cases hs : CNFPropagation.solve n (CompactCNF.clean (prepare locality flex cs).query) <;>
    simp [hs, bind, pure, RunResult.bind] at h
  cases h
  simp [CNFPropagation.solve_monotone hs fuel hf, bind, pure, RunResult.bind]

theorem synthesize_monotone {n flex e result}
    (h : synthesize n flex e = .success result) :
    ∀ fuel ≥ n, synthesize fuel flex e = .success result := by
  intro fuel hf
  unfold synthesize at h ⊢
  cases hc : CompactCNF.toCNF n true e <;> simp [hc, bind, RunResult.bind] at h
  simp [CompactCNF.toCNF_monotone hc fuel hf, synthesizeCNF_monotone h fuel hf, bind, RunResult.bind]

theorem synthesizeCNF_terminates (flex : List Nat) (cs : CNF) :
    ∃ n, ∀ fuel ≥ n, synthesizeCNF fuel flex cs ≠ .exhausted := by
  obtain ⟨n, hn⟩ := CNFPropagation.solve_terminates (CompactCNF.clean (prepare locality flex cs).query)
  refine ⟨n, fun fuel hf => ?_⟩
  cases hs : CNFPropagation.solve fuel (CompactCNF.clean (prepare locality flex cs).query) <;>
    simp_all [synthesizeCNF, bind, pure, RunResult.bind]

theorem synthesize_terminates (flex : List Nat) (e : BoolExpr) :
    ∃ n, ∀ fuel ≥ n, synthesize fuel flex e ≠ .exhausted := by
  obtain ⟨n, cs, hc⟩ := CompactCNF.toCNF_complete e true
  obtain ⟨m, hm⟩ := synthesizeCNF_terminates flex cs
  refine ⟨n + m, fun fuel hf => ?_⟩
  simpa [synthesize, hc fuel (by omega), bind, RunResult.bind] using hm fuel (by omega)

/-- The existing finite substitution assembler is total for synthesized images. -/
theorem synthesize_assembles {fuel flex e result}
    (h : synthesize fuel flex e = .success result) (parameters : List (Nat × ModVar)) :
    ∃ σ, SymbolicSchemeModes.assemble result parameters = some σ := by
  apply (SymbolicSchemeModes.assemble_iff result parameters).mpr
  intro p _
  exact Option.isSome_iff_exists.mpr (synthesize_reifies h p.2)

theorem reify_excludes {fuel flex e result}
    (h : synthesize fuel flex e = .success result) {v : Nat} (hv : v ∈ flex)
    {axis m} (hr : SymbolicModes.reify axis (result.substitute v) = some m) {w : ModVar}
    (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ m.vars := by
  intro hm
  obtain ⟨i, hi, he⟩ := SymbolicModes.reify_variables hr w hm
  apply (synthesize_support h hi).2 hv
  have ha := hw (i % 3) (Nat.mod_lt _ (by decide))
  rwa [← he, SymbolicSchemeModes.atomVariable_reencode] at ha

theorem mode_excludes {fuel flex e result}
    (h : synthesize fuel flex e = .success result) {v m} (hm : result.mode v = some m)
    (hv : ∀ a < 3, v.atomIndex a ∈ flex) {w : ModVar}
    (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ m.vars := by
  cases hl : SymbolicModes.reify .locality (result.substitute (v.atomIndex 0)) <;>
    cases ha : SymbolicModes.reify .affinity (result.substitute (v.atomIndex 1)) <;>
    cases hu : SymbolicModes.reify .uniqueness (result.substitute (v.atomIndex 2)) <;>
    simp [SymbolicModes.Elimination.mode, hl, ha, hu] at hm
  cases hm
  simp only [ModExpr.vars, Finset.mem_union, not_or]
  exact ⟨reify_excludes h (hv 0 (by decide)) hl hw,
    reify_excludes h (hv 1 (by decide)) ha hw,
    reify_excludes h (hv 2 (by decide)) hu hw⟩

theorem assemble_excludes {fuel flex e result parameters σ key v}
    (he : synthesize fuel flex e = .success result)
    (ha : SymbolicSchemeModes.assemble result parameters = some σ)
    (hv : parameters.lookup key = some v)
    (hcoords : ∀ a < 3, v.atomIndex a ∈ flex) {w : ModVar}
    (hw : ∀ a < 3, w.atomIndex a ∈ flex) : w ∉ (σ.mode (.flex key)).vars :=
  mode_excludes he (SymbolicSchemeModes.assemble_action ha hv) hcoords hw

end ModalityInference.ModalSynthesis
