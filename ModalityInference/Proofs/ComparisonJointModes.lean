import ModalityInference.ComparisonJointModes
import ModalityInference.Proofs.ModalSynthesis

/-! Scalar components with shared constant selectors preserve uniform strategies,
including their support and exact symbolic reification. -/
namespace ModalityInference.ComparisonJointModes

open ModalSynthesis

/-- A component mentions selectors and coordinates from its own dependency side. -/
def ComponentSupported (side : Nat → Bool) (b : Bool) (cs : CNF) : Prop :=
  ∀ v ∈ CNFPropagation.atoms cs, selector v = true ∨
    ∃ w, v = 2 * w ∧ side w = b

@[simp] theorem prepare_part (side : Nat → Bool) (flex : List Nat)
    (locality other : CNF) (b : Bool) :
    (prepare side flex locality other).part b =
      SymbolicCNF.solve (pivots side b flex) (if b then locality else other) := by
  cases b <;> rfl

private theorem supported_part {side : Nat → Bool} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    (b : Bool) : ComponentSupported side b (if b then locality else other) := by
  cases b
  · exact ho
  · exact hl

theorem image_fixed {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    {σ : Nat → Bool} {v : Nat} (h : v ∉ flex) :
    image side (prepare side flex locality other) σ v = .atom v := by
  simp only [image, prepare_part]
  rw [SymbolicCNF.solve_fixed (by simpa using h)]
  simp [SymbolicCNF.substitute, decode]

theorem witness_substitute (side : Nat → Bool) (flex : List Nat)
    (locality other : CNF) (σ : Nat → Bool) (v : Nat) :
    (witness side flex (prepare side flex locality other) σ).substitute v =
      image side (prepare side flex locality other) σ v := by
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

/-- Eliminated coordinate images use only fixed inputs from their own component. -/
theorem image_atoms {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    {σ : Nat → Bool} {v w : Nat}
    (h : w ∈ (image side (prepare side flex locality other) σ v).atoms) :
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
    rcases supported_part hl ho (side v) u hua with hs | ⟨x, rfl, hs⟩
    · simp [hus] at hs
    · have hwx : w = x := by simpa using hwu
      rw [hwx]
      exact ⟨hs, fun _ hx => hun (mem_pivots.mpr ⟨hx, hs⟩)⟩
  · rw [image_fixed hv] at h
    have hwv : w = v := by simpa [BoolExpr.atoms] using h
    exact ⟨hwv ▸ rfl, fun h => (hv h).elim⟩

theorem witness_atoms {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    {σ : Nat → Bool} {v w : Nat}
    (h : w ∈ ((witness side flex (prepare side flex locality other) σ).substitute v).atoms) :
    side w = side v ∧ (v ∈ flex → w ∉ flex) := by
  rw [witness_substitute] at h
  exact image_atoms hl ho h

/-- A selector-query model extends through each component's actual symbolic
images. This statement does not require any component-support assumption. -/
theorem query_component {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    {σ : Nat → Bool} (h : CNFHolds σ (prepare side flex locality other).query)
    (ρ : Nat → Bool) (b : Bool) :
    CNFHolds (SymbolicCNF.interpret ((prepare side flex locality other).part b).values (encode σ ρ))
      (if b then locality else other) := by
  rw [prepare_part]
  apply (SymbolicCNF.solve_correct _ _ _).mp
  have hp := query_part h b
  rw [prepare_part] at hp
  exact (SymbolicCNF.abstract_correct _ _ _).mp hp _
    (fun v hv => by simp [encode, hv])

/-- Component support identifies the two local symbolic solutions with one
uniform modality strategy, while keeping the same selector assignment. -/
theorem query_sound {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    {σ : Nat → Bool} (h : CNFHolds σ (prepare side flex locality other).query)
    (ρ : Nat → Bool) :
    CNFHolds (encode σ (fun v => (image side (prepare side flex locality other) σ v).eval ρ)) locality ∧
    CNFHolds (encode σ (fun v => (image side (prepare side flex locality other) σ v).eval ρ)) other := by
  have hh (b : Bool) :
      CNFHolds (encode σ (fun v => (image side (prepare side flex locality other) σ v).eval ρ))
        (if b then locality else other) := by
    apply (CNFPropagation.holds_congr ?_).mp (query_component h ρ b)
    intro u hu
    rcases supported_part hl ho b u hu with hs | ⟨v, rfl, hv⟩
    · rw [prepare_part]
      simp [SymbolicCNF.interpret, SymbolicCNF.solve_fixed (selector_not_pivot hs),
        BoolExpr.eval, encode, hs]
    · rw [encode_even, image_eval, hv]
  exact ⟨hh true, hh false⟩

/-- The given constant selectors remain valid after eliminating flexible
coordinates and universally abstracting only the rigid scalar inputs. -/
theorem query_complete {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    {σ : Nat → Bool} {s : (Nat → Bool) → Nat → Bool}
    (hs : Uniform side flex s)
    (h : ∀ ρ, CNFHolds (encode σ (s ρ)) locality ∧ CNFHolds (encode σ (s ρ)) other) :
    CNFHolds σ (prepare side flex locality other).query := by
  have hp (b : Bool) :
      CNFHolds σ (SymbolicCNF.abstract selector ((prepare side flex locality other).part b).residual) := by
    rw [prepare_part]
    apply (SymbolicCNF.abstract_correct _ _ _).mpr
    intro η hη
    let ρ : Nat → Bool := fun v => η (2 * v)
    have hmodel : CNFHolds (encode σ (s ρ)) (if b then locality else other) := by
      cases b
      · exact (h ρ).2
      · exact (h ρ).1
    have hm := SymbolicCNF.solve_preserves (pivots side b flex) hmodel
    apply (CNFPropagation.holds_congr (τ := η) ?_).mp hm
    intro u hu
    obtain ⟨hua, hun⟩ := SymbolicCNF.solve_residual_atoms hu
    rcases supported_part hl ho b u hua with hu | ⟨v, rfl, hv⟩
    · simpa [encode, hu] using (hη u hu).symm
    · have hvf : v ∉ flex := fun hvf => hun (mem_pivots.mpr ⟨hvf, hv⟩)
      rw [encode_even, hs.1 ρ v hvf]
  exact (cnfHolds_append _ _ _).mpr ⟨hp true, hp false⟩

theorem image_uniform {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    (σ : Nat → Bool) :
    Uniform side flex
      (fun ρ v => (image side (prepare side flex locality other) σ v).eval ρ) := by
  constructor
  · intro ρ v hv
    simp [image_fixed hv, BoolExpr.eval]
  · intro ρ τ v h
    exact SymbolicModes.eval_congr _ (fun w hw => h w (image_atoms hl ho hw).1)

/-- This equivalence retains the caller's exact selector assignment; it can be
conjoined with the type-polynomial component's obligations on those selectors. -/
theorem query_iff {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    (σ : Nat → Bool) :
    CNFHolds σ (prepare side flex locality other).query ↔
      ∃ s, Uniform side flex s ∧
        ∀ ρ, CNFHolds (encode σ (s ρ)) locality ∧ CNFHolds (encode σ (s ρ)) other := by
  constructor
  · intro h
    exact ⟨_, image_uniform hl ho σ, query_sound hl ho h⟩
  · rintro ⟨s, hs, h⟩
    exact query_complete hl ho hs h

theorem witness_uniform {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    (σ : Nat → Bool) :
    Uniform side flex (fun ρ v =>
      ((witness side flex (prepare side flex locality other) σ).substitute v).eval ρ) := by
  simpa only [witness_substitute] using image_uniform hl ho σ

theorem witness_sound {side : Nat → Bool} {flex : List Nat} {locality other : CNF}
    (hl : ComponentSupported side true locality) (ho : ComponentSupported side false other)
    {σ : Nat → Bool} (h : CNFHolds σ (prepare side flex locality other).query)
    (ρ : Nat → Bool) :
    CNFHolds (encode σ (fun v =>
      ((witness side flex (prepare side flex locality other) σ).substitute v).eval ρ)) locality ∧
    CNFHolds (encode σ (fun v =>
      ((witness side flex (prepare side flex locality other) σ).substitute v).eval ρ)) other := by
  simpa only [witness_substitute] using query_sound hl ho h ρ

/-- Every modality coordinate reifies after fixing the shared selectors. The
locality channel depends only on locality; affinity and uniqueness share their
permitted dependency component. -/
theorem witness_reifies {flex : List Nat} {localPart other : CNF}
    (hl : ComponentSupported locality true localPart) (ho : ComponentSupported locality false other)
    (σ : Nat → Bool) (v : ModVar) :
    ∃ m, (witness locality flex (prepare locality flex localPart other) σ).mode v = some m := by
  let result := witness locality flex (prepare locality flex localPart other) σ
  have hlocal : ∀ w ∈ (result.substitute (v.atomIndex 0)).atoms,
      SymbolicModes.Axis.Supports .locality w := by
    intro w hw
    have hs := (witness_atoms hl ho hw).1
    rw [locality_atom_zero] at hs
    simpa [locality, SymbolicModes.Axis.Supports] using hs
  have haffinity : ∀ w ∈ (result.substitute (v.atomIndex 1)).atoms,
      SymbolicModes.Axis.Supports .affinity w := by
    intro w hw
    have hs := (witness_atoms hl ho hw).1
    rw [locality_atom_one] at hs
    simpa [locality, SymbolicModes.Axis.Supports] using hs
  have hunique : ∀ w ∈ (result.substitute (v.atomIndex 2)).atoms,
      SymbolicModes.Axis.Supports .uniqueness w := by
    intro w hw
    have hs := (witness_atoms hl ho hw).1
    rw [locality_atom_two] at hs
    simpa [locality, SymbolicModes.Axis.Supports] using hs
  obtain ⟨l, hl⟩ := (SymbolicModes.reify_supported _ _).mpr hlocal
  obtain ⟨a, ha⟩ := (SymbolicModes.reify_supported _ _).mpr haffinity
  obtain ⟨u, hu⟩ := (SymbolicModes.reify_supported _ _).mpr hunique
  refine ⟨.compose l (.compose a u), ?_⟩
  change result.mode v = _
  simp [SymbolicModes.Elimination.mode, hl, ha, hu]

/-- The existing finite substitution assembler succeeds for every requested
modality image; no consistency or model-existence premise is needed. -/
theorem witness_assembles {flex : List Nat} {localPart other : CNF}
    (hl : ComponentSupported locality true localPart) (ho : ComponentSupported locality false other)
    (σ : Nat → Bool) (parameters : List (Nat × ModVar)) :
    ∃ action, SymbolicSchemeModes.assemble
      (witness locality flex (prepare locality flex localPart other) σ) parameters = some action := by
  apply (SymbolicSchemeModes.assemble_iff _ _).mpr
  intro p _
  obtain ⟨m, hm⟩ := witness_reifies hl ho σ p.2
  exact Option.isSome_iff_exists.mpr ⟨m, hm⟩

/-- Arbitrary selector prefixes may guard the scalar part of each joint clause.
The supplied prefix can contain several global selectors shared with other
components. -/
theorem guarded_components_supported {α : Type} (side : Nat → Bool) (b : Bool)
    (clauses : List α) (scalar : α → Clause) (guards : Nat → Clause)
    (hg : ∀ i < clauses.length, ∀ literal ∈ guards i, selector literal.1 = true) :
    ComponentSupported side b (clauses.zipIdx.map fun (c, i) => guards i ++
      ((scalar c).filter fun l => side l.1 == b).map (fun l => (2 * l.1, l.2))) := by
  intro v hv
  obtain ⟨c, hc, polarity, hp⟩ := CNFPropagation.mem_atoms.mp hv
  obtain ⟨⟨a, i⟩, hai, rfl⟩ := List.mem_map.mp hc
  rcases List.mem_append.mp hp with hp | hp
  · exact .inl (hg i (List.snd_lt_of_mem_zipIdx hai) (v, polarity) hp)
  · obtain ⟨⟨w, p⟩, hw, he⟩ := List.mem_map.mp hp
    cases he
    exact .inr ⟨w, rfl, by simpa using (List.mem_filter.mp hw).2⟩

end ModalityInference.ComparisonJointModes
