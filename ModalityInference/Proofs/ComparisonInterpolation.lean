import ModalityInference.ComparisonInterpolation

namespace ModalityInference.ComparisonInterpolation

theorem join_subtype_iff {Δ : Bounds} (head : CompareTy) (rest : List CompareTy)
    (t : CompareTy) : CompareSubtype Δ (join head rest) t ↔
      ∀ a ∈ head :: rest, CompareSubtype Δ a t := by
  induction rest generalizing head
  case nil => simp [join]
  case cons next rest ih =>
    constructor
    · intro h a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact .trans .joinLeft h
      · exact (ih next).mp (.trans .joinRight h) a ha
    · intro h
      exact .joinLeast (h head (by simp))
        ((ih next).mpr (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem subtype_meet_iff {Δ : Bounds} (head : CompareTy) (rest : List CompareTy)
    (t : CompareTy) : CompareSubtype Δ t (meet head rest) ↔
      ∀ a ∈ head :: rest, CompareSubtype Δ t a := by
  induction rest generalizing head
  case nil => simp [meet]
  case cons next rest ih =>
    constructor
    · intro h a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact .trans h .meetLeft
      · exact (ih next).mp (.trans h .meetRight) a ha
    · intro h
      exact .meetGreatest (h head (by simp))
        ((ih next).mpr (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem witness_interval {Δ lower upper} (h : Crossed Δ lower upper) :
    Interval Δ lower upper (witness lower upper) := by
  cases lower
  case nil =>
    cases upper
    case nil => simp [Interval]
    case cons head rest =>
      exact ⟨by simp, (subtype_meet_iff head rest (meet head rest)).mp .refl⟩
  case cons head rest =>
    exact ⟨(join_subtype_iff head rest (join head rest)).mp .refl,
      fun t ht => (join_subtype_iff head rest t).mpr (fun a ha => h a ha t ht)⟩

theorem Interval.crossed {Δ lower upper t} (h : Interval Δ lower upper t) :
    Crossed Δ lower upper :=
  fun a ha b hb => .trans (h.1 a ha) (h.2 b hb)

theorem witness_interval_iff (Δ : Bounds) (lower upper : List CompareTy) :
    Interval Δ lower upper (witness lower upper) ↔ Crossed Δ lower upper :=
  ⟨Interval.crossed, witness_interval⟩

/-- Crossing the isolated bounds is equivalent to existence of a finite witness. -/
theorem exists_interval_iff (Δ : Bounds) (lower upper : List CompareTy) :
    (∃ t, Interval Δ lower upper t) ↔ Crossed Δ lower upper :=
  ⟨fun ⟨_, h⟩ => h.crossed, fun h => ⟨witness lower upper, witness_interval h⟩⟩

private theorem binary_join_defined_iff (Δ : Bounds) (a b : CompareTy) :
    (CompareTy.join a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels,
    List.mem_append, or_imp, forall_and]

private theorem binary_meet_defined_iff (Δ : Bounds) (a b : CompareTy) :
    (CompareTy.meet a b).DefinedUnder Δ ↔ a.DefinedUnder Δ ∧ b.DefinedUnder Δ := by
  simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels,
    List.mem_append, or_imp, forall_and]

theorem join_defined_iff (Δ : Bounds) (head : CompareTy) (rest : List CompareTy) :
    (join head rest).DefinedUnder Δ ↔ EndpointsDefined Δ (head :: rest) := by
  induction rest generalizing head
  case nil => simp [join, EndpointsDefined]
  case cons next rest ih =>
    rw [join, binary_join_defined_iff, ih]
    simp [EndpointsDefined]

theorem meet_defined_iff (Δ : Bounds) (head : CompareTy) (rest : List CompareTy) :
    (meet head rest).DefinedUnder Δ ↔ EndpointsDefined Δ (head :: rest) := by
  induction rest generalizing head
  case nil => simp [meet, EndpointsDefined]
  case cons next rest ih =>
    rw [meet, binary_meet_defined_iff, ih]
    simp [EndpointsDefined]

theorem witness_defined {Δ lower upper}
    (hl : EndpointsDefined Δ lower) (hu : EndpointsDefined Δ upper) :
    (witness lower upper).DefinedUnder Δ := by
  cases lower
  case cons head rest => exact (join_defined_iff Δ head rest).mpr hl
  case nil =>
    cases upper
    case cons head rest => exact (meet_defined_iff Δ head rest).mpr hu
    case nil => simp [witness, CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]

theorem guarded_witness {Δ lower upper} (h : Crossed Δ lower upper)
    (hl : EndpointsDefined Δ lower) (hu : EndpointsDefined Δ upper) :
    GuardedInterval Δ lower upper (witness lower upper) := by
  have hi := witness_interval h
  have ht := witness_defined hl hu
  exact ⟨fun a ha => ⟨hi.1 a ha, hl a ha, ht⟩,
    fun b hb => ⟨hi.2 b hb, ht, hu b hb⟩⟩

theorem eliminate_spec (Δ : Bounds) (lower upper : List CompareTy) :
    CompareEntailsAll Δ (eliminate lower upper) ↔
      Crossed Δ lower upper ∧ EndpointsDefined Δ lower ∧ EndpointsDefined Δ upper := by
  simp only [CompareEntailsAll, eliminate, List.forall_mem_append,
    List.forall_mem_flatMap, List.forall_mem_map, CompareEntails]
  constructor
  · rintro ⟨h, hl, hu⟩
    exact ⟨fun a ha b hb => (h a ha b hb).1,
      fun a ha => (hl a ha).2.1, fun b hb => (hu b hb).2.1⟩
  · rintro ⟨h, hl, hu⟩
    exact ⟨fun a ha b hb => ⟨h a ha b hb, hl a ha, hu b hb⟩,
      fun a ha => ⟨.refl, hl a ha, hl a ha⟩,
      fun b hb => ⟨.refl, hu b hb, hu b hb⟩⟩

theorem GuardedInterval.eliminate {Δ lower upper t} (h : GuardedInterval Δ lower upper t) :
    CompareEntailsAll Δ (eliminate lower upper) := by
  apply (eliminate_spec Δ lower upper).mpr
  exact ⟨fun a ha b hb => .trans (h.1 a ha).1 (h.2 b hb).1,
    fun a ha => (h.1 a ha).2.1, fun b hb => (h.2 b hb).2.2⟩

theorem eliminate_witness {Δ lower upper} (h : CompareEntailsAll Δ (eliminate lower upper)) :
    GuardedInterval Δ lower upper (witness lower upper) := by
  obtain ⟨hc, hl, hu⟩ := (eliminate_spec Δ lower upper).mp h
  exact guarded_witness hc hl hu

/-- Guarded elimination retains all written endpoint guards, including one-sided
intervals, and reconstructs its finite witness without an existence assumption. -/
theorem eliminate_iff (Δ : Bounds) (lower upper : List CompareTy) :
    CompareEntailsAll Δ (eliminate lower upper) ↔
      GuardedInterval Δ lower upper (witness lower upper) :=
  ⟨eliminate_witness, GuardedInterval.eliminate⟩

theorem exists_guarded_interval_iff (Δ : Bounds) (lower upper : List CompareTy) :
    (∃ t, GuardedInterval Δ lower upper t) ↔ CompareEntailsAll Δ (eliminate lower upper) :=
  ⟨fun ⟨_, h⟩ => h.eliminate, fun h => ⟨witness lower upper, eliminate_witness h⟩⟩

theorem join_support_iff (p : TypeVar → Prop) (q : ModVar → Prop)
    (head : CompareTy) (rest : List CompareTy) :
    Supports p q (join head rest) ↔ ∀ a ∈ head :: rest, Supports p q a := by
  induction rest generalizing head <;> simp_all [join, Supports]

theorem meet_support_iff (p : TypeVar → Prop) (q : ModVar → Prop)
    (head : CompareTy) (rest : List CompareTy) :
    Supports p q (meet head rest) ↔ ∀ a ∈ head :: rest, Supports p q a := by
  induction rest generalizing head <;> simp_all [meet, Supports]

theorem witness_support {p : TypeVar → Prop} {q : ModVar → Prop} {lower upper}
    (hl : ∀ a ∈ lower, Supports p q a) (hu : ∀ b ∈ upper, Supports p q b) :
    Supports p q (witness lower upper) := by
  cases lower
  case cons head rest => exact (join_support_iff p q head rest).mpr hl
  case nil =>
    cases upper
    case cons head rest => exact (meet_support_iff p q head rest).mpr hu
    case nil => trivial

end ModalityInference.ComparisonInterpolation
