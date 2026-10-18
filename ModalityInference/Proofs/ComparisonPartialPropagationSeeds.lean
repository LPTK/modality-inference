import ModalityInference.Proofs.ComparisonPartialPropagation

/-! Seeded graph edges retain checked endpoint certificates. -/
namespace ModalityInference.ComparisonPartialPropagation

private theorem pair_index_injective {n i j k l : Nat}
    (hj : j < n) (hl : l < n) (h : i * n + j = k * n + l) :
    i = k ∧ j = l := by
  have hn : 0 < n := by omega
  have hdiv := congrArg (fun x => x / n) h
  have hmod := congrArg (fun x => x % n) h
  simp only [Nat.mul_comm _ n, Nat.mul_add_div hn, Nat.div_eq_of_lt hj,
    Nat.div_eq_of_lt hl, Nat.add_zero] at hdiv
  simp only [Nat.mul_comm _ n, Nat.mul_add_mod, Nat.mod_eq_of_lt hj,
    Nat.mod_eq_of_lt hl] at hmod
  exact ⟨hdiv, hmod⟩

private theorem idxOf_injective {α : Type} [BEq α] [LawfulBEq α]
    {xs : List α} {a b : α} (ha : xs.idxOf a < xs.length)
    (hb : xs.idxOf b < xs.length) (h : xs.idxOf a = xs.idxOf b) : a = b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      by_cases hxa : x = a <;> by_cases hxb : x = b
      · exact hxa.symm.trans hxb
      · have hfalse : (x == b) = false := beq_eq_false_iff_ne.mpr hxb
        have htrue : (x == a) = true := beq_iff_eq.mpr hxa
        simp only [List.idxOf_cons, hfalse, htrue, Bool.cond_false, Bool.cond_true] at h
        omega
      · have hfalse : (x == a) = false := beq_eq_false_iff_ne.mpr hxa
        have htrue : (x == b) = true := beq_iff_eq.mpr hxb
        simp only [List.idxOf_cons, hfalse, htrue, Bool.cond_false, Bool.cond_true] at h
        omega
      · have hva : (x == a) = false := beq_eq_false_iff_ne.mpr hxa
        have hvb : (x == b) = false := beq_eq_false_iff_ne.mpr hxb
        simp only [List.idxOf_cons, hva, hvb, Bool.cond_false, List.length_cons] at ha hb h
        exact ih (by omega) (by omega) (by omega)

private theorem Graph.index_injective {g : Graph} {a b : CompareTy}
    (ha : g.index a < g.nodes.size) (hb : g.index b < g.nodes.size)
    (h : g.index a = g.index b) : a = b := by
  exact idxOf_injective (by simpa [Graph.index] using ha)
    (by simpa [Graph.index] using hb) h

private theorem Graph.get_some_iff {g : Graph} {a b : CompareTy} {c : Certificate} :
    g.get a b = some c ↔ (g.index a < g.nodes.size ∧ g.index b < g.nodes.size) ∧
      (g.edges[g.index a * g.nodes.size + g.index b]?).getD none = some c := by
  simp [Graph.get]

/-- Every retrieved edge names its queried endpoints and carries a valid certificate. -/
def Graph.Checked (shape : CompareTy → Bool) (mode : ModExpr → ModExpr → Bool)
    (assumptions : Bounds) (g : Graph) : Prop :=
  ∀ a b c, g.get a b = some c →
    c.left = a ∧ c.right = b ∧ c.check shape mode assumptions = true

theorem Graph.get_add_of_some {g : Graph} {a b : CompareTy} {c : Certificate}
    (h : g.get a b = some c) (d : Certificate) : (g.add d).get a b = some c := by
  unfold Graph.add
  dsimp only
  split
  · rename_i hd
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    have hab := (Graph.get_some_iff.mp h).1
    have hk : g.index d.left * g.nodes.size + g.index d.right ≠
        g.index a * g.nodes.size + g.index b := by
      intro he
      have hn := hd.2
      rw [he] at hn
      have hh : (g.edges[g.index a * g.nodes.size + g.index b]?).getD none = some c := by
        simpa [Graph.get, hab.1, hab.2] using h
      simp [hh] at hn
    apply Graph.get_some_iff.mpr
    refine ⟨hab, ?_⟩
    change ((g.edges.set! _ _)[g.index a * g.nodes.size + g.index b]?).getD none = some c
    simpa only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hk, ↓reduceIte]
      using (Graph.get_some_iff.mp h).2
  · exact h

theorem Graph.Checked.add {g : Graph} {shape mode assumptions}
    (hg : g.Checked shape mode assumptions) {d : Certificate}
    (hd : d.check shape mode assumptions = true) :
    (g.add d).Checked shape mode assumptions := by
  unfold Graph.add
  dsimp only
  split
  · rename_i hnew
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hnew
    intro a b c hc
    have he := Graph.get_some_iff.mp hc
    have hab : g.index a < g.nodes.size ∧ g.index b < g.nodes.size := he.1
    have hh : ((g.edges.set! (g.index d.left * g.nodes.size + g.index d.right)
        (some d))[g.index a * g.nodes.size + g.index b]?).getD none = some c := he.2
    by_cases hk : g.index d.left * g.nodes.size + g.index d.right =
        g.index a * g.nodes.size + g.index b
    · have hi := pair_index_injective hnew.1.2 hab.2 hk
      have ha := Graph.index_injective hnew.1.1 hab.1 hi.1
      have hb := Graph.index_injective hnew.1.2 hab.2 hi.2
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hk,
        ↓reduceIte] at hh
      split at hh
      · simp only [Option.getD_some, Option.some.injEq] at hh
        subst c
        exact ⟨ha, hb, hd⟩
      · cases hh
    · simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hk,
        ↓reduceIte] at hh
      exact hg a b c (Graph.get_some_iff.mpr ⟨hab, hh⟩)
  · exact hg

@[simp] theorem Graph.add_nodes (g : Graph) (c : Certificate) : (g.add c).nodes = g.nodes := by
  simp only [Graph.add]
  split <;> rfl

@[simp] theorem Graph.add_size (g : Graph) (c : Certificate) :
    (g.add c).edges.size = g.edges.size := by
  simp only [Graph.add]
  split <;> simp

theorem Graph.get_add_self {g : Graph} (hsize : g.edges.size = g.nodes.size * g.nodes.size)
    (c : Certificate) (hl : c.left ∈ g.nodes.toList) (hr : c.right ∈ g.nodes.toList) :
    ∃d, (g.add c).get c.left c.right = some d := by
  have hi : g.index c.left < g.nodes.size := by
    simpa [Graph.index] using List.idxOf_lt_length_of_mem hl
  have hj : g.index c.right < g.nodes.size := by
    simpa [Graph.index] using List.idxOf_lt_length_of_mem hr
  have hk : g.index c.left * g.nodes.size + g.index c.right < g.edges.size := by
    rw [hsize]
    calc
      _ < g.index c.left * g.nodes.size + g.nodes.size := Nat.add_lt_add_left hj _
      _ = (g.index c.left + 1) * g.nodes.size := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ g.nodes.size * g.nodes.size := Nat.mul_le_mul_right _ (by omega)
  cases he : g.get c.left c.right with
  | some d => exact ⟨d, Graph.get_add_of_some he c⟩
  | none =>
      have hcell : (g.edges[g.index c.left * g.nodes.size + g.index c.right]?).getD none = none := by
        simpa [Graph.get, hi, hj] using he
      refine ⟨c, ?_⟩
      simp only [Graph.add, hi, hj, decide_true, Bool.true_and, hcell,
        Option.isNone_none, ↓reduceIte]
      apply Graph.get_some_iff.mpr
      refine ⟨⟨hi, hj⟩, ?_⟩
      change ((g.edges.set! _ _)[g.index c.left * g.nodes.size + g.index c.right]?).getD none = some c
      simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
        ↓reduceIte, hk, Option.getD_some]

theorem Graph.get_fold_add_of_some {g : Graph} {a b : CompareTy} {c : Certificate}
    (h : g.get a b = some c) (seeds : List Certificate) :
    (seeds.foldl Graph.add g).get a b = some c := by
  induction seeds generalizing g with
  | nil => exact h
  | cons d ds ih => exact ih (Graph.get_add_of_some h d)

theorem Graph.get_fold_add_seed {g : Graph}
    (hsize : g.edges.size = g.nodes.size * g.nodes.size)
    {seeds : List Certificate} {c : Certificate} (hc : c ∈ seeds)
    (hl : c.left ∈ g.nodes.toList) (hr : c.right ∈ g.nodes.toList) :
    ∃d, (seeds.foldl Graph.add g).get c.left c.right = some d := by
  induction seeds generalizing g with
  | nil => simp at hc
  | cons a rest ih =>
      rcases List.mem_cons.mp hc with rfl | hc
      · obtain ⟨d, hd⟩ := Graph.get_add_self hsize c hl hr
        exact ⟨d, Graph.get_fold_add_of_some hd rest⟩
      · apply ih (g := g.add a) (by simpa using hsize) hc
        · simpa using hl
        · simpa using hr

theorem Graph.Checked.empty (shape mode assumptions) (nodes : List CompareTy) :
    (Graph.empty nodes).Checked shape mode assumptions := by
  intro a b c h
  have h := (Graph.get_some_iff.mp h).2
  simp only [Graph.empty, Array.getElem?_replicate] at h
  split at h <;> cases h

theorem Graph.Checked.fold_add {g : Graph} {shape mode assumptions}
    (hg : g.Checked shape mode assumptions) (seeds : List Certificate)
    (hs : ∀c ∈ seeds, c.check shape mode assumptions = true) :
    (seeds.foldl Graph.add g).Checked shape mode assumptions := by
  induction seeds generalizing g with
  | nil => exact hg
  | cons c rest ih => exact ih (hg.add (hs c (by simp))) (fun d hd => hs d (by simp [hd]))

theorem initialGraph_bound {assumptions : Bounds} {nodes : List CompareTy} {a b : Ty}
    (hab : .sub a b ∈ assumptions) (ha : CompareTy.ofTy a ∈ nodes)
    (hb : CompareTy.ofTy b ∈ nodes) :
    ∃c, (initialGraph assumptions nodes).get (.ofTy a) (.ofTy b) = some c := by
  refine Graph.get_fold_add_seed (g := Graph.empty nodes) (c := .bound a b)
    (by simp [Graph.empty]) ?_ ?_ ?_
  · apply List.mem_append_right
    exact List.mem_filterMap.mpr ⟨.sub a b, hab, rfl⟩
  · simpa [Graph.empty, Certificate.left] using ha
  · simpa [Graph.empty, Certificate.right] using hb

theorem axioms_checked {shape : CompareTy → Bool} {mode : ModExpr → ModExpr → Bool}
    {assumptions : Bounds}
    (hmodal : ∀a m, shape (.modal a m) = shape a)
    {a : CompareTy} (ha : shape a = true) {c : Certificate} (hc : c ∈ axioms a) :
    c.check shape mode assumptions = true := by
  have hbase : ∀x, shape x = true → ∀c ∈
      [Certificate.refl x, .identity x false, .identity x true],
        c.check shape mode assumptions = true := by
    intro x hx c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact hx
  simp only [axioms, List.mem_append] at hc
  rcases hc with hc | hc
  · exact hbase a ha c hc
  · cases a <;> try simp at hc
    · rename_i inner m
      cases inner <;> cases m <;> simp at hc
      all_goals rcases hc with rfl | rfl
      all_goals simpa only [Certificate.check, hmodal] using ha
    all_goals rcases hc with rfl | rfl <;> exact ha

theorem initialGraph_checked {shape : CompareTy → Bool} {mode : ModExpr → ModExpr → Bool}
    {assumptions : Bounds} {nodes : List CompareTy}
    (hs : ∀a ∈ nodes, ∀c ∈ axioms a, c.check shape mode assumptions = true) :
    (initialGraph assumptions nodes).Checked shape mode assumptions := by
  apply (Graph.Checked.empty shape mode assumptions nodes).fold_add
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
    exact hs a ha c hc
  · obtain ⟨b, hb, he⟩ := List.mem_filterMap.mp hc
    cases b with
    | sub a b =>
        simp only [Option.some.injEq] at he
        subst c
        simpa [Certificate.check, List.contains_iff] using hb
    | mode a b | defined a | equal x a | equiv a b => cases he

end ModalityInference.ComparisonPartialPropagation
