import ModalityInference.Proofs.ComparisonElimination
import ModalityInference.Proofs.ComparisonAlgebraReification

/-! Interpretation of the exact opaque endpoints compiled by group elimination. -/
namespace ModalityInference.ComparisonElimination

open ComparisonPropagation ComparisonControls

theorem lookupFin_spec {α : Type} [BEq α] [LawfulBEq α] {xs : List α} {x : α}
    {i : Fin xs.length} (h : lookupFin xs x = some i) : xs[i] = x := by
  unfold lookupFin at h
  dsimp only at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  · subst i
    simpa only [List.idxOf, beq_iff_eq] using
      (List.findIdx_getElem (xs := xs) (p := (· == x)) (w := ‹_›))

theorem leaf_spec {basis : Basis} {names : List Nat} {v : TypeVar} {result : Leaf names.length}
    (h : leaf basis names v = .success result) :
    match result with
    | .fixed clauses => ∃ i, basis.index (.head (.var v)) = some i ∧ clauses = [[(i, true)]]
    | .flex i => v = .flex names[i] := by
  cases v with
  | rigid n =>
    simp only [leaf] at h
    split at h <;> try contradiction
    next i hi => cases h; exact ⟨i, hi, rfl⟩
  | flex n =>
    simp only [leaf] at h
    split at h
    · next i hi => cases h; exact congrArg TypeVar.flex (lookupFin_spec hi).symm
    · split at h <;> try contradiction
      next i hi => cases h; exact ⟨i, hi, rfl⟩

theorem basis_index_value {basis : Basis} {a : CompareTy} {i : Nat}
    (h : basis.index (.head a) = some i) (value : CompareTy → Bool) :
    basisValue basis.types value i = value a := by
  simp only [basisValue, Basis.types, List.getElem?_map, index_lookup h,
    Option.map_some, Basis.term, Option.getD_some]

theorem leaf_holds {basis : Basis} {names : List Nat} {v : TypeVar} {result : Leaf names.length}
    (h : leaf basis names v = .success result)
    (value : CompareTy → Bool) (values : Fin names.length → Prop)
    (hv : ∀ i : Fin names.length, values i ↔ value (.var (.flex names[i])) = true) :
    result.Holds (basisValue basis.types value) values ↔ value (.var v) = true := by
  have hs := leaf_spec h
  cases result with
  | fixed clauses =>
    obtain ⟨i, hi, rfl⟩ := hs
    simp [Leaf.Holds, CNFHolds, ClauseHolds, basis_index_value hi value]
  | flex i =>
    rw [hs]
    exact hv i

theorem endpoint_spec {basis : Basis} {names : List Nat} {atom : ComparisonGroups.Atom}
    {result : Endpoint names.length} (h : endpoint basis names atom = .success result) :
    leaf basis names atom.head = .success result.leaf ∧ result.mode = atom.mode := by
  unfold endpoint at h
  simp only [bind, pure, RunResult.bind] at h
  split at h <;> try contradiction
  next l hl => cases h; exact ⟨hl, rfl⟩

theorem bound_spec {basis : Basis} {names : List Nat} {pair : ComparisonGroups.Inequality}
    {result : Bound names.length} (h : bound basis names pair = .success result) :
    endpoint basis names pair.1 = .success result.left ∧
      endpoint basis names pair.2 = .success result.right := by
  unfold bound at h
  simp only [bind, pure, RunResult.bind] at h
  repeat' first | contradiction | split at h
  cases h
  constructor <;> assumption

/-- The endpoint namespace may contain selectors and modality atoms beyond the
basis prefix. Fixed-head and reconstructed-image readings are kept separate. -/
theorem leaf_holds_at {basis : Basis} {names : List Nat} {v : TypeVar} {result : Leaf names.length}
    (h : leaf basis names v = .success result)
    (value : CompareTy → Bool) (types : TypeVar → CompareTy) (values : Fin names.length → Prop)
    (τ : Nat → Bool)
    (hprefix : ∀ i < basis.types.length, τ i = basisValue basis.types value i)
    (hfixed : ∀ i, basis.index (.head (.var v)) = some i → value (.var v) = value (types v))
    (himages : ∀ i : Fin names.length, values i ↔ value (types (.flex names[i])) = true) :
    result.Holds τ values ↔ value (types v) = true := by
  have hs := leaf_spec h
  cases result with
  | fixed clauses =>
    obtain ⟨i, hi, rfl⟩ := hs
    simp [Leaf.Holds, CNFHolds, ClauseHolds, hprefix i (index_bound hi),
      basis_index_value hi value, hfixed i hi]
  | flex i =>
    rw [hs]
    exact himages i

/-- The actual low/high action polynomials implement the chosen modal
coordinate on the Boolean reading of an endpoint's underlying type. -/
theorem endpoint_holds_coordinate {fuel : Nat} {basis : Basis} {count : Nat}
    {endpoint : Endpoint count} {action : ModExpr → Action} {c : Coordinate}
    {headAtom modeAtom : Nat → Nat} {τ : Nat → Bool} {values : Fin count → Prop} {value : Bool}
    (hl : low fuel basis endpoint.mode = .success (action endpoint.mode).lower)
    (hu : high fuel basis endpoint.mode = .success (action endpoint.mode).upper)
    (ht : (basis.theoryAt id headAtom modeAtom c).eval τ = true)
    (hbottom : (basis.formula headAtom modeAtom c .bottom).eval τ = false)
    (htop : (basis.formula headAtom modeAtom c .top).eval τ = true)
    (hvalue : endpoint.leaf.Holds τ values ↔ value = true) :
    endpoint.Holds action τ values ↔
      (c.modalWith modeAtom (.const value) endpoint.mode).eval τ = true := by
  have hlo := low_theory hl ht
  have hhi := high_theory hu ht
  simp only [Function.comp_id] at hlo hhi
  rw [Endpoint.Holds, Action.Holds, hvalue, hlo, hhi]
  cases c <;> simp [Coordinate.modalWith, BoolExpr.eval, hbottom, htop]

theorem basis_index_head {basis : Basis} {a : CompareTy} {i : Nat}
    (h : basis.index (.head a) = some i) : a ∈ basis.heads := by
  have hm := List.mem_of_getElem? (index_lookup h)
  simpa [Basis.keys] using hm

/-- Actual propagated polynomials only inspect the basis prefix; selectors and
mode coordinates do not alter the Boolean reading of a reconstructed image. -/
theorem reduce_observer_at {Δ : Bounds} {shape : ComparisonShape}
    {basis : List CompareTy} {count : Nat} {program : Program count} {result : Reduction count}
    (h : reduce basis program = .success result)
    (f : LatticeHom (ComparisonAlgebra.Order Δ shape) Bool) (ms : ModVar → ModExpr)
    (τ : Nat → Bool)
    (hprefix : ∀ i < basis.length, τ i = basisValue basis
      (fun t => ComparisonAlgebra.booleanValue f (t.subst CompareTy.var ms)) i)
    (v : Fin count) :
    CNFHolds τ result.store[v] ↔
      ComparisonAlgebra.booleanValue f (result.images[v].subst CompareTy.var ms) = true := by
  have hc := CNFPropagation.holds_congr (cs := result.store[v])
    (fun i hi => hprefix i (List.mem_range.mp ((reduce_polynomial h).2.1 v i hi)))
  exact hc.trans (ComparisonAlgebra.reify_booleanValue ((reduce_correct h).2.1 v) f CompareTy.var ms).symm

end ModalityInference.ComparisonElimination
