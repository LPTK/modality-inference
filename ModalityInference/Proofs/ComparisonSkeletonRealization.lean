import ModalityInference.Proofs.ComparisonSkeletonNormalization
import ModalityInference.Proofs.ComparisonSkeleton

namespace ModalityInference.ComparisonSkeleton

open ComparisonSkeletonCoordinates ComparisonShapeSolver

def defaultShape (p : SchemePreparation.Prepared) : ComparisonShape → ComparisonShape
  | .var v => if sourceAllowed p v then .unit else .var v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (defaultShape p a) (defaultShape p b)
  | .sum a b => .sum (defaultShape p a) (defaultShape p b)
  | .fn a b => .fn (defaultShape p a) (defaultShape p b)

def FixedShape (p : SchemePreparation.Prepared) : ComparisonShape → Prop
  | .var v => sourceAllowed p v = false
  | .unit | .credit => True
  | .prod a b | .sum a b | .fn a b => FixedShape p a ∧ FixedShape p b

theorem defaultShape_fixed (p : SchemePreparation.Prepared) (s : ComparisonShape) :
    FixedShape p (defaultShape p s) := by
  induction s <;> simp_all [defaultShape, FixedShape]
  split <;> simp_all [FixedShape]

theorem typeCount_defaultShape (p : SchemePreparation.Prepared) (s : ComparisonShape) :
    typeCount p (defaultShape p s) = typeCount p s := by
  induction s <;> simp_all [defaultShape, typeCount]
  split <;> simp_all [typeCount]

theorem modeCount_defaultShape (p : SchemePreparation.Prepared) (s : ComparisonShape) :
    modeCount p (defaultShape p s) = modeCount p s := by
  induction s <;> simp_all [defaultShape, modeCount]
  split <;> simp_all [modeCount]

theorem build_defaultShape (p : SchemePreparation.Prepared) (s : ComparisonShape) (nt nm : Nat) :
    build p (defaultShape p s) nt nm = build p s nt nm := by
  induction s generalizing nt nm <;>
    simp_all only [defaultShape, build, typeCount_defaultShape, modeCount_defaultShape]
  split <;> simp_all [build]

def coordinateTypes {Δ : Bounds} (p : SchemePreparation.Prepared) :
    {s : ComparisonShape} → Tree Δ s → Nat → List (Nat × CompareTy)
  | _, .atom a, nt => [(nt, a.type)]
  | _, .unit _, _ | _, .credit _, _ => []
  | .prod s _, .prod a b _, nt | .sum s _, .sum a b _, nt | .fn s _, .fn a b _, nt =>
    coordinateTypes p a nt ++ coordinateTypes p b (nt + typeCount p s)

def coordinateModes {Δ : Bounds} (p : SchemePreparation.Prepared) :
    {s : ComparisonShape} → Tree Δ s → Nat → List (Nat × ModExpr)
  | _, .atom _, _ => []
  | _, .unit m, nm | _, .credit m, nm => [(nm, m.expression)]
  | .prod s _, .prod a b m, nm | .sum s _, .sum a b m, nm | .fn s _, .fn a b m, nm =>
    (nm, m.expression) :: (coordinateModes p a (nm + 1) ++
      coordinateModes p b (nm + 1 + modeCount p s))

def coordinateAction {Δ : Bounds} (p : SchemePreparation.Prepared) {s : ComparisonShape}
    (tree : Tree Δ s) (nt nm : Nat) : CompareSubstitution :=
  ⟨coordinateTypes p tree nt, coordinateModes p tree nm⟩

theorem coordinateTypes_keys {Δ : Bounds} (p : SchemePreparation.Prepared) {s : ComparisonShape}
    (tree : Tree Δ s) (hf : FixedShape p s) (nt : Nat) :
    (coordinateTypes p tree nt).map Prod.fst = List.range' nt (typeCount p s) := by
  induction tree generalizing nt with
  | atom a => simp [coordinateTypes, typeCount, FixedShape] at hf ⊢; simp [hf]
  | unit | credit => simp [coordinateTypes, typeCount]
  | prod a b m ih₁ ih₂ | sum a b m ih₁ ih₂ | fn a b m ih₁ ih₂ =>
    simp only [coordinateTypes, List.map_append, ih₁ hf.1, ih₂ hf.2, typeCount]
    simpa only [Nat.one_mul] using List.range'_append (s := nt) (step := 1)

theorem coordinateModes_keys {Δ : Bounds} (p : SchemePreparation.Prepared) {s : ComparisonShape}
    (tree : Tree Δ s) (hf : FixedShape p s) (nm : Nat) :
    (coordinateModes p tree nm).map Prod.fst = List.range' nm (modeCount p s) := by
  induction tree generalizing nm with
  | atom a => simp [coordinateModes, modeCount, FixedShape] at hf ⊢; simp [hf]
  | unit | credit => simp [coordinateModes, modeCount]
  | prod a b m ih₁ ih₂ | sum a b m ih₁ ih₂ | fn a b m ih₁ ih₂ =>
    simp only [coordinateModes, List.map_cons, List.map_append, ih₁ hf.1, ih₂ hf.2, modeCount]
    conv_rhs => rw [Nat.add_assoc, Nat.add_comm 1, List.range'_succ]
    congr 1
    simpa only [Nat.one_mul] using List.range'_append (s := nm + 1) (step := 1)


/-- Any substitution assigning the finite coordinate lists realizes exactly
the original structural template. -/
theorem build_coordinates {Δ : Bounds} (p : SchemePreparation.Prepared) {s : ComparisonShape}
    (tree : Tree Δ s) (hf : FixedShape p s) (nt nm : Nat) (σ : CompareSubstitution)
    (ht : ∀ entry ∈ coordinateTypes p tree nt, σ.type (.flex entry.1) = entry.2)
    (hm : ∀ entry ∈ coordinateModes p tree nm, σ.mode (.flex entry.1) = entry.2) :
    σ.ty (build p s nt nm) = tree.reify := by
  induction tree generalizing nt nm with
  | atom a =>
    simp only [FixedShape] at hf
    have hh := ht (nt, a.type) (List.mem_cons_self)
    simpa only [build, hf, Bool.false_eq_true, if_false, CompareSubstitution.ty,
      CompareTy.ofTy, CompareTy.subst, Tree.reify] using hh
  | unit m | credit m =>
    have hh := hm (nm, m.expression) (List.mem_cons_self)
    simp only [build, CompareSubstitution.ty, CompareTy.ofTy, CompareTy.subst,
      ModExpr.subst, hh, Tree.reify]
  | @prod s t a b m ih₁ ih₂ | @sum s t a b m ih₁ ih₂ | @fn s t a b m ih₁ ih₂ =>
    have hl := ih₁ hf.1 nt (nm + 1)
      (fun entry he => ht entry (List.mem_append_left _ he))
      (fun entry he => hm entry (List.mem_cons_of_mem _ (List.mem_append_left _ he)))
    have hr := ih₂ hf.2 (nt + typeCount p s) (nm + 1 + modeCount p s)
      (fun entry he => ht entry (List.mem_append_right _ he))
      (fun entry he => hm entry (List.mem_cons_of_mem _ (List.mem_append_right _ he)))
    have hh := hm (nm, m.expression) (List.mem_cons_self)
    first
    | change CompareTy.modal (.prod (σ.ty (build p s nt (nm + 1)))
        (σ.ty (build p t (nt + typeCount p s) (nm + 1 + modeCount p s))))
        (σ.mode (.flex nm)) = _
    | change CompareTy.modal (.sum (σ.ty (build p s nt (nm + 1)))
        (σ.ty (build p t (nt + typeCount p s) (nm + 1 + modeCount p s))))
        (σ.mode (.flex nm)) = _
    | change CompareTy.modal (.fn (σ.ty (build p s nt (nm + 1)))
        (σ.ty (build p t (nt + typeCount p s) (nm + 1 + modeCount p s))))
        (σ.mode (.flex nm)) = _
    all_goals rw [hl, hr, hh]; rfl

private theorem lookup_mem_keys_nodup {α : Type} {entries : List (Nat × α)}
    (hn : (entries.map Prod.fst).Nodup) {n : Nat} {a : α} (ha : (n, a) ∈ entries) :
    entries.lookup n = some a := by
  induction entries with
  | nil => contradiction
  | cons entry entries ih =>
    rcases entry with ⟨key, value⟩
    have hh := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with he | he
    · cases he
      simp
    · have hne : n ≠ key := by
        intro hn
        exact hh.1 (hn ▸ List.mem_map.mpr ⟨(n, a), he, rfl⟩)
      have hb : (n == key) = false := by simp [hne]
      simpa only [List.lookup_cons, hb] using ih hh.2 he

theorem coordinateAction_realizes {Δ : Bounds} (p : SchemePreparation.Prepared)
    {s : ComparisonShape} (tree : Tree Δ s) (hf : FixedShape p s) (nt nm : Nat) :
    (coordinateAction p tree nt nm).ty (build p s nt nm) = tree.reify := by
  apply build_coordinates p tree hf nt nm
  · intro entry he
    have hh := lookup_mem_keys_nodup
      ((coordinateTypes_keys p tree hf nt).symm ▸ List.nodup_range') he
    simp only [coordinateAction, CompareSubstitution.type, hh, Option.getD_some]
  · intro entry he
    have hh := lookup_mem_keys_nodup
      ((coordinateModes_keys p tree hf nm).symm ▸ List.nodup_range') he
    simp only [coordinateAction, CompareSubstitution.mode, hh, Option.getD_some]


theorem coordinateTypes_guarded {Δ : Bounds} (p : SchemePreparation.Prepared)
    {s : ComparisonShape} (tree : Tree Δ s) (nt : Nat) :
    ∀ entry ∈ coordinateTypes p tree nt, entry.2.WellShaped Δ ∧ entry.2.DefinedUnder Δ := by
  induction tree generalizing nt with
  | atom a =>
    intro entry he
    have hh : entry = (nt, a.type) := by simpa [coordinateTypes] using he
    subst entry
    exact ⟨a.shaped, a.defined⟩
  | unit | credit => simp [coordinateTypes]
  | prod a b m ih₁ ih₂ | sum a b m ih₁ ih₂ | fn a b m ih₁ ih₂ =>
    intro entry he
    rcases List.mem_append.mp he with he | he
    · exact ih₁ _ entry he
    · exact ih₂ _ entry he

theorem coordinateModes_defined {Δ : Bounds} (p : SchemePreparation.Prepared)
    {s : ComparisonShape} (tree : Tree Δ s) (nm : Nat) :
    ∀ entry ∈ coordinateModes p tree nm, Entails Δ (.defined entry.2) := by
  induction tree generalizing nm with
  | atom => simp [coordinateModes]
  | unit m | credit m =>
    intro entry he
    have hh : entry = (nm, m.expression) := by simpa [coordinateModes] using he
    subst entry
    exact m.defined
  | prod a b m ih₁ ih₂ | sum a b m ih₁ ih₂ | fn a b m ih₁ ih₂ =>
    intro entry he
    rcases List.mem_cons.mp he with he | he
    · subst entry
      exact m.defined
    · rcases List.mem_append.mp he with he | he
      · exact ih₁ _ entry he
      · exact ih₂ _ entry he

theorem coordinateAction_wellShaped {Δ : Bounds} (p : SchemePreparation.Prepared)
    {s : ComparisonShape} (tree : Tree Δ s) (nt nm : Nat) :
    (coordinateAction p tree nt nm).WellShaped Δ :=
  fun entry he => (coordinateTypes_guarded p tree nt entry he).1

/-- A finite explicit assignment realizes every coordinate tree at the shape
used by the existing template builder. Source shape parameters are defaulted
exactly as in `build`; fixed opaque classes retain genuine internal images. -/
theorem build_factor {Δ : Bounds} (p : SchemePreparation.Prepared) (s : ComparisonShape)
    (tree : Tree Δ (defaultShape p s)) (nt nm : Nat) :
    let σ := coordinateAction p tree nt nm
    σ.ty (build p s nt nm) = tree.reify ∧
      σ.types.map Prod.fst = List.range' nt (typeCount p s) ∧
      σ.modes.map Prod.fst = List.range' nm (modeCount p s) ∧
      σ.WellShaped Δ ∧ (∀ entry ∈ σ.types, entry.2.DefinedUnder Δ) ∧
      (∀ entry ∈ σ.modes, Entails Δ (.defined entry.2)) := by
  refine ⟨?_, ?_, ?_, coordinateAction_wellShaped p tree nt nm,
    fun entry he => (coordinateTypes_guarded p tree nt entry he).2,
    coordinateModes_defined p tree nm⟩
  · rw [← build_defaultShape p s nt nm]
    exact coordinateAction_realizes p tree (defaultShape_fixed p s) nt nm
  · exact (coordinateTypes_keys p tree (defaultShape_fixed p s) nt).trans
      (congrArg (List.range' nt) (typeCount_defaultShape p s))
  · exact (coordinateModes_keys p tree (defaultShape_fixed p s) nm).trans
      (congrArg (List.range' nm) (modeCount_defaultShape p s))

end ModalityInference.ComparisonSkeleton
