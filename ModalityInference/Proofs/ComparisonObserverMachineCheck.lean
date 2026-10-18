import ModalityInference.ComparisonObserverMachineCheck
import ModalityInference.Proofs.ComparisonObserverMachine
import ModalityInference.Proofs.ComparisonCoordinateTransition
import ModalityInference.Proofs.ComparisonStructuralCoherence

/-! Finite coordinate certificates imply the all-label semantic machine laws.
The only context guard is the original scalar model condition; function child
worlds remain separate and pair worlds agree only on the relevant input axes. -/
namespace ModalityInference.ComparisonObserverMachineCheck

open ComparisonControls ComparisonAlgebra ComparisonStructuralLayout
  ComparisonStructuralAlignment ComparisonObserverMachine ComparisonCoordinateTransition

variable {State : Type}

theorem bits_eq (η : ModVar → Mode) : bits η = encodeModes η := rfl

theorem act_eq (c : Coordinate) (m : Mode) (x : Bool) :
    act c m x = coordinateValue c x m := by cases c <;> rfl

theorem scalarOK_correct {Δ modes} {d : Description State} :
    scalarOK Δ modes d = true ↔ d.coordinate = .unaffected ∨ ModeModels Δ (modeValue modes d) := by
  simp only [scalarOK, Bool.or_eq_true, decide_eq_true_eq, bits_eq,
    boundsModeFormula_correct, projectedModes_encodeModes]

theorem action_complete {Δ modes} {d : Description State}
    (hs : scalarOK Δ modes d = true) {m : ModExpr} (hm : Entails Δ (.defined m)) (x : Bool) :
    action modes d m x = coordinateValue d.coordinate x (m.complete (modeValue modes d)) := by
  rcases scalarOK_correct.mp hs with hc | hη
  · simp [action, act, hc, coordinateValue]
  · obtain ⟨n,hn⟩ := Option.isSome_iff_exists.mp (hm _ hη)
    simp only [action, hn, Option.getD_some, ModExpr.complete_of_eval hn, act_eq]

theorem action_formula {Δ modes} {d : Description State}
    (hs : scalarOK Δ modes d = true) {m : ModExpr} (hm : Entails Δ (.defined m)) (x : Bool) :
    action modes d m x = (d.coordinate.modal (.const x) m).eval (encodeModes (modeValue modes d)) := by
  rcases scalarOK_correct.mp hs with hc | hη
  · simp [action, act, hc, Coordinate.modal, Coordinate.modalWith, BoolExpr.eval]
  · obtain ⟨n,hn⟩ := Option.isSome_iff_exists.mp (hm _ hη)
    have he := Coordinate.modalWith_eval (modeAtom := id) (value := .const x)
      (c := d.coordinate) (fun _ => rfl) (.inr hn)
    simpa only [action, hn, Option.getD_some, act_eq, Coordinate.modal, BoolExpr.eval] using he.symm

private theorem encode_local (η : ModVar → Mode) (v : ModVar) :
    encodeModes η (v.atomIndex 0) = (η v).isLocal :=
  congrArg Mode.isLocal (congrFun (projectedModes_encodeModes η) v)

private theorem encode_affine (η : ModVar → Mode) (v : ModVar) :
    encodeModes η (v.atomIndex 1) = (η v).once :=
  congrArg Mode.once (congrFun (projectedModes_encodeModes η) v)

private theorem encode_unique (η : ModVar → Mode) (v : ModVar) :
    encodeModes η (v.atomIndex 2) = (η v).unique :=
  congrArg Mode.unique (congrFun (projectedModes_encodeModes η) v)

theorem sameInputs_any {modes} {p c : Description State} (h : sameInputs modes p c = true)
    (names : List ModVar) : SameInputs names c.coordinate
      (encodeModes (modeValue modes p)) (encodeModes (modeValue modes c)) := by
  cases hc : c.coordinate with
  | unaffected => trivial
  | locality =>
    simp only [sameInputs, hc, List.all_eq_true, beq_iff_eq] at h
    intro v _
    simp only [encode_local]
    by_cases hv : v ∈ modes
    · exact h v hv
    · simp [modeValue, hv]
  | affinity | uniqueness =>
    simp only [sameInputs, hc, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
    intro v _
    simp only [encode_affine, encode_unique]
    by_cases hv : v ∈ modes
    · exact h v hv
    · simp [modeValue, hv]

theorem action_same {Δ modes} {p c : Description State}
    (hp : scalarOK Δ modes p = true) (hc : scalarOK Δ modes c = true)
    (he : c.coordinate = p.coordinate) (hi : sameInputs modes p c = true)
    {m : ModExpr} (hm : Entails Δ (.defined m)) (x : Bool) :
    action modes p m x = action modes c m x := by
  rw [action_formula hp hm, action_formula hc hm, ←he]
  exact (sameInputs_any hi m.freeVariables).modalWith (fun _ h => h) x

theorem action_idempotent {modes} (d : Description State) (m : ModExpr) (x : Bool) :
    action modes d m (action modes d m x) = action modes d m x := by
  cases hc : d.coordinate <;> simp [action, act, hc]

theorem pairOK_transfer {Δ modes} {p c : Description State}
    (hp : scalarOK Δ modes p = true) (hc : scalarOK Δ modes c = true)
    (h : pairOK modes p c = true) {m : ModExpr} (hm : Entails Δ (.defined m)) (x : Bool) :
    action modes p m (action modes c m x) = action modes p m x := by
  simp only [pairOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨he,hi⟩
  · simp only [action, h, act]
  · rw [←action_same hp hc he hi hm x]
    exact action_idempotent p m x

theorem modalValid {Δ types modes} {data : State → Description State}
    (hs : ∀ i, scalarOK Δ modes (data i) = true) :
    ModalValid Δ (nodes types modes data) := by
  constructor
  · intro i m hm x y hxy
    change action modes (data i) m x ≤ action modes (data i) m y
    rw [action_complete (hs i) hm, action_complete (hs i) hm]
    exact (transition (data i).coordinate (modeValue modes (data i))
      (scalarOK_correct.mp (hs i))).monotone m hm hxy
  · intro i x
    cases hc : (data i).coordinate <;>
      simp [nodes, action, ModExpr.eval, ModExpr.epsilon, act, hc, Mode.identity]
  · intro i m n hm hn x
    change action modes (data i) (.compose m n) x =
      action modes (data i) n (action modes (data i) m x)
    rw [action_complete (hs i) (Entails.defined_compose_iff.mpr ⟨hm,hn⟩),
      action_complete (hs i) hn, action_complete (hs i) hm]
    exact (transition (data i).coordinate (modeValue modes (data i))
      (scalarOK_correct.mp (hs i))).compose m n hm hn x
  · intro i m n hm hn x
    change action modes (data i) (.join m n) x =
      (action modes (data i) m x || action modes (data i) n x)
    have hmn : Entails Δ (.defined (.join m n)) := by
      simpa only [modeOp] using ComparisonDefinedCovers.modeOp_defined true hm hn
    rw [action_complete (hs i) hmn,
      action_complete (hs i) hm, action_complete (hs i) hn]
    exact (transition (data i).coordinate (modeValue modes (data i))
      (scalarOK_correct.mp (hs i))).join m n hm hn x
  · intro i m n hm hn x
    change action modes (data i) (.meet m n) x =
      (action modes (data i) m x && action modes (data i) n x)
    have hmn : Entails Δ (.defined (.meet m n)) := by
      simpa only [modeOp] using ComparisonDefinedCovers.modeOp_defined false hm hn
    rw [action_complete (hs i) hmn,
      action_complete (hs i) hm, action_complete (hs i) hn]
    exact (transition (data i).coordinate (modeValue modes (data i))
      (scalarOK_correct.mp (hs i))).meet m n hm hn x
  · intro i m n hmn x
    change action modes (data i) m x ≤ action modes (data i) n x
    rw [action_complete (hs i) hmn.defined.1, action_complete (hs i) hmn.defined.2]
    exact (transition (data i).coordinate (modeValue modes (data i))
      (scalarOK_correct.mp (hs i))).submode m n hmn x

structure Local (Δ : Bounds) (types : List TypeVar) (modes : List ModVar)
    (data : State → Description State) (i : State) : Prop where
  scalar : scalarOK Δ modes (data i) = true
  unit : (data i).range (data i).unitValue = true
  credit : (data i).range (data i).creditValue = true
  atom : ∀v∈types, (data i).range (atomValue types (data i) v) = true
  closed : closedRange (data i) = true
  branch : ∀k, branchRange data i k = true
  prod : pairOK modes (data i) (data ((data i).branch .prod).next) = true
  sum : pairOK modes (data i) (data ((data i).branch .sum).next) = true
  fn : functionRange data i = true
  declared : declared Δ types modes data i = true

theorem checkNode_correct {Δ types modes} {data : State → Description State} {i} :
    checkNode Δ types modes data i = true ↔ Local Δ types modes data i := by
  simp only [checkNode, List.all_cons, List.all_nil, id_eq, Bool.and_eq_true, and_true,
    List.all_eq_true]
  constructor
  · rintro ⟨hs,hu,hc,ha,hr,hp,hsm,hf,hpp,hps,hff,hb⟩
    exact ⟨hs,hu,hc,ha,hr,(fun k => by cases k; exact hp; exact hsm; exact hf),hpp,hps,hff,hb⟩
  · intro h
    exact ⟨h.scalar,h.unit,h.credit,h.atom,h.closed,h.branch .prod,h.branch .sum,
      h.branch .fn,h.prod,h.sum,h.fn,h.declared⟩

theorem closedRange_correct (d : Description State) :
    closedRange d = true ↔
      ComparisonStructuralCoherence.ClosedRange d.coordinate (fun x => d.range x = true) := by
  cases hc : d.coordinate <;> simp [closedRange, ComparisonStructuralCoherence.ClosedRange, hc, Bool.eq_false_iff,
    imp_iff_not_or, -Bool.not_eq_true]

theorem branchRange_correct {data : State → Description State} {i k} :
    branchRange data i k = true ↔
      ∀x, (data ((data i).branch k).next).range x = true →
        (data i).range (sign k ((data i).branch k).left x) = true := by
  simp [branchRange, Bool.forall_bool, Bool.eq_false_iff, imp_iff_not_or, -Bool.not_eq_true]

theorem functionRange_correct {data : State → Description State} {i} :
    functionRange data i = true ↔
      (data i).coordinate = .uniqueness → ∀x,
        (data ((data i).branch .fn).next).range x = true →
          sign .fn ((data i).branch .fn).left x = true := by
  simp [functionRange, Bool.forall_bool, Bool.eq_false_iff, imp_iff_not_or, -Bool.not_eq_true]

theorem local_coherent {Δ types modes} {data : State → Description State}
    (h : ∀i, Local Δ types modes data i) : Coherent Δ (nodes types modes data) := by
  constructor
  · intro i k hk m hm x _
    apply pairOK_transfer (h i).scalar (h ((data i).branch k).next).scalar _ hm
    rcases hk with rfl | rfl
    · exact (h i).prod
    · exact (h i).sum
  · intro i m n hmn x hx
    change action modes (data i) m (sign .fn ((data i).branch .fn).left x) ≤
      action modes (data i) n (sign .fn ((data i).branch .fn).left x)
    rw [action_complete (h i).scalar hmn.defined.1,
      action_complete (h i).scalar (Entails.defined_compose_iff.mp hmn.defined.2).1]
    apply ComparisonStructuralCoherence.complete_fn _ _
      (scalarOK_correct.mp (h i).scalar) _ _ hmn
    exact fun hc => (functionRange_correct.mp (h i).fn) hc x hx

theorem local_range {Δ types modes} {data : State → Description State}
    (h : ∀i, Local Δ types modes data i) : RangeClosed Δ (nodes types modes data) := by
  constructor
  · intro i v
    by_cases hv : v ∈ types
    · exact (h i).atom v hv
    · simpa [nodes, atomValue, hv] using (h i).unit
  · exact fun i => (h i).unit
  · exact fun i => (h i).credit
  · exact fun i k x hx => (branchRange_correct.mp ((h i).branch k)) x hx
  · intro i m _ x hx
    change (data i).range (action modes (data i) m x) = true
    unfold action
    rw [act_eq]
    exact (ComparisonStructuralCoherence.closedRange_iff _ _).mp
      (closedRange_correct (data i) |>.mp (h i).closed) x hx _

theorem declared_correct {Δ types modes} {data : State → Description State} {i} :
    declared Δ types modes data i = true ↔
      ∀a b, Constraint.sub a b ∈ Δ →
        value (nodes types modes data) (.ofTy a) i ≤
          value (nodes types modes data) (.ofTy b) i := by
  simp only [declared, List.all_eq_true]
  constructor
  · intro h a b hab
    have hh := h (.sub a b) hab
    simpa [Bool.le_iff_imp, Bool.eq_false_iff, imp_iff_not_or, -Bool.not_eq_true] using hh
  · intro h c hc
    cases c <;> simp only
    exact (by simpa [Bool.le_iff_imp, Bool.eq_false_iff, imp_iff_not_or, -Bool.not_eq_true]
      using (h _ _ hc))

theorem check_correct {count : Nat} {Δ types modes}
    {data : Fin count → Description (Fin count)} :
    check Δ types modes data = true ↔ ∀i, Local Δ types modes data i := by
  simp only [check, List.all_eq_true, List.mem_finRange, forall_true_left, checkNode_correct]

/-- Acceptance certifies genuine algebra observers, including every whole
original declared type edge and every guarded modal law. -/
theorem check_sound {count : Nat} {Δ types modes}
    {data : Fin count → Description (Fin count)} (h : check Δ types modes data = true) :
    Certified Δ (nodes types modes data) := by
  have hl := check_correct.mp h
  exact ⟨modalValid (fun i => (hl i).scalar), local_range hl, local_coherent hl,
    fun i => declared_correct.mp (hl i).declared⟩

noncomputable def checkedObserver {count : Nat} {Δ shape types modes}
    {data : Fin count → Description (Fin count)} (h : check Δ types modes data = true)
    (hΔ : Bounds.TypeBoundsDefined Δ) (i : Fin count) : LatticeHom (Order Δ shape) Bool :=
  (check_sound h).observer hΔ i

theorem checkedObserver_value {count : Nat} {Δ shape types modes}
    {data : Fin count → Description (Fin count)} (h : check Δ types modes data = true)
    (hΔ : Bounds.TypeBoundsDefined Δ) (i : Fin count) (a : Carrier Δ shape) :
    ComparisonAlgebra.observer (checkedObserver h hΔ i) a =
      value (nodes types modes data) a.type i := rfl

theorem checked_subtype {count : Nat} {Δ types modes}
    {data : Fin count → Description (Fin count)} (h : check Δ types modes data = true)
    (hΔ : Bounds.TypeBoundsDefined Δ) {a b : CompareTy}
    (ha : a.DefinedUnder Δ) (hb : b.DefinedUnder Δ) (hab : AlgebraSubtype Δ a b) (i : Fin count) :
    value (nodes types modes data) a i ≤ value (nodes types modes data) b i :=
  subtype_mono (check_sound h).modal (check_sound h).range (check_sound h).coherent
    (check_sound h).bounds hΔ ha hb hab i

end ModalityInference.ComparisonObserverMachineCheck
