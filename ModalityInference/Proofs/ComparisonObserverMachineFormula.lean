import ModalityInference.ComparisonObserverMachineFormula
import ModalityInference.Proofs.ComparisonObserverMachineCheck

/-! Exact semantics of symbolic observer-machine certificates. Priority
successors are compiled as multiplexers and retain structural term recursion. -/
namespace ModalityInference.ComparisonObserverMachineFormula

open ComparisonControls ComparisonStructuralLayout ComparisonObserverMachine

@[simp] theorem mux_eval (p a b : BoolExpr) (world : Nat → Bool) :
    (mux p a b).eval world = if p.eval world then a.eval world else b.eval world := by
  cases h : p.eval world <;> simp [mux, BoolExpr.eval, h]

@[simp] theorem all_map_eval {α} (xs : List α) (f : α → BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all (xs.map f)).eval world = xs.all (fun x => (f x).eval world) := by
  induction xs <;> simp_all [BoolExpr.all, BoolExpr.eval]

@[simp] theorem equal_eval (a b : BoolExpr) (world : Nat → Bool) :
    (BoolExpr.equal a b).eval world = (a.eval world == b.eval world) := by
  simp only [BoolExpr.equal, BoolExpr.eval]
  cases a.eval world <;> cases b.eval world <;> rfl

private theorem mapped_getD {α β} (f : α → β) (xs : List α) (i : Nat) (d : α) :
    (xs.map f)[i]?.getD (f d) = f (xs[i]?.getD d) := by
  simp only [List.getElem?_map]
  cases xs[i]? <;> rfl

@[simp] theorem atom_eval {count} (types : List TypeVar) (data : Fin count → Fields count)
    (i : Fin count) (v : TypeVar) (world : Nat → Bool) :
    (atom types (data i) v).eval world =
      ComparisonObserverMachineCheck.atomValue types (decode data world i) v := by
  simp only [atom, ComparisonObserverMachineCheck.atomValue, decode]
  split <;> simp only [mapped_getD]

theorem mode_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i : Fin count) (v : ModVar) (world : Nat → Bool) :
    scalar (mode names (data i) v) world =
      ComparisonObserverMachineCheck.modeValue names (decode data world i) v := by
  simp only [mode, ComparisonObserverMachineCheck.modeValue, decode]
  split
  · exact (mapped_getD (fun s => scalar s world) (data i).modes (names.idxOf v)
      (.const true,.const true,.const true)).symm
  · rfl

@[simp] theorem modeAtom_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i : Fin count) (u : Nat) (world : Nat → Bool) :
    (modeAtom names (data i) u).eval world = ComparisonObserverMachineCheck.bits
      (ComparisonObserverMachineCheck.modeValue names (decode data world i)) u := by
  unfold modeAtom ComparisonObserverMachineCheck.bits
  rw [←mode_eval names data i (SymbolicModes.atomVariable u) world]
  split <;> simp_all only [scalar]

@[simp] theorem modesFormula_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i : Fin count) (e : BoolExpr) (world : Nat → Bool) :
    (modesFormula names (data i) e).eval world = e.eval (ComparisonObserverMachineCheck.bits
      (ComparisonObserverMachineCheck.modeValue names (decode data world i))) := by
  simp [modesFormula]

theorem action_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i : Fin count) (m : ModExpr) (x : BoolExpr) (world : Nat → Bool) :
    (action names (data i) m x).eval world =
      ComparisonObserverMachineCheck.action names (decode data world i) m (x.eval world) := by
  have hp := m.project_correct (ComparisonObserverMachineCheck.bits
    (ComparisonObserverMachineCheck.modeValue names (decode data world i)))
  simp only [ComparisonObserverMachineCheck.bits_eq, projectedModes_encodeModes] at hp
  simp only [action, mux_eval, modesFormula_eval, BoolExpr.eval,
    ComparisonObserverMachineCheck.action, ←hp, Projection.eval]
  simp only [ComparisonObserverMachineCheck.bits_eq]
  cases hd : m.project.defined.eval (encodeModes
      (ComparisonObserverMachineCheck.modeValue names (decode data world i))) <;>
    cases hf : (data i).first.eval world <;> cases hs : (data i).second.eval world <;>
    simp [decode, coordinate, hf, hs, ComparisonObserverMachineCheck.act, Mode.identity]

@[simp] theorem choose_eval {α} (fallback : α) (test values : α → BoolExpr)
    (xs : List α) (world : Nat → Bool) :
    (choose (values fallback) test values xs).eval world =
      (values (firstTrue fallback (fun x => (test x).eval world) xs)).eval world := by
  induction xs <;> simp_all [choose, firstTrue, apply_ite]

@[simp] theorem successor_eval {count} (data : Fin count → Fields count)
    (i : Fin count) (k : Constructor) (values : Fin count → BoolExpr) (world : Nat → Bool) :
    (successor data i k values).eval world =
      (values ((decode data world i).branch k).next).eval world := by
  exact choose_eval i ((data i).next k) values (List.finRange count) world

theorem value_eval {count} (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (a : CompareTy) (i : Fin count) (world : Nat → Bool) :
    (value types names data a i).eval world =
      ComparisonObserverMachine.value
        (ComparisonObserverMachineCheck.nodes types names (decode data world)) a i := by
  induction a generalizing i with
  | var v => exact atom_eval types data i v world
  | unit | credit => rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [value, mux_eval, successor_eval, BoolExpr.eval, iha, ihb,
      ComparisonObserverMachine.value, ComparisonObserverMachineCheck.nodes, decode, Bool.or_false]
  | modal a m ih =>
    simp only [value, action_eval, ih, ComparisonObserverMachine.value,
      ComparisonObserverMachineCheck.nodes]
  | join a b iha ihb | meet a b iha ihb =>
    simp only [value, BoolExpr.eval, iha, ihb, ComparisonObserverMachine.value]

@[simp] theorem unaffected_eval {count} (data : Fin count → Fields count) (i : Fin count)
    (world : Nat → Bool) :
    (unaffected (data i)).eval world = decide ((decode data world i).coordinate = .unaffected) := by
  cases hf : (data i).first.eval world <;> cases hs : (data i).second.eval world <;>
    simp [unaffected, BoolExpr.eval, decode, coordinate, hf, hs]

@[simp] theorem unique_eval {count} (data : Fin count → Fields count) (i : Fin count)
    (world : Nat → Bool) :
    (unique (data i)).eval world = decide ((decode data world i).coordinate = .uniqueness) := by
  cases hf : (data i).first.eval world <;> cases hs : (data i).second.eval world <;>
    simp [unique, BoolExpr.eval, decode, coordinate, hf, hs]

@[simp] theorem scalarOK_eval {count} (Δ : Bounds) (names : List ModVar)
    (data : Fin count → Fields count) (i : Fin count) (world : Nat → Bool) :
    (scalarOK Δ names (data i)).eval world =
      ComparisonObserverMachineCheck.scalarOK Δ names (decode data world i) := by
  simp only [scalarOK, BoolExpr.eval, unaffected_eval, modesFormula_eval,
    ComparisonObserverMachineCheck.scalarOK]

@[simp] theorem mode_local_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i : Fin count) (v : ModVar) (world : Nat → Bool) :
    (mode names (data i) v).1.eval world =
      (ComparisonObserverMachineCheck.modeValue names (decode data world i) v).isLocal :=
  congrArg Mode.isLocal (mode_eval names data i v world)

@[simp] theorem mode_affine_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i : Fin count) (v : ModVar) (world : Nat → Bool) :
    (mode names (data i) v).2.1.eval world =
      (ComparisonObserverMachineCheck.modeValue names (decode data world i) v).once :=
  congrArg Mode.once (mode_eval names data i v world)

@[simp] theorem mode_unique_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i : Fin count) (v : ModVar) (world : Nat → Bool) :
    (mode names (data i) v).2.2.eval world =
      (ComparisonObserverMachineCheck.modeValue names (decode data world i) v).unique :=
  congrArg Mode.unique (mode_eval names data i v world)

@[simp] theorem sameInputs_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i j : Fin count) (world : Nat → Bool) :
    (sameInputs names (data i) (data j)).eval world =
      ComparisonObserverMachineCheck.sameInputs names (decode data world i) (decode data world j) := by
  simp only [sameInputs, mux_eval, all_map_eval, BoolExpr.eval, equal_eval,
    mode_local_eval, mode_affine_eval, mode_unique_eval, ComparisonObserverMachineCheck.sameInputs]
  cases hf : (data j).first.eval world <;> cases hs : (data j).second.eval world <;>
    simp [decode, coordinate, hf, hs]

theorem coordinate_inj (a b c d : Bool) : coordinate a b = coordinate c d ↔ a = c ∧ b = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

@[simp] theorem pairOK_eval {count} (names : List ModVar) (data : Fin count → Fields count)
    (i j : Fin count) (world : Nat → Bool) :
    (pairOK names (data i) (data j)).eval world =
      ComparisonObserverMachineCheck.pairOK names (decode data world i) (decode data world j) := by
  simp only [pairOK, BoolExpr.eval, unaffected_eval, equal_eval, sameInputs_eval,
    ComparisonObserverMachineCheck.pairOK]
  have he (a b : Bool) : (a == b) = decide (a = b) := by cases a <;> cases b <;> rfl
  simp [decode, coordinate_inj, he]

@[simp] theorem closedRange_eval {count} (data : Fin count → Fields count)
    (i : Fin count) (world : Nat → Bool) :
    (closedRange (data i)).eval world = ComparisonObserverMachineCheck.closedRange (decode data world i) := by
  simp only [closedRange, mux_eval, BoolExpr.eval, ComparisonObserverMachineCheck.closedRange]
  cases hf : (data i).first.eval world <;> cases hs : (data i).second.eval world <;>
    simp [decode, coordinate, hf, hs]

@[simp] theorem signed_eval {count} (data : Fin count → Fields count) (i : Fin count)
    (k : Constructor) (x : Bool) (world : Nat → Bool) :
    (signed (data i) k x).eval world = sign k ((decode data world i).branch k).left x := by
  cases hk : k.dual <;> simp [signed, sign, decode, hk, BoolExpr.eval]

@[simp] theorem rangeAt_eval {count} (data : Fin count → Fields count) (i : Fin count)
    (x : BoolExpr) (world : Nat → Bool) :
    (rangeAt (data i) x).eval world = (decode data world i).range (x.eval world) := by
  simp only [rangeAt, mux_eval, decode]
  cases x.eval world <;> rfl

@[simp] theorem branchRange_eval {count} (data : Fin count → Fields count) (i : Fin count)
    (k : Constructor) (world : Nat → Bool) :
    (branchRange data i k).eval world = ComparisonObserverMachineCheck.branchRange (decode data world) i k := by
  simp only [branchRange, all_map_eval, BoolExpr.eval, successor_eval, rangeAt_eval, signed_eval,
    ComparisonObserverMachineCheck.branchRange, decode]

@[simp] theorem functionRange_eval {count} (data : Fin count → Fields count) (i : Fin count)
    (world : Nat → Bool) :
    (functionRange data i).eval world = ComparisonObserverMachineCheck.functionRange (decode data world) i := by
  simp only [functionRange, BoolExpr.eval, unique_eval, all_map_eval, successor_eval, signed_eval,
    ComparisonObserverMachineCheck.functionRange, decode]

@[simp] theorem declared_eval {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (i : Fin count) (world : Nat → Bool) :
    (declared Δ types names data i).eval world =
      ComparisonObserverMachineCheck.declared Δ types names (decode data world) i := by
  simp only [declared, all_map_eval, ComparisonObserverMachineCheck.declared]
  congr 1
  funext c
  cases c <;> simp only [BoolExpr.eval, value_eval]

@[simp] theorem all_cons_eval (e : BoolExpr) (es : List BoolExpr) (world : Nat → Bool) :
    (BoolExpr.all (e::es)).eval world = (e.eval world && (BoolExpr.all es).eval world) := rfl

@[simp] theorem all_nil_eval (world : Nat → Bool) :
    (BoolExpr.all []).eval world = true := rfl

@[simp] theorem checkNode_eval {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (i : Fin count) (world : Nat → Bool) :
    (checkNode Δ types names data i).eval world =
      ComparisonObserverMachineCheck.checkNode Δ types names (decode data world) i := by
  simp only [checkNode, all_cons_eval, all_nil_eval,
    scalarOK_eval, rangeAt_eval, all_map_eval, atom_eval, closedRange_eval, branchRange_eval,
    successor_eval, pairOK_eval, functionRange_eval, declared_eval,
    ComparisonObserverMachineCheck.checkNode, List.all_cons, List.all_nil, id_eq]
  rfl

/-- Exact compilation of the finite checker, including all partial evaluation
branches, without a prior consistency or scalar-model assumption. -/
theorem query_eval {count} (Δ : Bounds) (types : List TypeVar) (names : List ModVar)
    (data : Fin count → Fields count) (world : Nat → Bool) :
    (query Δ types names data).eval world =
      ComparisonObserverMachineCheck.check Δ types names (decode data world) := by
  simp only [query, all_map_eval, checkNode_eval, ComparisonObserverMachineCheck.check]

theorem query_sound {count} {Δ types names} {data : Fin count → Fields count} {world : Nat → Bool}
    (h : (query Δ types names data).eval world = true) :
    Certified Δ (ComparisonObserverMachineCheck.nodes types names (decode data world)) :=
  ComparisonObserverMachineCheck.check_sound ((query_eval Δ types names data world) ▸ h)

end ModalityInference.ComparisonObserverMachineFormula
