import ModalityInference.Proofs.ComparisonObserverMachineCheck

/-! Duplicating observer states preserves finite checks and all term values.
A single description size therefore suffices at any larger fixed bound. -/
namespace ModalityInference.ComparisonObserverMachinePadding

open ComparisonObserverMachine ComparisonObserverMachineCheck

variable {S T : Type}

def reindex (data : S → Description S) (up : S → T) (down : T → S)
    (i : T) : Description T where
  atoms := (data (down i)).atoms
  modes := (data (down i)).modes
  coordinate := (data (down i)).coordinate
  unitValue := (data (down i)).unitValue
  creditValue := (data (down i)).creditValue
  branch k := ⟨((data (down i)).branch k).left, up ((data (down i)).branch k).next⟩
  range := (data (down i)).range

theorem reindex_value (data : S → Description S) (up : S → T) (down : T → S)
    (h : ∀i, down (up i) = i) (types : List TypeVar) (modes : List ModVar)
    (a : CompareTy) (i : T) :
    value (nodes types modes (reindex data up down)) a i = value (nodes types modes data) a (down i) := by
  induction a generalizing i <;> simp_all [value, nodes, reindex] <;> rfl

theorem reindex_declared (data : S → Description S) (up : S → T) (down : T → S)
    (h : ∀i, down (up i) = i) (Δ : Bounds) (types : List TypeVar) (modes : List ModVar) (i : T) :
    declared Δ types modes (reindex data up down) i = declared Δ types modes data (down i) := by
  simp only [declared]
  congr 1
  funext c
  cases c <;> simp only [reindex_value data up down h]

theorem reindex_checkNode (data : S → Description S) (up : S → T) (down : T → S)
    (h : ∀i, down (up i) = i) (Δ : Bounds) (types : List TypeVar) (modes : List ModVar) (i : T) :
    checkNode Δ types modes (reindex data up down) i = checkNode Δ types modes data (down i) := by
  simp only [checkNode, reindex_declared data up down h, scalarOK, atomValue, modeValue,
    closedRange, branchRange, pairOK, sameInputs, functionRange, reindex, h]
  rfl

theorem reindex_check {count size : Nat} (data : Fin count → Description (Fin count))
    (up : Fin count → Fin size) (down : Fin size → Fin count) (h : ∀i, down (up i) = i)
    (Δ : Bounds) (types : List TypeVar) (modes : List ModVar) :
    check Δ types modes (reindex data up down) = check Δ types modes data := by
  apply Bool.eq_iff_iff.mpr
  simp only [check, List.all_eq_true, List.mem_finRange, forall_true_left,
    reindex_checkNode data up down h]
  constructor
  · intro hh i
    simpa only [h] using hh (up i)
  · exact fun h i => h (down i)

def lower {count size : Nat} (fallback : Fin count) (i : Fin size) : Fin count :=
  if h : i.val < count then ⟨i.val,h⟩ else fallback

theorem lower_castLE {count size : Nat} (h : count ≤ size) (fallback : Fin count) (i : Fin count) :
    lower fallback (i.castLE h) = i := by
  simp [lower, i.isLt]

def pad {count size : Nat} (h : count ≤ size) (fallback : Fin count)
    (data : Fin count → Description (Fin count)) : Fin size → Description (Fin size) :=
  reindex data (Fin.castLE h) (lower fallback)

theorem pad_check {count size : Nat} (h : count ≤ size) (fallback : Fin count)
    (data : Fin count → Description (Fin count)) (Δ : Bounds)
    (types : List TypeVar) (modes : List ModVar) :
    check Δ types modes (pad h fallback data) = check Δ types modes data :=
  reindex_check data _ _ (lower_castLE h fallback) Δ types modes

theorem pad_value {count size : Nat} (h : count ≤ size) (fallback : Fin count)
    (data : Fin count → Description (Fin count)) (types : List TypeVar) (modes : List ModVar)
    (a : CompareTy) (i : Fin count) :
    value (nodes types modes (pad h fallback data)) a (i.castLE h) =
      value (nodes types modes data) a i := by
  rw [pad, reindex_value data _ _ (lower_castLE h fallback), lower_castLE]

end ModalityInference.ComparisonObserverMachinePadding
