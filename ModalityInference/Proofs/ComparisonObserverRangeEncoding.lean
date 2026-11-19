import ModalityInference.ComparisonObserverRangeEncoding
import ModalityInference.Proofs.ComparisonObserverFiniteRange

/-! The executable admitted-vector list enumerates exactly the finite range
algebra. Primitive vector operations agree with its semantic operations. -/
namespace ModalityInference.ComparisonObserverRangeEncoding

open ComparisonObserverMachine ComparisonObserverMachineCheck ComparisonStructuralLayout

theorem mem_allBits {count} (x : Bits count) : x ∈ allBits count := by
  induction count with
  | zero =>
    have hx : x = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [allBits,hx]
  | succ n ih =>
    let tail : Bits n := fun i => x i.succ
    have hx : Fin.cases (x 0) tail = x := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    apply List.mem_flatMap.mpr
    refine ⟨tail,ih tail,?_⟩
    rw [←hx]
    cases x 0 <;> simp

@[simp] theorem le_correct {count} (x y : Bits count) : le x y = true ↔ x ≤ y := by
  simp [le,Pi.le_def,Bool.le_iff_imp,Bool.eq_false_iff,imp_iff_not_or,-Bool.not_eq_true]

@[simp] theorem equal_correct {count} (x y : Bits count) : equal x y = true ↔ x = y := by
  simp [equal,funext_iff]

variable {count : Nat} {data : Fin count → Description (Fin count)}

@[simp] theorem admitted_correct (x : Bits count) :
    admitted data x = true ↔ ∀ i, (data i).range (x i) = true := by
  simp [admitted]

@[simp] theorem mem_vectors (x : Bits count) : x ∈ vectors data ↔ admitted data x = true := by
  simp [vectors,mem_allBits]

variable {types : List TypeVar} {modes : List ModVar}

def pack (x : ComparisonObserverFiniteRange.Value (nodes types modes data)) : Bits count :=
  fun i => (x i).val

theorem pack_admitted (x : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    admitted data (pack x) = true := admitted_correct _ |>.mpr (fun i => (x i).property)

def unpack (x : Bits count) (hx : admitted data x = true) :
    ComparisonObserverFiniteRange.Value (nodes types modes data) :=
  fun i => ⟨x i,admitted_correct x |>.mp hx i⟩

@[simp] theorem pack_unpack (x : Bits count) (hx : admitted data x = true) :
    pack (unpack (types := types) (modes := modes) x hx) = x := rfl

@[simp] theorem unpack_pack (x : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    unpack (pack x) (pack_admitted x) = x := rfl

@[simp] theorem pack_le (x y : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    pack x ≤ pack y ↔ x ≤ y := Iff.rfl

def rangeEquiv : {x : Bits count // admitted data x = true} ≃o
    ComparisonObserverFiniteRange.Value (nodes types modes data) where
  toFun x := unpack x.val x.property
  invFun x := ⟨pack x,pack_admitted x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- A finite Boolean check over the admitted-vector list quantifies over the
entire semantic range algebra, including values not represented by a term. -/
theorem all_vectors (test : Bits count → Bool) :
    (vectors data).all test = true ↔
      ∀ x : ComparisonObserverFiniteRange.Value (nodes types modes data), test (pack x) = true := by
  rw [List.all_eq_true]
  constructor
  · exact fun h x => h _ ((mem_vectors _).mpr (pack_admitted x))
  · intro h x hx
    exact h (unpack x ((mem_vectors _).mp hx))

/-- Executable enumeration of the existing range-value type, without using
its noncomputable `Fintype` instance. Membership proofs are erased at runtime. -/
def values : List (ComparisonObserverFiniteRange.Value (nodes types modes data)) :=
  (vectors data).attach.map fun x => unpack x.val ((mem_vectors _).mp x.property)

theorem mem_values (x : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    x ∈ values := by
  apply List.mem_map.mpr
  refine ⟨⟨pack x,(mem_vectors _).mpr (pack_admitted x)⟩,by simp,?_⟩
  exact unpack_pack x

theorem all_values (test : ComparisonObserverFiniteRange.Value (nodes types modes data) → Bool) :
    values.all test = true ↔ ∀ x, test x = true := by
  rw [List.all_eq_true]
  exact ⟨fun h x => h x (mem_values x),fun h x _ => h x⟩

@[simp] theorem pack_sup (x y : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    pack (x ⊔ y) = join (pack x) (pack y) :=
  funext fun i => ComparisonObserverFiniteRange.sup_val x y i

@[simp] theorem pack_inf (x y : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    pack (x ⊓ y) = meet (pack x) (pack y) :=
  funext fun i => ComparisonObserverFiniteRange.inf_val x y i

theorem admitted_join {x y : Bits count}
    (hx : admitted data x = true) (hy : admitted data y = true) :
    admitted data (join x y) = true := by
  apply (admitted_correct _).mpr
  intro i
  have hxi := admitted_correct x |>.mp hx i
  have hyi := admitted_correct y |>.mp hy i
  cases he : x i <;> cases hf : y i <;> simp_all [join]

theorem admitted_meet {x y : Bits count}
    (hx : admitted data x = true) (hy : admitted data y = true) :
    admitted data (meet x y) = true := by
  apply (admitted_correct _).mpr
  intro i
  have hxi := admitted_correct x |>.mp hx i
  have hyi := admitted_correct y |>.mp hy i
  cases he : x i <;> cases hf : y i <;> simp_all [meet]

variable {Δ : Bounds} (hr : RangeClosed Δ (nodes types modes data))

@[simp] theorem pack_unit : pack (ComparisonObserverFiniteRange.unit hr) = unit data := rfl

@[simp] theorem pack_credit : pack (ComparisonObserverFiniteRange.credit hr) = credit data := rfl

@[simp] theorem pack_atom (v : TypeVar) :
    pack (ComparisonObserverFiniteRange.atom hr v) = atom data types v := rfl

@[simp] theorem pack_modal (m : ModExpr) (hm : Entails Δ (.defined m))
    (x : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    pack (ComparisonObserverFiniteRange.modal hr m hm x) = modal data modes m (pack x) := rfl

@[simp] theorem pack_op (k : Constructor)
    (x y : ComparisonObserverFiniteRange.Value (nodes types modes data)) :
    pack (ComparisonObserverFiniteRange.op hr k x y) = op data k (pack x) (pack y) := by
  funext i
  simp only [pack,ComparisonObserverFiniteRange.op,op,nodes]
  split <;> rfl

@[simp] theorem pack_eval (a : CompareTy) (ha : a.DefinedUnder Δ) :
    pack (ComparisonObserverFiniteRange.eval hr a ha) = eval data types modes a := rfl

include hr

theorem admitted_unit : admitted data (unit data) = true :=
  pack_admitted (ComparisonObserverFiniteRange.unit hr)

theorem admitted_credit : admitted data (credit data) = true :=
  pack_admitted (ComparisonObserverFiniteRange.credit hr)

theorem admitted_atom (v : TypeVar) : admitted data (atom data types v) = true :=
  pack_admitted (ComparisonObserverFiniteRange.atom hr v)

theorem admitted_modal (m : ModExpr) (hm : Entails Δ (.defined m))
    {x : Bits count} (hx : admitted data x = true) :
    admitted data (modal data modes m x) = true :=
  pack_admitted (ComparisonObserverFiniteRange.modal hr m hm (unpack x hx))

theorem admitted_op (k : Constructor) {x y : Bits count}
    (hx : admitted data x = true) (hy : admitted data y = true) :
    admitted data (op data k x y) = true := by
  simpa only [pack_op,pack_unpack] using
    pack_admitted (ComparisonObserverFiniteRange.op hr k (unpack x hx) (unpack y hy))

theorem admitted_eval (a : CompareTy) (ha : a.DefinedUnder Δ) :
    admitted data (eval data types modes a) = true :=
  pack_admitted (ComparisonObserverFiniteRange.eval hr a ha)

end ModalityInference.ComparisonObserverRangeEncoding
