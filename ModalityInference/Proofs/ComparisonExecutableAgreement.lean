import ModalityInference.ComparisonExecutableAgreement
import ModalityInference.Proofs.ComparisonExecutableTables
import ModalityInference.Proofs.ComparisonRelativeSyntaxDefined

/-! The finite embedding checks are equivalent to the corresponding universal
laws. Matching the supplied operations to a defined range algebra then yields
the existing defined-agreement contract. -/
namespace ModalityInference.ComparisonExecutableAgreement

open ComparisonRelativeCoordinates

variable {D M O : Type*} (values : List D) (indices : List M) (observations : List O)
  (hd : ∀ x, x ∈ values) (hm : ∀ m, m ∈ indices) (ho : ∀ o, o ∈ observations)
  (E : Operations D M O) (j : D → Vector M O)

include hm ho in
theorem vectorEq_correct (x y : Vector M O) :
    vectorEq indices observations x y = true ↔ x = y := by
  simp only [vectorEq,List.all_eq_true,beq_iff_eq]
  exact ⟨fun h => funext fun m => funext fun o => h m (hm m) o (ho o),
    fun h _ _ _ _ => congrFun (congrFun h _) _⟩

include hm ho in
theorem vectorBelow_correct (x y : Vector M O) :
    vectorBelow indices observations x y = true ↔ x ≤ y := by
  simp only [vectorBelow,List.all_eq_true,ComparisonExecutableTables.below_correct observations ho]
  exact ⟨fun h m => h m (hm m),fun h m _ => h m⟩

structure Valid : Prop where
  index : ∀ x m n, E.indexLe m n = true → j x m ≤ j x n
  join : ∀ x y, j (E.join x y) = fun m o => j x m o || j y m o
  meet : ∀ x y, j (E.meet x y) = fun m o => j x m o && j y m o
  reflect : ∀ x y, j x ≤ j y → E.domainLe x y = true
  action : ∀ m x, (fun n => j x (E.mul m n)) = j (E.action m x)
  prod : ∀ x y, E.vectorProd (j x) (j y) = j (E.prod x y)
  sum : ∀ x y, E.vectorSum (j x) (j y) = j (E.sum x y)
  fn : ∀ x y, E.vectorFn (j x) (j y) = j (E.fn x y)

private theorem implies_true (a b : Bool) : (!a || b) = true ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

include hd hm ho in
theorem indexCheck_correct : indexCheck values indices observations E j = true ↔
    ∀ x m n, E.indexLe m n = true → j x m ≤ j x n := by
  simp only [indexCheck,List.all_eq_true,implies_true,
    ComparisonExecutableTables.below_correct observations ho]
  exact ⟨fun h x m n => h x (hd x) m (hm m) n (hm n),fun h x _ m _ n _ => h x m n⟩

include hd hm ho in
theorem latticeCheck_correct : latticeCheck values indices observations E j = true ↔
    (∀ x y, j (E.join x y) = fun m o => j x m o || j y m o) ∧
    (∀ x y, j (E.meet x y) = fun m o => j x m o && j y m o) := by
  simp only [latticeCheck,List.all_eq_true,Bool.and_eq_true,vectorEq_correct indices observations hm ho]
  exact ⟨fun h => ⟨fun x y => (h x (hd x) y (hd y)).1,fun x y => (h x (hd x) y (hd y)).2⟩,
    fun h x _ y _ => ⟨h.1 x y,h.2 x y⟩⟩

include hd hm ho in
theorem reflectCheck_correct : reflectCheck values indices observations E j = true ↔
    ∀ x y, j x ≤ j y → E.domainLe x y = true := by
  simp only [reflectCheck,List.all_eq_true,implies_true,vectorBelow_correct indices observations hm ho]
  exact ⟨fun h x y => h x (hd x) y (hd y),fun h x _ y _ => h x y⟩

include hd hm ho in
theorem actionCheck_correct : actionCheck values indices observations E j = true ↔
    ∀ m x, (fun n => j x (E.mul m n)) = j (E.action m x) := by
  simp only [actionCheck,List.all_eq_true,vectorEq_correct indices observations hm ho]
  exact ⟨fun h m x => h m (hm m) x (hd x),fun h m _ x _ => h m x⟩

include hd hm ho in
theorem constructorCheck_correct (op : D → D → D)
    (vectorOp : Vector M O → Vector M O → Vector M O) :
    constructorCheck values indices observations j op vectorOp = true ↔
      ∀ x y, vectorOp (j x) (j y) = j (op x y) := by
  simp only [constructorCheck,List.all_eq_true,vectorEq_correct indices observations hm ho]
  exact ⟨fun h x y => h x (hd x) y (hd y),fun h x _ y _ => h x y⟩

include hd hm ho in
theorem check_correct : check values indices observations E j = true ↔ Valid E j := by
  simp only [check,Bool.and_eq_true,indexCheck_correct values indices observations hd hm ho,
    latticeCheck_correct values indices observations hd hm ho,reflectCheck_correct values indices observations hd hm ho,
    actionCheck_correct values indices observations hd hm ho,constructorCheck_correct values indices observations hd hm ho]
  exact ⟨fun ⟨⟨⟨⟨⟨⟨hi,⟨hj,hmt⟩⟩,hr⟩,ha⟩,hp⟩,hs⟩,hf⟩ =>
      ⟨hi,hj,hmt,hr,ha,hp,hs,hf⟩,
    fun h => ⟨⟨⟨⟨⟨⟨h.index,⟨h.join,h.meet⟩⟩,h.reflect⟩,h.action⟩,h.prod⟩,h.sum⟩,h.fn⟩⟩

namespace Valid

variable {E j} (h : Valid E j)

section Lattice
variable [Lattice D] [PartialOrder M]
  (hi : ∀ m n, E.indexLe m n = true ↔ m ≤ n)
  (hj : ∀ x y, E.join x y = x ⊔ y) (ht : ∀ x y, E.meet x y = x ⊓ y)

def embedding : LatticeHom D (Coordinates M (O → Bool)) where
  toFun x := ⟨j x,fun m n hmn => h.index x m n ((hi m n).mpr hmn)⟩
  map_sup' x y := by
    ext m o
    exact congrFun (congrFun ((congrArg j (hj x y)).symm.trans (h.join x y)) m) o
  map_inf' x y := by
    ext m o
    exact congrFun (congrFun ((congrArg j (ht x y)).symm.trans (h.meet x y)) m) o

@[simp] theorem embedding_apply (x : D) (m : M) (o : O) :
    h.embedding hi hj ht x m o = j x m o := rfl

theorem embedding_reflect (hl : ∀ x y, E.domainLe x y = true ↔ x ≤ y)
    {x y : D} (hxy : h.embedding hi hj ht x ≤ h.embedding hi hj ht y) : x ≤ y :=
  (hl x y).mp (h.reflect x y hxy)

end Lattice
end Valid

section Defined

open ComparisonRelativeSyntax ComparisonFiniteControls ComparisonFiniteControlProjection
  ComparisonObserverMachine ComparisonObserverFiniteRange ComparisonFiniteControlRange

variable {Δ : Bounds} {names : List ModVar} {State : Type} {nodes : State → Node State}
  {A O : Type*} {embed : A → O → Bool}
  (S : Model Δ (Control Δ names) A O embed)
  (hv : ModalValid Δ nodes) (hr : RangeClosed Δ nodes)
  (E : Operations (ComparisonObserverFiniteRange.Value nodes) (Control Δ names) O)
  (j : ComparisonObserverFiniteRange.Value nodes → Vector (Control Δ names) O)

/-- These equations identify the executable primitive operations with the
semantic operations. The embedding laws themselves are checked separately. -/
structure Matches : Prop where
  domainLe : ∀ x y, E.domainLe x y = true ↔ x ≤ y
  indexLe : ∀ m n, E.indexLe m n = true ↔ m ≤ n
  join : ∀ x y, E.join x y = x ⊔ y
  meet : ∀ x y, E.meet x y = x ⊓ y
  mul : ∀ m n, E.mul m n = m * n
  action : ∀ m x, E.action m x = action hv hr m x
  prod : ∀ x y, E.prod x y = op hr .prod x y
  sum : ∀ x y, E.sum x y = op hr .sum x y
  fn : ∀ x y, E.fn x y = op hr .fn x y
  vectorProd : ∀ x y m o, E.vectorProd (j x) (j y) m o =
    (S.prodTable none).extend m (j x m) (j y m) o
  vectorSum : ∀ x y m o, E.vectorSum (j x) (j y) m o =
    (S.sumTable none).extend m (j x m) (j y m) o
  vectorFn : ∀ x y m o, E.vectorFn (j x) (j y) m o =
    S.fnTable.extend m (j x 1) (j y 1) o

variable {S hv hr E j}

/-- Finite validation supplies all quantified embedding laws required for
guarded equations and clamp. Base values and scalar control translation stay
explicit, since they belong to the syntax-data adapter. -/
theorem Valid.definedAgreement (h : Valid E j) (w : Matches S hv hr E j)
    (hnames : Δ.modVars ⊆ names.toFinset)
    (hcontrols : ∀ m hm, S.controls.toFun m hm = project hnames m hm)
    (hatom : ∀ v, S.atom v = h.embedding w.indexLe w.join w.meet (atom hr v))
    (hunit : S.unit = h.embedding w.indexLe w.join w.meet (unit hr))
    (hcredit : S.credit = h.embedding w.indexLe w.join w.meet (credit hr)) :
    DefinedAgreement S hv hr hnames (h.embedding w.indexLe w.join w.meet) where
  controls := hcontrols
  reflect := h.embedding_reflect w.indexLe w.join w.meet w.domainLe
  atom := hatom
  unit := hunit
  credit := hcredit
  action m x := by
    ext n o
    change j x (m * n) o = j (ComparisonFiniteControlRange.action hv hr m x) n o
    simpa only [w.mul,w.action] using congrFun (congrFun (h.action m x) n) o
  prod x y := by
    ext m o
    exact (w.vectorProd x y m o).symm.trans
      ((congrFun (congrFun (h.prod x y) m) o).trans (by rw [w.prod]; rfl))
  sum x y := by
    ext m o
    exact (w.vectorSum x y m o).symm.trans
      ((congrFun (congrFun (h.sum x y) m) o).trans (by rw [w.sum]; rfl))
  fn x y := by
    ext m o
    exact (w.vectorFn x y m o).symm.trans
      ((congrFun (congrFun (h.fn x y) m) o).trans (by rw [w.fn]; rfl))

end Defined

end ModalityInference.ComparisonExecutableAgreement
