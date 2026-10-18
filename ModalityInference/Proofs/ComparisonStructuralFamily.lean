import ModalityInference.ComparisonStructuralFamily
import ModalityInference.Proofs.ComparisonStructuralMatrix
import ModalityInference.Proofs.ComparisonBasisReflection

/-! A common parent observer interprets all outer actions and reconstructed child
polynomials with one coordinate assignment. The executable family constraints
retain rectangular and inherited-action equations under the original guards. -/
namespace ModalityInference.ComparisonStructuralFamily

open ComparisonAlgebra ComparisonStructuralLattice ComparisonStructuralMatrix

noncomputable def actObserver {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (m : GuardedMode Δ) :
    LatticeHom (Order Δ shape) Bool where
  toFun := Quotient.lift (fun a => observer f (m.act a)) (by
    intro a b h
    apply congrArg f
    exact Quotient.sound ⟨.congr h.1 (.valid fun η hη =>
      ⟨_, _, m.eval η hη, m.eval η hη, Mode.le_refl _⟩),
      .congr h.2 (.valid fun η hη =>
      ⟨_, _, m.eval η hη, m.eval η hη, Mode.le_refl _⟩)⟩)
  map_sup' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rename_i a b
    change observer f (m.act (a.join b)) = (observer f (m.act a) || observer f (m.act b))
    have he : Order.of (m.act (a.join b)) = Order.of (m.act a) ⊔ Order.of (m.act b) :=
      Quotient.sound ⟨.equation (.modal true (a.compatible b) m.defined),
        .equationRev (.modal true (a.compatible b) m.defined)⟩
    exact (congrArg f he).trans (f.map_sup' _ _)
  map_inf' := by
    intro a b
    induction a using Antisymmetrization.induction_on
    induction b using Antisymmetrization.induction_on
    rename_i a b
    change observer f (m.act (a.meet b)) = (observer f (m.act a) && observer f (m.act b))
    have he : Order.of (m.act (a.meet b)) = Order.of (m.act a) ⊓ Order.of (m.act b) :=
      Quotient.sound ⟨.equation (.modal false (a.compatible b) m.defined),
        .equationRev (.modal false (a.compatible b) m.defined)⟩
    exact (congrArg f he).trans (f.map_inf' _ _)


theorem actObserver_value {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (m : GuardedMode Δ)
    {a : CompareTy} (ha : Representable Δ shape a) :
    booleanValue (actObserver f m) a = booleanValue f (.modal a m.expression) := by
  rw [booleanValue_represented _ _ ha]
  rw [booleanValue_represented _ _
    (show Representable Δ shape (.modal a m.expression) from
      ⟨ha.1, CompareTy.definedUnder_modal_iff.mpr ⟨ha.2.1, m.defined⟩, ha.2.2⟩)]
  rfl


theorem modal_idem {Δ : Bounds} {a : CompareTy} (ha : a.WellShaped Δ)
    (m : GuardedMode Δ) :
    Equiv Δ (.modal (.modal a m.expression) m.expression) (.modal a m.expression) := by
  have he : Submode Δ (.compose m.expression m.expression) m.expression :=
    .valid fun η hη => ⟨(m.value η).compose (m.value η), m.value η,
      by simp [ModExpr.eval, m.eval η hη],
      m.eval η hη, by simp only [Mode.compose_self]; exact Mode.le_refl _⟩
  have hr : Submode Δ m.expression (.compose m.expression m.expression) :=
    .valid fun η hη => ⟨m.value η, (m.value η).compose (m.value η), m.eval η hη,
      by simp [ModExpr.eval, m.eval η hη],
      by simp only [Mode.compose_self]; exact Mode.le_refl _⟩
  exact ⟨(AlgebraSubtype.shaped (.compose ha)).trans (.congr (.refl ha) he),
    (AlgebraSubtype.congr (.refl ha) hr).trans (.shaped (.composeRev ha))⟩

theorem pair_absorb {Δ : Bounds} {a b : CompareTy} (isSum : Bool)
    (ha : a.WellShaped Δ) (hb : b.WellShaped Δ) (m : GuardedMode Δ) :
    Equiv Δ (.modal ((if isSum then CompareTy.sum else CompareTy.prod) a b) m.expression)
      (.modal ((if isSum then CompareTy.sum else CompareTy.prod)
        (.modal a m.expression) (.modal b m.expression)) m.expression) := by
  have hma := modal_idem ha m
  have hmb := modal_idem hb m
  cases isSum
  · exact ⟨.prod hma.2 hmb.2, .prod hma.1 hmb.1⟩
  · exact ⟨.sum hma.2 hmb.2, .sum hma.1 hmb.1⟩


open ComparisonPropagation

theorem outer_rectangular (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (m : GuardedMode Δ)
    (left : Fin rows → CompareTy) (right : Fin cols → CompareTy)
    (hl : ∀i, Representable Δ s (left i)) (hr : ∀j, Representable Δ t (right j)) :
    Rectangular (fun i j => booleanValue f (.modal (k.op (left i) (right j)) m.expression)) := by
  have h := observer_rectangular k (actObserver f m) left right hl hr
  simpa only [actObserver_value f m (k.op_representable (hl _) (hr _))] using h

theorem outer_apply (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (m : GuardedMode Δ)
    {left right : List CompareTy} {ls rs : CNF} {a b : CompareTy}
    (hl : ∀x∈left, Representable Δ s x) (hr : ∀y∈right, Representable Δ t y)
    (ha : reify left ls = some a) (hb : reify right rs = some b) :
    (factor (fun (i : Fin left.length) (j : Fin right.length) =>
      booleanValue f (.modal (k.op left[i] right[j]) m.expression))).apply
      (k.leftSign false) ls rs = booleanValue f (.modal (k.op a b) m.expression) := by
  have h := observer_apply k (actObserver f m) hl hr ha hb
  have hc : (fun (i : Fin left.length) (j : Fin right.length) =>
      booleanValue (actObserver f m) (k.op left[i] right[j])) =
      (fun (i : Fin left.length) (j : Fin right.length) =>
        booleanValue f (.modal (k.op left[i] right[j]) m.expression)) := by
    funext i j
    exact actObserver_value f m (k.op_representable
      (hl _ (List.getElem_mem i.isLt)) (hr _ (List.getElem_mem j.isLt)))
  rw [hc] at h
  exact h.trans (actObserver_value f m (k.op_representable
    (reify_property ha (Representable Δ s) hl (fun _ _ => representable_typeOp true)
      (fun _ _ => representable_typeOp false))
    (reify_property hb (Representable Δ t) hr (fun _ _ => representable_typeOp true)
      (fun _ _ => representable_typeOp false))))


private theorem all_eval_value (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.all es).eval σ = es.all (fun e => e.eval σ) := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

private theorem any_eval_value (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.any es).eval σ = es.any (fun e => e.eval σ) := by
  induction es <;> simp_all [BoolExpr.any, BoolExpr.eval]

theorem literalFormula_eval (value : Nat → BoolExpr) (literal : Literal) (σ : Nat → Bool) :
    (literalFormula value literal).eval σ = ((value literal.1).eval σ == literal.2) := by
  cases literal with
  | mk i p => cases p <;> simp [literalFormula, BoolExpr.eval]

theorem clauseFormula_eval (dual : Bool) (value : Nat → BoolExpr) (clause : Clause)
    (σ : Nat → Bool) :
    (clauseFormula dual value clause).eval σ =
      clauseValue dual (fun i => (value i).eval σ) clause := by
  cases dual <;> simp [clauseFormula, clauseValue, all_eval_value, any_eval_value,
    List.all_map, List.any_map, Function.comp_def, literalFormula_eval]

theorem cnfFormula_eval (dual : Bool) (value : Nat → BoolExpr) (clauses : CNF)
    (σ : Nat → Bool) :
    (cnfFormula dual value clauses).eval σ =
      cnfValue dual (fun i => (value i).eval σ) clauses := by
  cases dual <;> simp [cnfFormula, cnfValue, all_eval_value, any_eval_value,
    List.all_map, List.any_map, Function.comp_def, clauseFormula_eval]


theorem matrixFormula_correct (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    {left right : List CompareTy} {ls rs : CNF} {a b : CompareTy}
    (hl : ∀x∈left, Representable Δ s x) (hr : ∀y∈right, Representable Δ t y)
    (ha : reify left ls = some a) (hb : reify right rs = some b)
    (atom : Fin left.length → Fin right.length → Nat) (σ : Nat → Bool)
    (hc : ∀i j, σ (atom i j) = booleanValue f (k.op left[i] right[j])) :
    (matrixFormula atom (k.leftSign false) ls rs).eval σ = booleanValue f (k.op a b) := by
  rw [matrixFormula, cnfFormula_eval]
  have hv : (fun i => (if hi : i < left.length then
      cnfFormula false (fun j => if hj : j < right.length then
        BoolExpr.atom (atom ⟨i,hi⟩ ⟨j,hj⟩) else .const false) rs
      else .const false).eval σ) =
      basisValue left (fun x => booleanValue f (k.op x b)) := by
    funext i
    by_cases hi : i < left.length
    · simp only [hi, dif_pos, cnfFormula_eval]
      have hv : (fun j => (if hj : j < right.length then
          BoolExpr.atom (atom ⟨i,hi⟩ ⟨j,hj⟩) else .const false).eval σ) =
          basisValue right (fun y => booleanValue f (k.op left[i] y)) := by
        funext j
        by_cases hj : j < right.length
        · simpa [hj, BoolExpr.eval, basisValue, List.getElem?_eq_getElem hj] using hc ⟨i,hi⟩ ⟨j,hj⟩
        · simp [hj, BoolExpr.eval, basisValue]
      rw [hv]
      simpa [basisValue, List.getElem?_eq_getElem hi] using
        (reify_right k f hb hr (hl _ (List.getElem_mem hi))).symm
    · simp [hi, BoolExpr.eval, basisValue]
  rw [hv]
  exact (reify_left k f ha hl (reify_property hb (Representable Δ t) hr
    (fun _ _ => representable_typeOp true) (fun _ _ => representable_typeOp false))).symm


theorem lattice_interval {Δ : Bounds} {shape : ComparisonShape}
    {lower upper : Carrier Δ shape} {basis : List CompareTy} {a : CompareTy}
    (ha : ComparisonControls.LatticeForm basis a)
    (hb : ∀x∈basis, InInterval lower upper x) : InInterval lower upper a := by
  induction ha with
  | atom h => exact hb _ h
  | join _ _ iha ihb => exact iha.join ihb
  | meet _ _ iha ihb => exact iha.meet ihb

theorem pair_interval (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    {lower upper : Carrier Δ (k.shape s t)}
    {left right : List CompareTy} {ls rs : CNF} {a b : CompareTy}
    (hl : ∀x∈left, Representable Δ s x) (hr : ∀y∈right, Representable Δ t y)
    (hc : ∀x∈left, ∀y∈right, InInterval lower upper (k.op x y))
    (ha : reify left ls = some a) (hb : reify right rs = some b) :
    InInterval lower upper (k.op a b) := by
  have hla : ComparisonControls.LatticeForm left a := reify_property ha
    (ComparisonControls.LatticeForm left) (fun _ => .atom)
    (fun _ _ => .join) (fun _ _ => .meet)
  have hlb : ComparisonControls.LatticeForm right b := reify_property hb
    (ComparisonControls.LatticeForm right) (fun _ => .atom)
    (fun _ _ => .join) (fun _ _ => .meet)
  obtain ⟨x,hx,hxr,hxe⟩ := k.lattice hla hlb hl hr
  obtain ⟨_,hlo,hhi⟩ := lattice_interval hx (by
    intro z hz
    obtain ⟨a,ha,hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    exact hc a ha b hb)
  exact ⟨k.op_representable (hla.representable hl) (hlb.representable hr),
    hlo.trans hxe.2, hxe.1.trans hhi⟩


theorem family_realizable (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    (lower upper : Carrier Δ (k.shape s t)) (hlu : lower ≤ upper)
    (hlo : observer f (lower.atMode Mode.bottom) = false)
    (hhi : observer f (upper.atMode Mode.top) = true)
    {left right : List CompareTy}
    (hl : ∀x∈left, Representable Δ s x) (hr : ∀y∈right, Representable Δ t y)
    (hc : ∀x∈left, ∀y∈right,
      InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) (k.op x y))
    (labels : List ModExpr) (hd : ∀m∈labels, DefinedMode Δ m) :
    ∃ coordinate η, (coordinate = ComparisonControls.Coordinate.unaffected ∨ ModeModels Δ η) ∧
      ∀ (σ : Nat → Bool) (modeAtom : Nat → Nat),
        (∀i, σ (modeAtom i) = encodeModes η i) →
        ∀ (ls rs : CNF) (a b : CompareTy),
          reify left ls = some a → reify right rs = some b →
          ∀ atom : Fin left.length → Fin right.length → Nat,
            (∀i j, σ (atom i j) = booleanValue f (k.op left[i] right[j])) →
            ∀m∈labels, booleanValue f (.modal (k.op a b) m) =
              (coordinate.modalWith modeAtom (matrixFormula atom (k.leftSign false) ls rs) m).eval σ := by
  obtain ⟨coordinate,η,hη,hmodal⟩ := observer_substituted_realizable
    f lower upper hlu hlo hhi ModExpr.var (fun η => η) (fun _ _ => rfl)
    labels (by simpa only [ModExpr.subst_id] using hd)
  refine ⟨coordinate,η,hη,?_⟩
  intro σ modeAtom hs ls rs a b ha hb atom hatom m hm
  obtain ⟨hp,hlo',hhi'⟩ := pair_interval k hl hr hc ha hb
  simp only [CompareTy.subst_id] at hmodal
  have he := hmodal σ modeAtom hs (k.op a b) hp hlo' hhi' m hm
  exact he.trans (coordinate.modalWith_congr_value modeAtom m
    (matrixFormula_correct k f hl hr ha hb atom σ hatom).symm)


private theorem all_eval (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.all es).eval σ = true ↔ ∀e∈es, e.eval σ = true := by
  rw [all_eval_value, List.all_eq_true]

private theorem equal_eval (a b : BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.equal a b).eval σ = true ↔ a.eval σ = b.eval σ := by
  cases ha : a.eval σ <;> cases hb : b.eval σ <;> simp [BoolExpr.equal, BoolExpr.eval, ha, hb]

theorem familyTheory_correct (coordinate : ComparisonControls.Coordinate) (modeAtom : Nat → Nat)
    (base : Fin rows → Fin cols → Nat) (labels : Vector ModExpr count)
    (acted : Fin count → Fin rows → Fin cols → Nat) (σ : Nat → Bool) :
    (familyTheory coordinate modeAtom base labels acted).eval σ = true ↔
      Rectangular (fun i j => σ (base i j)) ∧ ∀k i j,
        σ (acted k i j) = (coordinate.modalWith modeAtom (.atom (base i j)) labels[k]).eval σ := by
  simp only [familyTheory, BoolExpr.eval, Bool.and_eq_true, theory_correct, all_eval,
    List.forall_mem_flatMap, List.forall_mem_map, List.mem_finRange, forall_true_left, equal_eval]

theorem Absorption.formula_correct (a : Absorption rows cols)
    (coordinate : ComparisonControls.Coordinate) (modeAtom : Nat → Nat)
    (base : Fin rows → Fin cols → Nat) (σ : Nat → Bool) :
    (a.formula coordinate modeAtom base).eval σ = true ↔ ∀i j,
      (coordinate.modalWith modeAtom (.atom (base i j)) a.mode).eval σ =
        (coordinate.modalWith modeAtom (matrixFormula base false a.left[i] a.right[j]) a.mode).eval σ := by
  simp only [Absorption.formula, all_eval, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_finRange, forall_true_left, equal_eval]

theorem compileFamily_correct {fuel : Nat} {coordinate : ComparisonControls.Coordinate}
    {modeAtom : Nat → Nat} {base : Fin rows → Fin cols → Nat}
    {labels : Vector ModExpr count} {acted : Fin count → Fin rows → Fin cols → Nat}
    {clauses : CNF} (h : compileFamily fuel coordinate modeAtom base labels acted = .success clauses)
    (σ : Nat → Bool) :
    CNFHolds σ clauses ↔ Rectangular (fun i j => σ (base i j)) ∧ ∀k i j,
      σ (acted k i j) = (coordinate.modalWith modeAtom (.atom (base i j)) labels[k]).eval σ :=
  (CompactCNF.toCNF_correct h σ).trans (familyTheory_correct coordinate modeAtom base labels acted σ)

theorem compileFamily_complete (coordinate : ComparisonControls.Coordinate) (modeAtom : Nat → Nat)
    (base : Fin rows → Fin cols → Nat) (labels : Vector ModExpr count)
    (acted : Fin count → Fin rows → Fin cols → Nat) :
    ∃ threshold clauses, ∀ fuel ≥ threshold,
      compileFamily fuel coordinate modeAtom base labels acted = .success clauses :=
  CompactCNF.toCNF_complete (familyTheory coordinate modeAtom base labels acted) true

theorem compileAbsorption_correct {fuel : Nat} {a : Absorption rows cols}
    {coordinate : ComparisonControls.Coordinate} {modeAtom : Nat → Nat}
    {base : Fin rows → Fin cols → Nat} {clauses : CNF}
    (h : compileAbsorption fuel a coordinate modeAtom base = .success clauses) (σ : Nat → Bool) :
    CNFHolds σ clauses ↔ ∀i j,
      (coordinate.modalWith modeAtom (.atom (base i j)) a.mode).eval σ =
        (coordinate.modalWith modeAtom (matrixFormula base false a.left[i] a.right[j]) a.mode).eval σ :=
  (CompactCNF.toCNF_correct h σ).trans (a.formula_correct coordinate modeAtom base σ)

theorem compileAbsorption_complete (a : Absorption rows cols)
    (coordinate : ComparisonControls.Coordinate) (modeAtom : Nat → Nat)
    (base : Fin rows → Fin cols → Nat) :
    ∃ threshold clauses, ∀ fuel ≥ threshold,
      compileAbsorption fuel a coordinate modeAtom base = .success clauses :=
  CompactCNF.toCNF_complete (a.formula coordinate modeAtom base) true


theorem reify_singleton (basis : List CompareTy) (i : Fin basis.length) :
    reify basis [[(i.val,true)]] = some basis[i] := by
  simp [reify, clauseType]

theorem matrixFormula_singleton (atom : Fin rows → Fin cols → Nat) (dual : Bool)
    (i : Fin rows) (j : Fin cols) (σ : Nat → Bool) :
    (matrixFormula atom dual [[(i.val,true)]] [[(j.val,true)]]).eval σ = σ (atom i j) := by
  cases dual <;> simp [matrixFormula, cnfFormula, clauseFormula, literalFormula,
    i.isLt, j.isLt, BoolExpr.all, BoolExpr.any, BoolExpr.eval]

def Absorption.Certified (Δ : Bounds) (left right : List CompareTy)
    (a : Absorption left.length right.length) : Prop :=
  DefinedMode Δ a.mode ∧
    (∀i : Fin left.length, ∃x, reify left a.left[i] = some x ∧
      Equiv Δ x (.modal left[i] a.mode)) ∧
    (∀j : Fin right.length, ∃y, reify right a.right[j] = some y ∧
      Equiv Δ y (.modal right[j] a.mode))

theorem pair_absorb_reify {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    {a b x y : CompareTy} (ha : Representable Δ s a) (hb : Representable Δ t b)
    (hx : Representable Δ s x) (hy : Representable Δ t y) (m : GuardedMode Δ)
    (he : Equiv Δ x (.modal a m.expression)) (hf : Equiv Δ y (.modal b m.expression))
    (f : LatticeHom (Order Δ ((if isSum then Kind.sum else Kind.prod).shape s t)) Bool) :
    booleanValue f (.modal ((if isSum then Kind.sum else Kind.prod).op a b) m.expression) =
      booleanValue f (.modal ((if isSum then Kind.sum else Kind.prod).op x y) m.expression) := by
  let k := if isSum then Kind.sum else Kind.prod
  have hl := k.op_representable ha hb
  have hr := k.op_representable hx hy
  have hmode : Submode Δ m.expression m.expression :=
    .valid fun η hη => ⟨_, _, m.eval η hη, m.eval η hη, Mode.le_refl _⟩
  apply equiv_value f
    (show Representable Δ (k.shape s t) (.modal (k.op a b) m.expression) from
      ⟨hl.1, CompareTy.definedUnder_modal_iff.mpr ⟨hl.2.1,m.defined⟩, hl.2.2⟩)
    (show Representable Δ (k.shape s t) (.modal (k.op x y) m.expression) from
      ⟨hr.1, CompareTy.definedUnder_modal_iff.mpr ⟨hr.2.1,m.defined⟩, hr.2.2⟩)
  have h := k.congr he.symm hf.symm
  have hh : Equiv Δ (.modal (k.op a b) m.expression)
      (.modal (k.op (.modal a m.expression) (.modal b m.expression)) m.expression) := by
    cases isSum
    · exact pair_absorb false ha.1 hb.1 m
    · exact pair_absorb true ha.1 hb.1 m
  exact hh.trans ⟨.congr h.1 hmode, .congr h.2 hmode⟩


theorem Absorption.sound {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    (f : LatticeHom (Order Δ ((if isSum then Kind.sum else Kind.prod).shape s t)) Bool)
    {left right : List CompareTy}
    (hl : ∀x∈left, Representable Δ s x) (hr : ∀y∈right, Representable Δ t y)
    (a : Absorption left.length right.length) (ha : a.Certified Δ left right)
    (coordinate : ComparisonControls.Coordinate) (modeAtom : Nat → Nat)
    (atom : Fin left.length → Fin right.length → Nat) (σ : Nat → Bool)
    (hobserve : ∀(ls rs : CNF) (x y : CompareTy),
      reify left ls = some x → reify right rs = some y →
      booleanValue f (.modal ((if isSum then Kind.sum else Kind.prod).op x y) a.mode) =
        (coordinate.modalWith modeAtom (matrixFormula atom false ls rs) a.mode).eval σ) :
    (a.formula coordinate modeAtom atom).eval σ = true := by
  apply (a.formula_correct coordinate modeAtom atom σ).mpr
  intro i j
  obtain ⟨x,hx,hxe⟩ := ha.2.1 i
  obtain ⟨y,hy,hye⟩ := ha.2.2 j
  have he := pair_absorb_reify isSum
    (hl _ (List.getElem_mem i.isLt)) (hr _ (List.getElem_mem j.isLt))
    (reify_property hx (Representable Δ s) hl (fun _ _ => representable_typeOp true)
      (fun _ _ => representable_typeOp false))
    (reify_property hy (Representable Δ t) hr (fun _ _ => representable_typeOp true)
      (fun _ _ => representable_typeOp false))
    (GuardedMode.ofDefined a.mode ha.1) hxe hye f
  have hbase := hobserve [[(i.val,true)]] [[(j.val,true)]] left[i] right[j]
    (reify_singleton left i) (reify_singleton right j)
  have hsingle := coordinate.modalWith_congr_value modeAtom a.mode
    (right := .atom (atom i j)) (σ := σ) (matrixFormula_singleton atom false i j σ)
  exact hsingle.symm.trans (hbase.symm.trans (he.trans (hobserve _ _ _ _ hx hy)))


theorem family_sound (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    (lower upper : Carrier Δ (k.shape s t)) (hlu : lower ≤ upper)
    (hlo : observer f (lower.atMode Mode.bottom) = false)
    (hhi : observer f (upper.atMode Mode.top) = true)
    {left right : List CompareTy}
    (hl : ∀x∈left, Representable Δ s x) (hr : ∀y∈right, Representable Δ t y)
    (hc : ∀x∈left, ∀y∈right,
      InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) (k.op x y))
    (labels : Vector ModExpr count) (hd : ∀m∈labels.toList, DefinedMode Δ m) :
    ∃ coordinate η, (coordinate = ComparisonControls.Coordinate.unaffected ∨ ModeModels Δ η) ∧
      ∀(σ : Nat → Bool) (modeAtom : Nat → Nat)
        (base : Fin left.length → Fin right.length → Nat)
        (acted : Fin count → Fin left.length → Fin right.length → Nat),
        (∀i, σ (modeAtom i) = encodeModes η i) →
        (∀i j, σ (base i j) = booleanValue f (k.op left[i] right[j])) →
        (∀l i j, σ (acted l i j) = booleanValue f (.modal (k.op left[i] right[j]) labels[l])) →
        (familyTheory coordinate modeAtom base labels acted).eval σ = true := by
  obtain ⟨coordinate,η,hη,he⟩ := family_realizable k f lower upper hlu hlo hhi hl hr hc labels.toList hd
  refine ⟨coordinate,η,hη,?_⟩
  intro σ modeAtom base acted hs hb ha
  apply (familyTheory_correct coordinate modeAtom base labels acted σ).mpr
  constructor
  · simpa only [hb] using observer_rectangular k f (fun i => left[i]) (fun j => right[j])
      (fun i => hl _ (List.getElem_mem i.isLt)) (fun j => hr _ (List.getElem_mem j.isLt))
  · intro l i j
    have h := he σ modeAtom hs [[(i.val,true)]] [[(j.val,true)]] left[i] right[j]
      (reify_singleton left i) (reify_singleton right j) base hb labels[l]
      (Vector.mem_toList_iff.mpr (Vector.getElem_mem l.isLt))
    exact (ha l i j).trans (h.trans (coordinate.modalWith_congr_value modeAtom labels[l]
      (right := .atom (base i j)) (σ := σ) (matrixFormula_singleton base (k.leftSign false) i j σ)))

theorem pair_family_sound {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    (f : LatticeHom (Order Δ ((if isSum then Kind.sum else Kind.prod).shape s t)) Bool)
    (lower upper : Carrier Δ ((if isSum then Kind.sum else Kind.prod).shape s t))
    (hlu : lower ≤ upper)
    (hlo : observer f (lower.atMode Mode.bottom) = false)
    (hhi : observer f (upper.atMode Mode.top) = true)
    {left right : List CompareTy}
    (hl : ∀x∈left, Representable Δ s x) (hr : ∀y∈right, Representable Δ t y)
    (hc : ∀x∈left, ∀y∈right, InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top)
      ((if isSum then Kind.sum else Kind.prod).op x y))
    (labels : Vector ModExpr count) (hd : ∀m∈labels.toList, DefinedMode Δ m)
    (actions : List (Absorption left.length right.length))
    (hcert : ∀a∈actions, a.Certified Δ left right ∧ a.mode∈labels.toList) :
    ∃ coordinate η, (coordinate = ComparisonControls.Coordinate.unaffected ∨ ModeModels Δ η) ∧
      ∀(σ : Nat → Bool) (modeAtom : Nat → Nat)
        (base : Fin left.length → Fin right.length → Nat)
        (acted : Fin count → Fin left.length → Fin right.length → Nat),
        (∀i, σ (modeAtom i) = encodeModes η i) →
        (∀i j, σ (base i j) = booleanValue f ((if isSum then Kind.sum else Kind.prod).op left[i] right[j])) →
        (∀l i j, σ (acted l i j) = booleanValue f
          (.modal ((if isSum then Kind.sum else Kind.prod).op left[i] right[j]) labels[l])) →
        (familyTheory coordinate modeAtom base labels acted).eval σ = true ∧
          ∀a∈actions, (a.formula coordinate modeAtom base).eval σ = true := by
  let k := if isSum then Kind.sum else Kind.prod
  obtain ⟨coordinate,η,hη,he⟩ := family_realizable k f lower upper hlu hlo hhi hl hr hc labels.toList hd
  refine ⟨coordinate,η,hη,?_⟩
  intro σ modeAtom base acted hs hb ha
  constructor
  · apply (familyTheory_correct coordinate modeAtom base labels acted σ).mpr
    constructor
    · simpa only [hb] using observer_rectangular k f (fun i => left[i]) (fun j => right[j])
        (fun i => hl _ (List.getElem_mem i.isLt)) (fun j => hr _ (List.getElem_mem j.isLt))
    · intro l i j
      have h := he σ modeAtom hs [[(i.val,true)]] [[(j.val,true)]] left[i] right[j]
        (reify_singleton left i) (reify_singleton right j) base hb labels[l]
        (Vector.mem_toList_iff.mpr (Vector.getElem_mem l.isLt))
      exact (ha l i j).trans (h.trans (coordinate.modalWith_congr_value modeAtom labels[l]
        (right := .atom (base i j)) (σ := σ) (matrixFormula_singleton base (k.leftSign false) i j σ)))
  · intro a ha
    apply a.sound isSum f hl hr (hcert a ha).1 coordinate modeAtom base σ
    intro ls rs x y hx hy
    have h := he σ modeAtom hs ls rs x y hx hy base hb a.mode (hcert a ha).2
    cases isSum <;> exact h

end ModalityInference.ComparisonStructuralFamily
