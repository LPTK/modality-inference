import ModalityInference.ComparisonStructuralMatrix
import ModalityInference.Proofs.ComparisonStructuralLattice

/-! The finite constructor matrix compiler is exact. Actual guarded algebra
observers satisfy its equations, and its selected coordinate evaluates both
reconstructed child CNFs exactly, including contravariant function domains. -/
namespace ModalityInference.ComparisonStructuralMatrix

private theorem rectangle_change {a b c d : Bool}
    (h : ((a || d) = (b || c)) ∧ ((a && d) = (b && c))) (hne : a ≠ b) :
    c = a ∧ d = b := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem varying_row {table : Table rows cols} (h : Rectangular table)
    {i : Fin rows} {j k : Fin cols} (hne : table i j ≠ table i k) :
    ∀ i' l, table i' l = table i l := by
  intro i' l
  by_cases he : table i j = table i l
  · exact (rectangle_change (h i i' k l) (fun hx => hne (he.trans hx.symm))).2
  · exact (rectangle_change (h i i' j l) he).2

theorem factor_correct {table : Table rows cols} (h : Rectangular table) :
    ∀ i j, (factor table).eval i j = table i j := by
  intro i j
  unfold factor
  split
  · split
    · rename_i row hrow
      have hp := List.find?_some hrow
      simp at hp
      obtain ⟨col, hcol⟩ := hp
      simpa [Projection.eval] using (varying_row h hcol i j).symm
    · rename_i hnone
      have hp := List.find?_eq_none.mp hnone i (by simp)
      simp at hp
      simpa [Projection.eval] using (hp j).symm
  · have := j.isLt
    omega

private theorem all_eval (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.all es).eval σ = true ↔ ∀e∈es, e.eval σ = true := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

private theorem equal_eval (a b : BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.equal a b).eval σ = true ↔ a.eval σ = b.eval σ := by
  cases ha : a.eval σ <;> cases hb : b.eval σ <;> simp [BoolExpr.equal, BoolExpr.eval, ha, hb]

theorem theory_correct (atom : Fin rows → Fin cols → Nat) (σ : Nat → Bool) :
    (theory atom).eval σ = true ↔ Rectangular (fun i j => σ (atom i j)) := by
  simp only [theory, all_eval, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_finRange, forall_true_left, BoolExpr.eval, Bool.and_eq_true, equal_eval, Rectangular]

theorem compile_correct {fuel : Nat} {atom : Fin rows → Fin cols → Nat} {clauses : CNF}
    (h : compile fuel atom = .success clauses) (σ : Nat → Bool) :
    CNFHolds σ clauses ↔ Rectangular (fun i j => σ (atom i j)) :=
  (CompactCNF.toCNF_correct h σ).trans (theory_correct atom σ)

theorem compile_complete (atom : Fin rows → Fin cols → Nat) :
    ∃ threshold clauses, ∀ fuel ≥ threshold, compile fuel atom = .success clauses :=
  CompactCNF.toCNF_complete (theory atom) true

open ComparisonAlgebra ComparisonStructuralLattice

theorem typeOp_comm {Δ : Bounds} {a b : CompareTy} (p : Bool)
    (h : Compatible Δ a b) : Equiv Δ (typeOp p a b) (typeOp p b a) := by
  have hr : (.join b a : CompareTy).WellShaped Δ :=
    ⟨h.1.2.1, h.1.1, h.1.2.2.symm⟩
  cases p
  · exact ⟨.meetGreatest (.shaped (.meetRight h.1)) (.shaped (.meetLeft h.1)),
      .meetGreatest (.shaped (.meetRight hr)) (.shaped (.meetLeft hr))⟩
  · exact ⟨.joinLeast (.shaped (.joinRight hr)) (.shaped (.joinLeft hr)),
      .joinLeast (.shaped (.joinRight h.1)) (.shaped (.joinLeft h.1))⟩

theorem Kind.rectangle (k : Kind) {Δ : Bounds} {a b c d : CompareTy} (p : Bool)
    (ha : Compatible Δ a c) (hb : Compatible Δ b d) :
    Equiv Δ (typeOp p (k.op a b) (k.op c d))
      (typeOp p (k.op a d) (k.op c b)) := by
  refine (k.distrib p ha hb).symm.trans ?_
  refine (k.congr (.refl ((typeOp_wellShaped _ _ _ _).mpr ha.1))
    (typeOp_comm p hb)).trans ?_
  exact k.distrib p ha ⟨⟨hb.1.2.1, hb.1.1, hb.1.2.2.symm⟩, hb.2.2, hb.2.1⟩

theorem equiv_value {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) {a b : CompareTy}
    (ha : Representable Δ shape a) (hb : Representable Δ shape b)
    (h : Equiv Δ a b) : booleanValue f a = booleanValue f b := by
  exact Bool.eq_iff_iff.mpr
    ⟨ComparisonTupleReflection.booleanValue_mono f ha hb h.1,
      ComparisonTupleReflection.booleanValue_mono f hb ha h.2⟩

theorem observer_rectangular (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    (left : Fin rows → CompareTy) (right : Fin cols → CompareTy)
    (hl : ∀i, Representable Δ s (left i)) (hr : ∀j, Representable Δ t (right j)) :
    Rectangular (fun i j => booleanValue f (k.op (left i) (right j))) := by
  intro i i' j j'
  have hvalue (p : Bool) := equiv_value f
    (representable_typeOp p (k.op_representable (hl i) (hr j))
      (k.op_representable (hl i') (hr j')))
    (representable_typeOp p (k.op_representable (hl i) (hr j'))
      (k.op_representable (hl i') (hr j)))
    (Kind.rectangle k p ((represented (hl i)).compatible (represented (hl i')))
      ((represented (hr j)).compatible (represented (hr j'))))
  exact ⟨hvalue true, hvalue false⟩

open ComparisonPropagation

theorem cnfValue_correct (values : Nat → Bool) (clauses : CNF) :
    cnfValue false values clauses = true ↔ CNFHolds values clauses := by
  simp only [cnfValue, Bool.false_eq_true, if_false, List.all_eq_true,
    clauseValue, List.any_eq_true, beq_iff_eq, CNFHolds, ClauseHolds, Prod.exists]

theorem clauseType_value {basis : List CompareTy} {clause : Clause} {t : CompareTy}
    (h : clauseType basis clause = some t) (dual : Bool)
    (P : CompareTy → Prop) (value : CompareTy → Bool)
    (hb : ∀a∈basis, P a) (hp : ∀a b, P a → P b → P (.join a b))
    (hj : ∀a b, P a → P b →
      value (.join a b) = if dual then value a && value b else value a || value b) :
    value t = clauseValue dual (basisValue basis value) clause := by
  induction clause generalizing t with
  | nil => simp [clauseType] at h
  | cons literal rest ih =>
    rcases literal with ⟨v, positive⟩
    cases positive with
    | false => simp [clauseType] at h
    | true =>
      cases he : basis[v]? with
      | none => simp [clauseType, he] at h
      | some a =>
        cases rest with
        | nil =>
          have hh : a = t := by simpa [clauseType, he] using h
          subst t
          cases dual <;> simp [clauseValue, basisValue, he]
        | cons l rest =>
          cases ht : clauseType basis (l :: rest) with
          | none => rw [clauseType] at h; simp [he, ht] at h
          | some b =>
            have hh : .join a b = t := by rw [clauseType] at h; simpa [he, ht] using h
            cases hh
            rw [hj a b (hb a (List.mem_of_getElem? he)) (clauseType_property ht P hb hp), ih ht]
            cases dual <;> simp [clauseValue, basisValue, he]

theorem reify_value {basis : List CompareTy} {clauses : CNF} {t : CompareTy}
    (h : reify basis clauses = some t) (dual : Bool)
    (P : CompareTy → Prop) (value : CompareTy → Bool)
    (hb : ∀a∈basis, P a)
    (hpj : ∀a b, P a → P b → P (.join a b))
    (hpm : ∀a b, P a → P b → P (.meet a b))
    (hj : ∀a b, P a → P b →
      value (.join a b) = if dual then value a && value b else value a || value b)
    (hm : ∀a b, P a → P b →
      value (.meet a b) = if dual then value a || value b else value a && value b) :
    value t = cnfValue dual (basisValue basis value) clauses := by
  induction clauses generalizing t with
  | nil => simp [reify] at h
  | cons c cs ih =>
    cases hc : clauseType basis c with
    | none => simp [reify, hc] at h
    | some a =>
      cases cs with
      | nil =>
        have he : a = t := by simpa [reify, hc] using h
        subst t
        simpa [cnfValue] using clauseType_value hc dual P value hb hpj hj
      | cons c' cs =>
        cases hr : reify basis (c' :: cs) with
        | none => rw [reify] at h; simp [hc, hr] at h
        | some b =>
          have he : .meet a b = t := by rw [reify] at h; simpa [hc, hr] using h
          cases he
          rw [hm a b (clauseType_property hc P hb hpj) (reify_property hr P hb hpj hpm),
            clauseType_value hc dual P value hb hpj hj, ih hr]
          cases dual <;> simp [cnfValue]

theorem observer_left_typeOp (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (p : Bool)
    {a c b : CompareTy} (ha : Representable Δ s a) (hc : Representable Δ s c)
    (hb : Representable Δ t b) :
    booleanValue f (k.op (typeOp p a c) b) =
      booleanValue f (typeOp (k.leftSign p) (k.op a b) (k.op c b)) :=
  equiv_value f (k.op_representable (representable_typeOp p ha hc) hb)
    (representable_typeOp _ (k.op_representable ha hb) (k.op_representable hc hb))
    (k.left_distrib p ((represented ha).compatible (represented hc)) hb.1 hb.2.1)

theorem observer_right_typeOp (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (p : Bool)
    {a b d : CompareTy} (ha : Representable Δ s a) (hb : Representable Δ t b)
    (hd : Representable Δ t d) :
    booleanValue f (k.op a (typeOp p b d)) =
      booleanValue f (typeOp p (k.op a b) (k.op a d)) :=
  equiv_value f (k.op_representable ha (representable_typeOp p hb hd))
    (representable_typeOp _ (k.op_representable ha hb) (k.op_representable ha hd))
    (k.right_distrib p ha.1 ha.2.1 ((represented hb).compatible (represented hd)))

theorem reify_left (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    {basis : List CompareTy} {clauses : CNF} {a b : CompareTy}
    (h : reify basis clauses = some a) (hs : ∀x∈basis, Representable Δ s x)
    (hb : Representable Δ t b) :
    booleanValue f (k.op a b) = cnfValue (k.leftSign false)
      (basisValue basis (fun x => booleanValue f (k.op x b))) clauses := by
  refine reify_value h (k.leftSign false) (Representable Δ s)
    (fun x => booleanValue f (k.op x b)) hs
    (fun _ _ => representable_typeOp true) (fun _ _ => representable_typeOp false) ?_ ?_
  · intro x y hx hy
    have he := observer_left_typeOp k f true hx hy hb
    cases k <;> exact he
  · intro x y hx hy
    have he := observer_left_typeOp k f false hx hy hb
    cases k <;> exact he

theorem reify_right (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    {basis : List CompareTy} {clauses : CNF} {a b : CompareTy}
    (h : reify basis clauses = some b) (hs : ∀x∈basis, Representable Δ t x)
    (ha : Representable Δ s a) :
    booleanValue f (k.op a b) = cnfValue false
      (basisValue basis (fun x => booleanValue f (k.op a x))) clauses := by
  exact reify_value h false (Representable Δ t)
    (fun x => booleanValue f (k.op a x)) hs
    (fun _ _ => representable_typeOp true) (fun _ _ => representable_typeOp false)
    (fun _ _ => observer_right_typeOp k f true ha)
    (fun _ _ => observer_right_typeOp k f false ha)

theorem cnfValue_constant {basis : List CompareTy} {clauses : CNF} {a : CompareTy}
    (h : reify basis clauses = some a) (dual value : Bool) :
    cnfValue dual (basisValue basis (fun _ => value)) clauses = value := by
  exact (reify_value h dual (fun _ => True) (fun _ => value) (by simp) (by simp) (by simp)
    (by cases dual <;> simp) (by cases dual <;> simp)).symm

theorem basisValue_congr {basis : List CompareTy} {left right : CompareTy → Bool}
    (h : ∀a∈basis, left a = right a) : basisValue basis left = basisValue basis right := by
  funext i
  cases hi : basis[i]? with
  | none => simp [basisValue, hi]
  | some a => simp [basisValue, hi, h a (List.mem_of_getElem? hi)]

theorem basisValue_vector {basis : List CompareTy} {value : CompareTy → Bool}
    {values : Vector Bool basis.length} (h : ∀i : Fin basis.length, value basis[i] = values[i]) :
    basisValue basis value = vectorValue values := by
  funext i
  by_cases hi : i < basis.length
  · simpa [basisValue, vectorValue, List.getElem?_eq_getElem hi,
      Vector.getElem?_eq_getElem hi] using h ⟨i, hi⟩
  · simp [basisValue, vectorValue, List.getElem?_eq_none (Nat.le_of_not_gt hi),
      Vector.getElem?_eq_none (Nat.le_of_not_gt hi)]

theorem observer_apply (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    {left right : List CompareTy} {ls rs : CNF} {a b : CompareTy}
    (hl : ∀x∈left, Representable Δ s x) (hr : ∀y∈right, Representable Δ t y)
    (ha : reify left ls = some a) (hb : reify right rs = some b) :
    (factor (fun (i : Fin left.length) (j : Fin right.length) =>
      booleanValue f (k.op left[i] right[j]))).apply (k.leftSign false) ls rs =
        booleanValue f (k.op a b) := by
  let table : Table left.length right.length := fun i j => booleanValue f (k.op left[i] right[j])
  have htable := factor_correct (observer_rectangular k f (fun i => left[i]) (fun j => right[j])
    (fun i => hl _ (List.getElem_mem i.isLt)) (fun j => hr _ (List.getElem_mem j.isLt)))
  change ∀i j, (factor table).eval i j = table i j at htable
  change (factor table).apply (k.leftSign false) ls rs = _
  cases he : factor table with
  | left values =>
    simp only [he, Projection.eval] at htable
    have hleft (i : Fin left.length) : booleanValue f (k.op left[i] b) = values[i] := by
      refine (reify_right k f hb hr (hl _ (List.getElem_mem i.isLt))).trans ?_
      have hfix : basisValue right (fun x => booleanValue f (k.op left[i] x)) =
          basisValue right (fun _ => values[i]) := by
        apply basisValue_congr
        intro y hy
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
        exact (htable i ⟨j, hj⟩).symm
      exact (congrArg (fun values => cnfValue false values rs) hfix).trans
        (cnfValue_constant hb false _)
    exact (congrArg (fun values => cnfValue (k.leftSign false) values ls)
      (basisValue_vector hleft)).symm.trans
        (reify_left k f ha hl (reify_property hb (Representable Δ t) hr
          (fun _ _ => representable_typeOp true) (fun _ _ => representable_typeOp false))).symm
  | right values =>
    simp only [he, Projection.eval] at htable
    have hright (j : Fin right.length) : booleanValue f (k.op a right[j]) = values[j] := by
      refine (reify_left k f ha hl (hr _ (List.getElem_mem j.isLt))).trans ?_
      have hfix : basisValue left (fun x => booleanValue f (k.op x right[j])) =
          basisValue left (fun _ => values[j]) := by
        apply basisValue_congr
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
        exact (htable ⟨i, hi⟩ j).symm
      exact (congrArg (fun values => cnfValue (k.leftSign false) values ls) hfix).trans
        (cnfValue_constant ha (k.leftSign false) _)
    exact (congrArg (fun values => cnfValue false values rs)
      (basisValue_vector hright)).symm.trans
        (reify_right k f hb hr (reify_property ha (Representable Δ s) hl
          (fun _ _ => representable_typeOp true) (fun _ _ => representable_typeOp false))).symm

end ModalityInference.ComparisonStructuralMatrix
