import ModalityInference.Proofs.ComparisonModalSeparation
import ModalityInference.Proofs.ComparisonAlgebraReification

namespace ModalityInference.ComparisonControls

open ComparisonAlgebra

theorem Coordinate.modalWith_eval {c : Coordinate} {modeAtom : Nat → Nat}
    {value : BoolExpr} {m : ModExpr} {σ : Nat → Bool} {η : ModVar → Mode} {n : Mode}
    (hs : ∀ i, σ (modeAtom i) = encodeModes η i)
    (hm : c = .unaffected ∨ m.eval (some ∘ η) = some n) :
    (c.modalWith modeAtom value m).eval σ = coordinateValue c (value.eval σ) n := by
  rcases hm with rfl | hm
  · rfl
  have hp : m.project.eval (encodeModes η) = some n := by
    simpa only [ModExpr.project_correct, projectedModes_encodeModes] using hm
  cases hd : m.project.defined.eval (encodeModes η) <;> simp [Projection.eval, hd] at hp
  subst n
  cases c <;> simp only [Coordinate.modalWith, coordinateValue, BoolExpr.eval,
    SymbolicCNF.substitute_eval, hs, Bool.or_false]

def Basis.modalPairs (b : Basis) : List (CompareTy × ModExpr) :=
  [(ComparisonInterpolation.meet b.head b.rest, .const Mode.bottom),
   (ComparisonInterpolation.join b.head b.rest, .const Mode.top),
   (b.bottom, .const Mode.top), (b.top, .const Mode.global), (b.top, .const Mode.many)] ++
    (b.modes.flatMap controls).map fun c =>
      (if c.channel == .lower then b.bottom else b.top, c.expression)

private theorem all_eval (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.all es).eval σ = (es.map fun e => e.eval σ).all id := by
  induction es <;> simp_all [BoolExpr.all, BoolExpr.eval]

private theorem any_eval (es : List BoolExpr) (σ : Nat → Bool) :
    (BoolExpr.any es).eval σ = (es.map fun e => e.eval σ).any id := by
  induction es <;> simp_all [BoolExpr.any, BoolExpr.eval]

private theorem head_values (b : Basis) (headAtom : Nat → Nat) (σ : Nat → Bool)
    (value : CompareTy → Bool)
    (hh : ∀ i (hi : i < b.heads.length), σ (headAtom i) = value b.heads[i]) :
    (b.heads.mapIdx (fun i _ => BoolExpr.atom (headAtom i))).map (fun e => e.eval σ) =
      b.heads.map value := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_mapIdx, BoolExpr.eval]
    exact hh i (by simpa using hj)

private theorem value_meet (value : CompareTy → Bool)
    (hm : ∀ a b, value (.meet a b) = (value a && value b))
    (head : CompareTy) (rest : List CompareTy) :
    value (ComparisonInterpolation.meet head rest) = ((head :: rest).map value).all id := by
  induction rest generalizing head <;>
    simp_all [ComparisonInterpolation.meet]

private theorem value_join (value : CompareTy → Bool)
    (hj : ∀ a b, value (.join a b) = (value a || value b))
    (head : CompareTy) (rest : List CompareTy) :
    value (ComparisonInterpolation.join head rest) = ((head :: rest).map value).any id := by
  induction rest generalizing head <;>
    simp_all [ComparisonInterpolation.join]

theorem Coordinate.modalWith_congr_value (c : Coordinate) (modeAtom : Nat → Nat)
    (m : ModExpr) {left right : BoolExpr} {σ : Nat → Bool}
    (h : left.eval σ = right.eval σ) :
    (c.modalWith modeAtom left m).eval σ = (c.modalWith modeAtom right m).eval σ := by
  cases c <;> simp only [Coordinate.modalWith, BoolExpr.eval, h]

theorem Basis.formula_of_modal (b : Basis) (headAtom modeAtom : Nat → Nat)
    (c : Coordinate) (σ : Nat → Bool) (value : CompareTy → Bool)
    (hj : ∀ a d, value (.join a d) = (value a || value d))
    (hm : ∀ a d, value (.meet a d) = (value a && value d))
    (hh : ∀ i (hi : i < b.heads.length), σ (headAtom i) = value b.heads[i])
    (hmodal : ∀ a m, (a, m) ∈ b.modalPairs →
      value (.modal a m) = (c.modalWith modeAtom (.const (value a)) m).eval σ)
    (k : Key) (hk : k ∈ b.keys) :
    (b.formula headAtom modeAtom c k).eval σ = value (b.term k) := by
  have hlo : (b.formula headAtom modeAtom c .bottom).eval σ = value b.bottom := by
    apply Eq.trans (c.modalWith_congr_value modeAtom (.const Mode.bottom) ?_)
      (hmodal _ _ (by simp [Basis.modalPairs])).symm
    exact (all_eval _ _).trans ((congrArg (fun bs => bs.all id) (head_values b headAtom σ value hh)).trans
      (value_meet value hm b.head b.rest).symm)
  have hhi : (b.formula headAtom modeAtom c .top).eval σ = value b.top := by
    apply Eq.trans (c.modalWith_congr_value modeAtom (.const Mode.top) ?_)
      (hmodal _ _ (by simp [Basis.modalPairs])).symm
    exact (any_eval _ _).trans ((congrArg (fun bs => bs.any id) (head_values b headAtom σ value hh)).trans
      (value_join value hj b.head b.rest).symm)
  cases k with
  | head a =>
    have ha : a ∈ b.heads := by simpa [Basis.keys] using hk
    have hi := List.idxOf_lt_length_of_mem ha
    have he : b.heads[b.heads.idxOf a] = a := by
      simpa only [List.idxOf, beq_iff_eq] using
        (List.findIdx_getElem (xs := b.heads) (p := (· == a)) (w := hi))
    exact (hh _ hi).trans (congrArg value he)
  | bottom => exact hlo
  | top => exact hhi
  | raised =>
    exact (c.modalWith_congr_value modeAtom (.const Mode.top) hlo).trans
      (hmodal _ _ (by simp [Basis.modalPairs])).symm
  | localFloor =>
    exact (c.modalWith_congr_value modeAtom (.const Mode.global) hhi).trans
      (hmodal _ _ (by simp [Basis.modalPairs])).symm
  | affineFloor =>
    exact (c.modalWith_congr_value modeAtom (.const Mode.many) hhi).trans
      (hmodal _ _ (by simp [Basis.modalPairs])).symm
  | control q =>
    have hq : q ∈ b.modes.flatMap controls := by simpa [Basis.keys] using hk
    have hp : (if q.channel == .lower then b.bottom else b.top, q.expression) ∈ b.modalPairs :=
      List.mem_append_right _ (List.mem_map.mpr ⟨q, hq, rfl⟩)
    change (c.modalWith modeAtom
      (if q.channel == .lower then b.formula headAtom modeAtom c .bottom
        else b.formula headAtom modeAtom c .top) q.expression).eval σ = _
    apply Eq.trans (c.modalWith_congr_value modeAtom q.expression ?_) (hmodal _ _ hp).symm
    split <;> assumption

theorem Basis.theoryAt_of_formula (b : Basis) (basisAtom headAtom modeAtom : Nat → Nat)
    (c : Coordinate) (σ : Nat → Bool)
    (h : ∀ i (hi : i < b.keys.length),
      σ (basisAtom i) = (b.formula headAtom modeAtom c b.keys[i]).eval σ) :
    (b.theoryAt basisAtom headAtom modeAtom c).eval σ = true := by
  rw [Basis.theoryAt, all_eval]
  apply List.all_eq_true.mpr
  intro value hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have hi' : i < b.keys.length := by simpa using hi
  simp only [List.getElem_mapIdx, id_eq, BoolExpr.equal, BoolExpr.eval,
    h i hi']
  cases (b.formula headAtom modeAtom c b.keys[i]).eval σ <;> rfl

theorem Basis.theoryAt_of_modal (b : Basis) (basisAtom headAtom modeAtom : Nat → Nat)
    (c : Coordinate) (σ : Nat → Bool) (value : CompareTy → Bool)
    (hj : ∀ a d, value (.join a d) = (value a || value d))
    (hm : ∀ a d, value (.meet a d) = (value a && value d))
    (hh : ∀ i (hi : i < b.heads.length), σ (headAtom i) = value b.heads[i])
    (hb : ∀ i (hi : i < b.types.length), σ (basisAtom i) = value b.types[i])
    (hmodal : ∀ a m, (a, m) ∈ b.modalPairs →
      value (.modal a m) = (c.modalWith modeAtom (.const (value a)) m).eval σ) :
    (b.theoryAt basisAtom headAtom modeAtom c).eval σ = true := by
  apply b.theoryAt_of_formula
  intro i hi
  have hv : σ (basisAtom i) = value (b.term b.keys[i]) := by
    simpa only [Basis.types, List.getElem_map] using hb i (by simpa [Basis.types] using hi)
  exact hv.trans (b.formula_of_modal headAtom modeAtom c σ value hj hm hh hmodal
    _ (List.getElem_mem hi)).symm

end ModalityInference.ComparisonControls

namespace ModalityInference.ComparisonAlgebra

open ComparisonControls

/-- Simultaneous mode substitution is observed through one actual assignment.
The same witness interprets every required label and every type in the interval. -/
theorem observer_substituted_realizable (f : LatticeHom (Order Δ shape) Bool)
    (a b : Carrier Δ shape) (hab : a ≤ b)
    (hb : observer f (a.atMode Mode.bottom) = false)
    (ht : observer f (b.atMode Mode.top) = true)
    (ms : ModVar → ModExpr) (actual : (ModVar → Mode) → ModVar → Mode)
    (hactual : ∀ η v, (ms v).eval (some ∘ η) = some (actual η v))
    (labels : List ModExpr) (hd : ∀ m ∈ labels, DefinedMode Δ (m.subst ms)) :
    ∃ c η, (c = Coordinate.unaffected ∨ ModeModels Δ η) ∧
      ∀ (σ : Nat → Bool) (modeAtom : Nat → Nat),
        (∀ i, σ (modeAtom i) = encodeModes (actual η) i) →
        ∀ t (hrep : Representable Δ shape (t.subst CompareTy.var ms)),
          a.atMode Mode.bottom ≤ represented hrep → represented hrep ≤ b.atMode Mode.top →
          ∀ m ∈ labels,
            booleanValue f ((.modal t m : CompareTy).subst CompareTy.var ms) =
              (c.modalWith modeAtom (.const (booleanValue f (t.subst CompareTy.var ms))) m).eval σ := by
  let prepared := labels.attach.map fun m =>
    GuardedMode.ofDefined (m.val.subst ms) (hd m.val m.property)
  obtain ⟨c, η, hη, he⟩ := observer_modal_realizable f a b hab hb ht prepared
  refine ⟨c, η, hη, ?_⟩
  intro σ modeAtom hs t hrep hlo hhi m hm
  let label := GuardedMode.ofDefined (m.subst ms) (hd m hm)
  have hl : label ∈ prepared :=
    List.mem_map.mpr ⟨⟨m, hm⟩, by simp, rfl⟩
  have hv := he (represented hrep) hlo hhi label hl
  change booleanValue f (label.act (represented hrep)).type = _
  rw [booleanValue_carrier, booleanValue_represented f _ hrep]
  apply hv.trans (Coordinate.modalWith_eval (c := c)
    (value := .const (observer f (represented hrep))) (m := m) (n := label.value η) hs ?_).symm
  rcases hη with hη | hη
  · exact Or.inl hη
  · right
    have hv := label.eval η hη
    change (m.subst ms).eval (some ∘ η) = some (label.value η) at hv
    simpa only [ModExpr.eval_subst, show (fun v => (ms v).eval (some ∘ η)) =
      some ∘ actual η from funext (hactual η)] using hv

end ModalityInference.ComparisonAlgebra
