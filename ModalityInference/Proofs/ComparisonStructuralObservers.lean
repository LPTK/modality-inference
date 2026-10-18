import ModalityInference.Proofs.ComparisonStructuralFamily

namespace ModalityInference.ComparisonStructuralObservers

open ComparisonAlgebra ComparisonStructuralLattice ComparisonStructuralMatrix

/-- Clamping makes every guarded action constant on each fiber of one parent
observer. The parent observer is fixed on both sides. -/
theorem observer_modal_congr {Δ : Bounds} {shape : ComparisonShape}
    (f : LatticeHom (Order Δ shape) Bool) (m : GuardedMode Δ)
    (a b : Carrier Δ shape) (h : observer f a = observer f b) :
    observer f (m.act a) = observer f (m.act b) := by
  have clamp_value (x : Carrier Δ shape) (hl : a.meet b ≤ x) (hu : x ≤ a.join b) :
      observer f (m.act x) =
        ((observer f x || observer f (m.act (a.meet b))) &&
          observer f (m.act (a.join b))) := by
    have he : Order.of (m.act x) =
        Order.of ((x.join (m.act (a.meet b))).meet (m.act (a.join b))) :=
      Quotient.sound ⟨.clamp ((a.meet b).compatible x) (x.compatible (a.join b))
        m.defined hl hu,
        .clampRev ((a.meet b).compatible x) (x.compatible (a.join b)) m.defined hl hu⟩
    exact (congrArg f he).trans ((observer_meet f _ _).trans
      (congrArg (fun x => x && observer f (m.act (a.join b))) (observer_join f _ _)))
  rw [clamp_value a (Carrier.meet_le_left a b) (Carrier.le_join_left a b),
    clamp_value b (Carrier.meet_le_right a b) (Carrier.le_join_right a b), h]

private theorem rectangle_change {a b c d : Bool}
    (h : ((a || d) = (b || c)) ∧ ((a && d) = (b && c))) (hne : a ≠ b) :
    c = a ∧ d = b := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

/-- A Boolean rectangle on arbitrary domains depends on at most one coordinate. -/
theorem rectangle_factor {α β : Type*} (F : α → β → Bool)
    (h : ∀a c b d, (F a b || F c d) = (F a d || F c b) ∧
      (F a b && F c d) = (F a d && F c b)) (a₀ : α) (b₀ : β) :
    (∀a b, F a b = F a b₀) ∨ (∀a b, F a b = F a₀ b) := by
  classical
  by_cases hv : ∃a b c, F a b ≠ F a c
  · obtain ⟨a,b,c,hbc⟩ := hv
    have hr (a' : α) (d : β) : F a' d = F a d := by
      by_cases he : F a b = F a d
      · exact (rectangle_change (h a a' c d) (fun hx => hbc (he.trans hx.symm))).2
      · exact (rectangle_change (h a a' b d) he).2
    exact .inr (fun a' d => (hr a' d).trans (hr a₀ d).symm)
  · exact .inl (fun a b => by by_contra hn; exact hv ⟨a,b,b₀,hn⟩)

def opCarrier (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (a : Carrier Δ s) (b : Carrier Δ t) : Carrier Δ (k.shape s t) :=
  represented (k.op_representable ⟨a.shaped,a.defined,a.shape_eq⟩
    ⟨b.shaped,b.defined,b.shape_eq⟩)

theorem observer_rectangle (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    (a c : Carrier Δ s) (b d : Carrier Δ t) :
    (observer f (opCarrier k a b) || observer f (opCarrier k c d)) =
      (observer f (opCarrier k a d) || observer f (opCarrier k c b)) ∧
    (observer f (opCarrier k a b) && observer f (opCarrier k c d)) =
      (observer f (opCarrier k a d) && observer f (opCarrier k c b)) := by
  have hvalue (p : Bool) := equiv_value f
    (representable_typeOp p
      (k.op_representable ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨b.shaped,b.defined,b.shape_eq⟩)
      (k.op_representable ⟨c.shaped,c.defined,c.shape_eq⟩ ⟨d.shaped,d.defined,d.shape_eq⟩))
    (representable_typeOp p
      (k.op_representable ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨d.shaped,d.defined,d.shape_eq⟩)
      (k.op_representable ⟨c.shaped,c.defined,c.shape_eq⟩ ⟨b.shaped,b.defined,b.shape_eq⟩))
    (ComparisonStructuralMatrix.Kind.rectangle k p (a.compatible c) (b.compatible d))
  have happ (a : Carrier Δ s) (b : Carrier Δ t) :
      booleanValue f (k.op a.type b.type) = observer f (opCarrier k a b) :=
    booleanValue_carrier f (opCarrier k a b)
  simpa only [typeOp, Bool.false_eq_true, if_false, if_true, booleanValue_join,
    booleanValue_meet, happ] using And.intro (hvalue true) (hvalue false)

/-- One parent observer selects a single constructor child for every guarded
outer action simultaneously. -/
theorem observer_factor_family (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    (a₀ : Carrier Δ s) (b₀ : Carrier Δ t) :
    (∀(m : GuardedMode Δ) a b,
      observer f (m.act (opCarrier k a b)) = observer f (m.act (opCarrier k a b₀))) ∨
    (∀(m : GuardedMode Δ) a b,
      observer f (m.act (opCarrier k a b)) = observer f (m.act (opCarrier k a₀ b))) := by
  rcases rectangle_factor (fun a b => observer f (opCarrier k a b))
    (observer_rectangle k f) a₀ b₀ with hl | hr
  · exact .inl (fun m a b => observer_modal_congr f m _ _ (hl a b))
  · exact .inr (fun m a b => observer_modal_congr f m _ _ (hr a b))

/-- Function domains reverse the Boolean order; the sign converts the selected
child into an ordinary lattice observer. -/
def leftSign (k : Kind) (x : Bool) : Bool :=
  match k with
  | .fn => !x
  | _ => x

@[simp] theorem leftSign_involutive (k : Kind) (x : Bool) : leftSign k (leftSign k x) = x := by
  cases k <;> simp [leftSign]

noncomputable def leftObserver (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (b : Carrier Δ t) :
    LatticeHom (Order Δ s) Bool where
  toFun := Quotient.lift (fun a : Carrier Δ s =>
    leftSign k (booleanValue f (k.op a.type b.type))) (by
      intro a c h
      apply congrArg (leftSign k)
      exact equiv_value f
        (k.op_representable ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨b.shaped,b.defined,b.shape_eq⟩)
        (k.op_representable ⟨c.shaped,c.defined,c.shape_eq⟩ ⟨b.shaped,b.defined,b.shape_eq⟩)
        (k.congr h (.refl b.shaped)))
  map_sup' := by
    intro a c
    induction a using Antisymmetrization.induction_on
    induction c using Antisymmetrization.induction_on
    rename_i a c
    change leftSign k (booleanValue f (k.op (.join a.type c.type) b.type)) =
      (leftSign k (booleanValue f (k.op a.type b.type)) ||
        leftSign k (booleanValue f (k.op c.type b.type)))
    have he := observer_left_typeOp k f true
      ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨c.shaped,c.defined,c.shape_eq⟩
      ⟨b.shaped,b.defined,b.shape_eq⟩
    change booleanValue f (k.op (.join a.type c.type) b.type) = _ at he
    rw [he]
    cases k <;> simp [Kind.leftSign, typeOp, leftSign]
  map_inf' := by
    intro a c
    induction a using Antisymmetrization.induction_on
    induction c using Antisymmetrization.induction_on
    rename_i a c
    change leftSign k (booleanValue f (k.op (.meet a.type c.type) b.type)) =
      (leftSign k (booleanValue f (k.op a.type b.type)) &&
        leftSign k (booleanValue f (k.op c.type b.type)))
    have he := observer_left_typeOp k f false
      ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨c.shaped,c.defined,c.shape_eq⟩
      ⟨b.shaped,b.defined,b.shape_eq⟩
    change booleanValue f (k.op (.meet a.type c.type) b.type) = _ at he
    rw [he]
    cases k <;> simp [Kind.leftSign, typeOp, leftSign]

noncomputable def rightObserver (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (a : Carrier Δ s) :
    LatticeHom (Order Δ t) Bool where
  toFun := Quotient.lift (fun b : Carrier Δ t => booleanValue f (k.op a.type b.type)) (by
    intro b d h
    exact equiv_value f
      (k.op_representable ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨b.shaped,b.defined,b.shape_eq⟩)
      (k.op_representable ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨d.shaped,d.defined,d.shape_eq⟩)
      (k.congr (.refl a.shaped) h))
  map_sup' := by
    intro b d
    induction b using Antisymmetrization.induction_on
    induction d using Antisymmetrization.induction_on
    rename_i b d
    exact observer_right_typeOp k f true
      ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨b.shaped,b.defined,b.shape_eq⟩
      ⟨d.shaped,d.defined,d.shape_eq⟩
  map_inf' := by
    intro b d
    induction b using Antisymmetrization.induction_on
    induction d using Antisymmetrization.induction_on
    rename_i b d
    exact observer_right_typeOp k f false
      ⟨a.shaped,a.defined,a.shape_eq⟩ ⟨b.shaped,b.defined,b.shape_eq⟩
      ⟨d.shaped,d.defined,d.shape_eq⟩

theorem leftObserver_value (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (a : Carrier Δ s) (b : Carrier Δ t) :
    leftSign k (observer (leftObserver k f b) a) = observer f (opCarrier k a b) := by
  change leftSign k (leftSign k (booleanValue f (k.op a.type b.type))) = _
  rw [leftSign_involutive]
  exact booleanValue_carrier f (opCarrier k a b)

theorem rightObserver_value (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool) (a : Carrier Δ s) (b : Carrier Δ t) :
    observer (rightObserver k f a) b = observer f (opCarrier k a b) :=
  booleanValue_carrier f (opCarrier k a b)

open ComparisonStructuralFamily in
/-- The selected coordinate is an actual observer of the declared child algebra.
Both families are derived from the same parent observer and outer action. -/
theorem observer_child_family (k : Kind) {Δ : Bounds} {s t : ComparisonShape}
    (f : LatticeHom (Order Δ (k.shape s t)) Bool)
    (a₀ : Carrier Δ s) (b₀ : Carrier Δ t) :
    (∀(m : GuardedMode Δ) a b,
      observer f (m.act (opCarrier k a b)) =
        leftSign k (observer (leftObserver k (actObserver f m) b₀) a)) ∨
    (∀(m : GuardedMode Δ) a b,
      observer f (m.act (opCarrier k a b)) =
        observer (rightObserver k (actObserver f m) a₀) b) := by
  rcases observer_factor_family k f a₀ b₀ with hl | hr
  · exact .inl (fun m a b => (hl m a b).trans (leftObserver_value k (actObserver f m) a b₀).symm)
  · exact .inr (fun m a b => (hr m a b).trans (rightObserver_value k (actObserver f m) a₀ b).symm)

private theorem pair_observer_absorb {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    (f : LatticeHom (Order Δ ((if isSum then Kind.sum else Kind.prod).shape s t)) Bool)
    (m : GuardedMode Δ) (a : Carrier Δ s) (b : Carrier Δ t) :
    observer f (m.act (opCarrier (if isSum then Kind.sum else Kind.prod) a b)) =
      observer f (m.act (opCarrier (if isSum then Kind.sum else Kind.prod) (m.act a) (m.act b))) := by
  apply congrArg f
  apply Quotient.sound
  cases isSum
  · exact ComparisonStructuralFamily.pair_absorb false a.shaped b.shaped m
  · exact ComparisonStructuralFamily.pair_absorb true a.shaped b.shaped m

open ComparisonStructuralFamily in
/-- For products and sums, the selected child observer is also invariant under
its inherited parent action. This retains the root/child action correlation. -/
theorem pair_child_family {Δ : Bounds} {s t : ComparisonShape} (isSum : Bool)
    (f : LatticeHom (Order Δ ((if isSum then Kind.sum else Kind.prod).shape s t)) Bool)
    (a₀ : Carrier Δ s) (b₀ : Carrier Δ t) :
    let k := if isSum then Kind.sum else Kind.prod
    (∀m : GuardedMode Δ,
      (∀a b, observer f (m.act (opCarrier k a b)) =
        observer (leftObserver k (actObserver f m) b₀) a) ∧
      (∀a, observer (leftObserver k (actObserver f m) b₀) (m.act a) =
        observer (leftObserver k (actObserver f m) b₀) a)) ∨
    (∀m : GuardedMode Δ,
      (∀a b, observer f (m.act (opCarrier k a b)) =
        observer (rightObserver k (actObserver f m) a₀) b) ∧
      (∀b, observer (rightObserver k (actObserver f m) a₀) (m.act b) =
        observer (rightObserver k (actObserver f m) a₀) b)) := by
  let k := if isSum then Kind.sum else Kind.prod
  have hsign (x : Bool) : leftSign k x = x := by cases isSum <;> rfl
  rcases observer_factor_family k f a₀ b₀ with hl | hr
  · left
    intro m
    have he (a : Carrier Δ s) (b : Carrier Δ t) :
        observer f (m.act (opCarrier k a b)) = observer (leftObserver k (actObserver f m) b₀) a := by
      exact (hl m a b).trans (by simpa only [hsign] using (leftObserver_value k (actObserver f m) a b₀).symm)
    refine ⟨he, ?_⟩
    intro a
    exact (he (m.act a) (m.act b₀)).symm.trans
      ((pair_observer_absorb isSum f m a b₀).symm.trans (he a b₀))
  · right
    intro m
    have he (a : Carrier Δ s) (b : Carrier Δ t) :
        observer f (m.act (opCarrier k a b)) = observer (rightObserver k (actObserver f m) a₀) b :=
      (hr m a b).trans (rightObserver_value k (actObserver f m) a₀ b).symm
    refine ⟨he, ?_⟩
    intro b
    exact (he (m.act a₀) (m.act b)).symm.trans
      ((pair_observer_absorb isSum f m a₀ b).symm.trans (he a₀ b))

end ModalityInference.ComparisonStructuralObservers
