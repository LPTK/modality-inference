import ModalityInference.Proofs.GroundSubtyping

/-! A structural presentation of subtyping between ground types. It retains the
whole field types, with inherited modes, and future-only function comparisons. -/
namespace ModalityInference

@[simp] theorem Mode.compose_self (m : Mode) : m.compose m = m := by
  cases m
  simp [Mode.compose]

theorem Mode.compose_comm (m n : Mode) : m.compose n = n.compose m := by
  cases m
  cases n
  simp [Mode.compose, Bool.and_comm]

@[simp] theorem Mode.le_refl (m : Mode) : m.le m = true := by
  simp [Mode.le_iff]

@[simp] theorem Mode.compose_absorb_left (m n : Mode) : m.compose (m.compose n) = m.compose n := by
  rw [← Mode.compose_assoc, Mode.compose_self]

@[simp] theorem Mode.compose_absorb_right (m n : Mode) : n.compose (m.compose n) = m.compose n := by
  rw [Mode.compose_comm n (m.compose n), Mode.compose_assoc, Mode.compose_self]

inductive GroundOrder : GroundTy → GroundTy → Prop where
  | unit {m n} : m.le n = true → GroundOrder (.unit m) (.unit n)
  | credit {m n} : m.le n = true → GroundOrder (.credit m) (.credit n)
  | prod {a b c d m n} : m.le n = true →
      GroundOrder (a.modal m) (c.modal n) → GroundOrder (b.modal m) (d.modal n) →
      GroundOrder (.prod a b m) (.prod c d n)
  | sum {a b c d m n} : m.le n = true →
      GroundOrder (a.modal m) (c.modal n) → GroundOrder (b.modal m) (d.modal n) →
      GroundOrder (.sum a b m) (.sum c d n)
  | fn {a b c d m n} : GroundOrder c a → GroundOrder b d →
      (m.isLocal = true → n.isLocal = true) → (m.once = true → n.once = true) →
      GroundOrder (.fn a b m) (.fn c d n)

theorem Mode.compose_le {m n p q : Mode} (hmn : m.le n = true) (hpq : p.le q = true) :
    (m.compose p).le (n.compose q) = true :=
  Mode.le_trans (Mode.compose_le_right p hmn) (Mode.compose_le_left n hpq)

theorem GroundOrder.modal {a b} (h : GroundOrder a b) {p q} (hpq : p.le q = true) :
    GroundOrder (a.modal p) (b.modal q) := by
  induction h generalizing p q
  case unit hmn => exact .unit (Mode.compose_le hmn hpq)
  case credit hmn => exact .credit (Mode.compose_le hmn hpq)
  case prod a b c d m n hmn ha hb iha ihb =>
    exact .prod (Mode.compose_le hmn hpq)
      (by simpa only [GroundTy.modal_compose] using iha hpq)
      (by simpa only [GroundTy.modal_compose] using ihb hpq)
  case sum a b c d m n hmn ha hb iha ihb =>
    exact .sum (Mode.compose_le hmn hpq)
      (by simpa only [GroundTy.modal_compose] using iha hpq)
      (by simpa only [GroundTy.modal_compose] using ihb hpq)
  case fn a b c d m n ha hb hl hf iha ihb =>
    have hpq' := (Mode.le_iff _ _).mp hpq
    exact .fn ha hb
      (fun h => Bool.and_eq_true_iff.mpr
        ⟨hl (Bool.and_eq_true_iff.mp h).1, hpq'.1 (Bool.and_eq_true_iff.mp h).2⟩)
      (fun h => Bool.and_eq_true_iff.mpr
        ⟨hf (Bool.and_eq_true_iff.mp h).1, hpq'.2.1 (Bool.and_eq_true_iff.mp h).2⟩)

theorem GroundOrder.refl (a : GroundTy) : GroundOrder a a := by
  induction a
  case unit m => exact .unit (Mode.le_refl m)
  case credit m => exact .credit (Mode.le_refl m)
  case prod a b m iha ihb => exact .prod (Mode.le_refl m) (iha.modal (Mode.le_refl m)) (ihb.modal (Mode.le_refl m))
  case sum a b m iha ihb => exact .sum (Mode.le_refl m) (iha.modal (Mode.le_refl m)) (ihb.modal (Mode.le_refl m))
  case fn a b m iha ihb => exact .fn iha ihb id id

def GroundTy.nodes : GroundTy → Nat
  | .unit _ | .credit _ => 1
  | .prod a b _ | .sum a b _ | .fn a b _ => a.nodes + b.nodes + 1

@[simp] theorem GroundTy.nodes_modal (a : GroundTy) (m : Mode) : (a.modal m).nodes = a.nodes := by
  cases a <;> rfl

theorem GroundOrder.trans {a b c} (hab : GroundOrder a b) (hbc : GroundOrder b c) : GroundOrder a c := by
  cases hab
  case unit m n hmn =>
    cases hbc with
    | unit hnp => exact .unit (Mode.le_trans hmn hnp)
  case credit m n hmn =>
    cases hbc with
    | credit hnp => exact .credit (Mode.le_trans hmn hnp)
  case prod a b c d m n hmn hac hbd =>
    cases hbc with
    | prod hnp hce hdf => exact .prod (Mode.le_trans hmn hnp) (hac.trans hce) (hbd.trans hdf)
  case sum a b c d m n hmn hac hbd =>
    cases hbc with
    | sum hnp hce hdf => exact .sum (Mode.le_trans hmn hnp) (hac.trans hce) (hbd.trans hdf)
  case fn a b c d m n hca hbd hlocal honce =>
    cases hbc with
    | fn hec hdf hlocal' honce' =>
      exact .fn (hec.trans hca) (hbd.trans hdf) (hlocal' ∘ hlocal) (honce' ∘ honce)
termination_by b.nodes
decreasing_by all_goals simp_all only [GroundTy.nodes_modal, GroundTy.nodes]; omega

private theorem Subtype.modal_intersection {a b : GroundTy} {m n : Mode}
    (h : Subtype [] (a.modal m).reify (b.modal n).reify) :
    Subtype [] (.modal a.reify (.const (m.compose n))) (.modal b.reify (.const (m.compose n))) := by
  have hh := h.ground_modal (Mode.le_refl (m.compose n))
  simp only [GroundTy.modal_compose, Mode.compose_absorb_left, Mode.compose_absorb_right] at hh
  exact (a.reify_modal_right _ []).trans (hh.trans (b.reify_modal_left _ []))

/-- The structural relation is derivable using the original declarative rules.
Different product/sum modes are mediated by their composed mode. -/
theorem GroundOrder.to_subtype {a b} (h : GroundOrder a b) : Subtype [] a.reify b.reify := by
  induction h
  case unit m n hmn => exact .congr .refl (.valid fun _ _ => ⟨m, n, rfl, rfl, hmn⟩)
  case credit m n hmn => exact .congr .refl (.valid fun _ _ => ⟨m, n, rfl, rfl, hmn⟩)
  case fn a b c d m n hca hbd hlocal honce iha ihb =>
    exact .fn iha ihb (.valid fun _ _ => ⟨m, n.compose Mode.top, rfl, rfl, by
      simpa [Mode.le_iff, Mode.compose, Mode.top] using And.intro hlocal honce⟩)
  case prod a b c d m n hmn hac hbd iha ihb =>
    have hmk : m.le (m.compose n) = true := by simpa using Mode.compose_le_left m hmn
    have hkn : (m.compose n).le n = true := by simpa using Mode.compose_le_right n hmn
    exact (Subtype.congr .refl (.valid fun _ _ => ⟨m, m.compose n, rfl, rfl, hmk⟩)).trans
      ((Subtype.prod iha.modal_intersection ihb.modal_intersection).trans
        (.congr .refl (.valid fun _ _ => ⟨m.compose n, n, rfl, rfl, hkn⟩)))
  case sum a b c d m n hmn hac hbd iha ihb =>
    have hmk : m.le (m.compose n) = true := by simpa using Mode.compose_le_left m hmn
    have hkn : (m.compose n).le n = true := by simpa using Mode.compose_le_right n hmn
    exact (Subtype.congr .refl (.valid fun _ _ => ⟨m, m.compose n, rfl, rfl, hmk⟩)).trans
      ((Subtype.sum iha.modal_intersection ihb.modal_intersection).trans
        (.congr .refl (.valid fun _ _ => ⟨m.compose n, n, rfl, rfl, hkn⟩)))

private def OptGroundOrder : Option GroundTy → Option GroundTy → Prop
  | none, none => True
  | some a, some b => GroundOrder a b
  | _, _ => False

private theorem OptGroundOrder.refl (a : Option GroundTy) : OptGroundOrder a a :=
  match a with
  | none => trivial
  | some a => GroundOrder.refl a

private theorem OptGroundOrder.trans {a b c}
    (hab : OptGroundOrder a b) (hbc : OptGroundOrder b c) : OptGroundOrder a c := by
  cases a <;> cases b <;> cases c <;> simp only [OptGroundOrder] at *
  exact hab.trans hbc

private theorem Subtype.optGroundOrder {ρ Δ a b} (h : Subtype Δ a b)
    (hmodes : ModeModels Δ ρ.modes)
    (hbounds : ∀ a b, Constraint.sub a b ∈ Δ → OptGroundOrder (a.realize ρ) (b.realize ρ)) :
    OptGroundOrder (a.realize ρ) (b.realize ρ) := by
  induction h
  case fn a b c d m n _ _ hmode iha ihb =>
    have hmn := hmode.denote hmodes
    cases hm : m.eval (some ∘ ρ.modes) <;> cases hn : n.eval (some ∘ ρ.modes) <;>
      simp [ModExpr.Below, ModExpr.eval, ModExpr.top, hm, hn] at hmn
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      simp_all [OptGroundOrder, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    exact .fn iha ihb
      (by simpa [Mode.compose, Mode.top] using ((Mode.le_iff _ _).mp hmn).1)
      (by simpa [Mode.compose, Mode.top] using ((Mode.le_iff _ _).mp hmn).2.1)
  case prod a b c d m _ _ iha ihb | sum a b c d m _ _ iha ihb =>
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      cases hm : m.eval (some ∘ ρ.modes) <;>
      simp_all [OptGroundOrder, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    all_goals first | exact .prod (Mode.le_refl _) iha ihb | exact .sum (Mode.le_refl _) iha ihb
  case congr a b m n _ hmode ih =>
    obtain ⟨u, v, hm, hn, huv⟩ := hmode.denote hmodes
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      simp_all [OptGroundOrder, TypeExpr.realize]
    exact ih.modal huv
  case bound a b hc => exact hbounds a b hc
  all_goals try simp only [TypeExpr.realize_identity, TypeExpr.realize_compose]
  all_goals solve_by_elim [OptGroundOrder.refl, OptGroundOrder.trans]

theorem GroundOrder.of_subtype {a b : GroundTy} (h : Subtype [] a.reify b.reify) :
    GroundOrder a b := by
  have hh := h.optGroundOrder (ρ := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩)
    (by simp [ModeModels]) (by simp)
  simpa only [GroundTy.realize_reify, OptGroundOrder] using hh

theorem GroundOrder.iff_subtype {a b : GroundTy} :
    GroundOrder a b ↔ Subtype [] a.reify b.reify := ⟨GroundOrder.to_subtype, GroundOrder.of_subtype⟩

@[simp] theorem GroundOrder.prod_iff {a b c d m n} :
    GroundOrder (.prod a b m) (.prod c d n) ↔ m.le n = true ∧
      GroundOrder (a.modal m) (c.modal n) ∧ GroundOrder (b.modal m) (d.modal n) := by
  constructor
  · intro h; cases h; exact ⟨‹_›, ‹_›, ‹_›⟩
  · rintro ⟨hm, ha, hb⟩; exact .prod hm ha hb

@[simp] theorem GroundOrder.sum_iff {a b c d m n} :
    GroundOrder (.sum a b m) (.sum c d n) ↔ m.le n = true ∧
      GroundOrder (a.modal m) (c.modal n) ∧ GroundOrder (b.modal m) (d.modal n) := by
  constructor
  · intro h; cases h; exact ⟨‹_›, ‹_›, ‹_›⟩
  · rintro ⟨hm, ha, hb⟩; exact .sum hm ha hb

@[simp] theorem GroundOrder.fn_iff {a b c d m n} :
    GroundOrder (.fn a b m) (.fn c d n) ↔
      GroundOrder c a ∧ GroundOrder b d ∧ m.le (n.compose Mode.top) = true := by
  constructor
  · intro h
    cases h with
    | fn ha hb hl ho => exact ⟨ha, hb, by simpa [Mode.le_iff, Mode.compose, Mode.top] using And.intro hl ho⟩
  · rintro ⟨ha, hb, hm⟩
    exact .fn ha hb
      (by simpa [Mode.compose, Mode.top] using ((Mode.le_iff _ _).mp hm).1)
      (by simpa [Mode.compose, Mode.top] using ((Mode.le_iff _ _).mp hm).2.1)

@[simp] theorem GroundOrder.unit_iff {m n} : GroundOrder (.unit m) (.unit n) ↔ m.le n = true := by
  constructor
  · intro h; cases h; assumption
  · exact GroundOrder.unit

@[simp] theorem GroundOrder.credit_iff {m n} :
    GroundOrder (.credit m) (.credit n) ↔ m.le n = true := by
  constructor
  · intro h; cases h; assumption
  · exact GroundOrder.credit

end ModalityInference
