import ModalityInference.Proofs.GroundOrder
import ModalityInference.Proofs.GroundAssignment

/-! Constraint models and type observations respect mutual ground subtyping.
This is the equality used when eliminating a type variable from a configuration. -/
namespace ModalityInference

def GroundTy.Equivalent (a b : GroundTy) : Prop := GroundOrder a b ∧ GroundOrder b a

theorem GroundTy.Equivalent.refl (a : GroundTy) : a.Equivalent a := ⟨.refl a, .refl a⟩

theorem GroundTy.Equivalent.symm {a b : GroundTy} (h : a.Equivalent b) : b.Equivalent a := ⟨h.2, h.1⟩

theorem GroundTy.Equivalent.trans {a b c : GroundTy} (h : a.Equivalent b) (h' : b.Equivalent c) :
    a.Equivalent c := ⟨h.1.trans h'.1, h'.2.trans h.2⟩

theorem GroundTy.Equivalent.modal {a b : GroundTy} (h : a.Equivalent b) (m : Mode) :
    (a.modal m).Equivalent (b.modal m) := ⟨h.1.modal (Mode.le_refl m), h.2.modal (Mode.le_refl m)⟩

theorem GroundTy.Equivalent.prod {a b c d : GroundTy} (ha : a.Equivalent b) (hc : c.Equivalent d) (m : Mode) :
    (a.prod c m).Equivalent (b.prod d m) :=
  ⟨.prod (Mode.le_refl m) (ha.modal m).1 (hc.modal m).1,
   .prod (Mode.le_refl m) (ha.modal m).2 (hc.modal m).2⟩

theorem GroundTy.Equivalent.sum {a b c d : GroundTy} (ha : a.Equivalent b) (hc : c.Equivalent d) (m : Mode) :
    (a.sum c m).Equivalent (b.sum d m) :=
  ⟨.sum (Mode.le_refl m) (ha.modal m).1 (hc.modal m).1,
   .sum (Mode.le_refl m) (ha.modal m).2 (hc.modal m).2⟩

theorem GroundTy.Equivalent.fn {a b c d : GroundTy} (ha : a.Equivalent b) (hc : c.Equivalent d) (m : Mode) :
    (a.fn c m).Equivalent (b.fn d m) := ⟨.fn ha.2 hc.1 id id, .fn ha.1 hc.2 id id⟩

def EquivalentRealizations : Option GroundTy → Option GroundTy → Prop
  | none, none => True
  | some a, some b => a.Equivalent b
  | _, _ => False

theorem TypeExpr.realize_equivalent (a : Ty) {ρ η : GroundAssignment}
    (ht : ∀ v ∈ a.typeVars, (ρ.types v).Equivalent (η.types v))
    (hm : ∀ v ∈ a.modVars, ρ.modes v = η.modes v) :
    EquivalentRealizations (a.realize ρ) (a.realize η) := by
  induction a <;> simp only [TypeExpr.typeVars, TypeExpr.modVars, Finset.mem_union,
    or_imp, forall_and] at ht hm
  case prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    have ha := iha ht.1 hm.1
    have hb := ihb ht.2 hm.2
    cases hρa : a.realize ρ <;> cases hηa : a.realize η <;>
      cases hρb : b.realize ρ <;> cases hηb : b.realize η <;>
      simp_all [EquivalentRealizations, TypeExpr.realize]
    all_goals first | exact iha.prod ihb _ | exact iha.sum ihb _ | exact iha.fn ihb _
  case modal a m ih =>
    have ha := ih ht hm.1
    have hmode := m.eval_congr (σ := some ∘ ρ.modes) (τ := some ∘ η.modes)
      (fun v hv => congrArg some (hm.2 v hv))
    cases hρ : a.realize ρ <;> cases hη : a.realize η <;>
      cases hm : m.eval (some ∘ ρ.modes) <;>
      simp_all [EquivalentRealizations, TypeExpr.realize]
    all_goals simp only [← hmode, Option.bind_some, Option.bind_none]
    exact ih.modal _
  case var v => exact ht v (by simp)
  case unit | credit => exact GroundTy.Equivalent.refl _

theorem EquivalentRealizations.some_left {a b : Option GroundTy} (h : EquivalentRealizations a b)
    {x} (hx : a = some x) : ∃ y, b = some y ∧ x.Equivalent y := by
  cases a <;> cases b <;> simp_all [EquivalentRealizations]

theorem GroundSatisfies.transport {ρ η : GroundAssignment} {c : Constraint}
    (h : GroundSatisfies ρ c)
    (ht : ∀ v ∈ c.typeVars, (ρ.types v).Equivalent (η.types v))
    (hm : ∀ v ∈ c.modVars, ρ.modes v = η.modes v) : GroundSatisfies η c := by
  cases c <;> simp only [Constraint.typeVars, Constraint.modVars, Finset.mem_union,
    Finset.mem_insert, or_imp, forall_and, forall_eq] at ht hm
  case sub a b =>
    obtain ⟨x, y, hx, hy, hs⟩ := h
    obtain ⟨x', hx', heqx⟩ := (a.realize_equivalent ht.1 hm.1).some_left hx
    obtain ⟨y', hy', heqy⟩ := (b.realize_equivalent ht.2 hm.2).some_left hy
    exact ⟨x', y', hx', hy', (heqx.2.trans ((GroundOrder.of_subtype hs).trans heqy.1)).to_subtype⟩
  case equiv a b =>
    obtain ⟨x, y, hx, hy, hxy, hyx⟩ := h
    obtain ⟨x', hx', heqx⟩ := (a.realize_equivalent ht.1 hm.1).some_left hx
    obtain ⟨y', hy', heqy⟩ := (b.realize_equivalent ht.2 hm.2).some_left hy
    exact ⟨x', y', hx', hy',
      (heqx.2.trans ((GroundOrder.of_subtype hxy).trans heqy.1)).to_subtype,
      (heqy.2.trans ((GroundOrder.of_subtype hyx).trans heqx.1)).to_subtype⟩
  case equal v t =>
    obtain ⟨x, hx, hvx, hxv⟩ := h
    obtain ⟨x', hx', heqx⟩ := (t.realize_equivalent ht.2 hm).some_left hx
    exact ⟨x', hx',
      (ht.1.2.trans ((GroundOrder.of_subtype hvx).trans heqx.1)).to_subtype,
      (heqx.2.trans ((GroundOrder.of_subtype hxv).trans ht.1.1)).to_subtype⟩
  case mode a b =>
    exact (GroundSatisfies.congr (.mode a b) (by simp [Constraint.typeVars])
      (by simpa [Constraint.modVars, Finset.mem_union, or_imp, forall_and] using hm)).mp h
  case defined a => exact (GroundSatisfies.congr (.defined a) (by simp [Constraint.typeVars]) hm).mp h

theorem GroundSatisfies.equivalent {ρ η : GroundAssignment} (c : Constraint)
    (ht : ∀ v ∈ c.typeVars, (ρ.types v).Equivalent (η.types v))
    (hm : ∀ v ∈ c.modVars, ρ.modes v = η.modes v) :
    GroundSatisfies ρ c ↔ GroundSatisfies η c :=
  ⟨fun h => h.transport ht hm,
   fun h => h.transport (fun v hv => (ht v hv).symm) (fun v hv => (hm v hv).symm)⟩

theorem GroundModels.equivalent {ρ η : GroundAssignment} (cs : Bounds)
    (ht : ∀ v ∈ cs.typeVars, (ρ.types v).Equivalent (η.types v))
    (hm : ∀ v ∈ cs.modVars, ρ.modes v = η.modes v) : GroundModels ρ cs ↔ GroundModels η cs := by
  induction cs <;> simp_all [Bounds.typeVars_cons, Bounds.modVars_cons,
    Finset.mem_union, or_imp, forall_and, GroundModels]
  exact fun _ => GroundSatisfies.equivalent _ ht.1 hm.1

end ModalityInference
