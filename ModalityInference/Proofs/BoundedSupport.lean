import ModalityInference.Proofs.ModeOrientation
import ModalityInference.Proofs.SubstitutionSupport

/-! Finite identifier bounds for fresh allocation in the solver. -/
namespace ModalityInference

def ModExpr.Bounded (nm : Nat) : ModExpr → Prop
  | .const _ => True
  | .var v => v.index < nm
  | .compose a b | .meet a b | .join a b | .leftResidual a b | .rightResidual a b =>
    a.Bounded nm ∧ b.Bounded nm
  | .close a | .closeInv a | .future a | .capture a => a.Bounded nm

def TypeExpr.Bounded (nt nm : Nat) : Ty → Prop
  | .var v => v.index < nt
  | .unit | .credit => True
  | .prod a b | .sum a b | .fn a b => a.Bounded nt nm ∧ b.Bounded nt nm
  | .modal a m => a.Bounded nt nm ∧ m.Bounded nm

def Constraint.Bounded (nt nm : Nat) : Constraint → Prop
  | .sub a b | .equiv a b => a.Bounded nt nm ∧ b.Bounded nt nm
  | .equal v a => v.index < nt ∧ a.Bounded nt nm
  | .mode a b => a.Bounded nm ∧ b.Bounded nm
  | .defined a => a.Bounded nm

def Bounds.Bounded (nt nm : Nat) (cs : Bounds) : Prop := ∀ c ∈ cs, c.Bounded nt nm

theorem ModExpr.bounded_iff (m : ModExpr) (nm : Nat) :
    m.Bounded nm ↔ ∀ v ∈ m.vars, v.index < nm := by
  induction m <;> simp_all [Bounded, vars, or_imp, forall_and]

theorem TypeExpr.bounded_iff (a : Ty) (nt nm : Nat) : a.Bounded nt nm ↔
    (∀ v ∈ a.typeVars, v.index < nt) ∧ (∀ v ∈ a.modVars, v.index < nm) := by
  induction a <;> simp_all [Bounded, typeVars, modVars, ModExpr.bounded_iff,
    or_imp, forall_and, and_assoc, and_left_comm, and_comm]

theorem Constraint.bounded_iff (c : Constraint) (nt nm : Nat) : c.Bounded nt nm ↔
    (∀ v ∈ c.typeVars, v.index < nt) ∧ (∀ v ∈ c.modVars, v.index < nm) := by
  cases c <;> simp [Bounded, typeVars, modVars, TypeExpr.bounded_iff, ModExpr.bounded_iff,
    or_imp, forall_and, and_assoc, and_left_comm, and_comm]

theorem Bounds.bounded_iff (cs : Bounds) (nt nm : Nat) : cs.Bounded nt nm ↔
    (∀ v ∈ cs.typeVars, v.index < nt) ∧ (∀ v ∈ cs.modVars, v.index < nm) := by
  simp only [Bounded, Constraint.bounded_iff, forall_and, mem_typeVars_iff, mem_modVars_iff]
  aesop

@[simp] theorem Bounds.bounded_nil (nt nm : Nat) : Bounds.Bounded nt nm [] := by simp [Bounded]

@[simp] theorem Bounds.bounded_cons {c : Constraint} {cs : Bounds} {nt nm} :
    Bounds.Bounded nt nm (c :: cs) ↔ c.Bounded nt nm ∧ cs.Bounded nt nm := by
  simp [Bounded]

@[simp] theorem Bounds.bounded_append {cs ds : Bounds} {nt nm} :
    (cs ++ ds).Bounded nt nm ↔ cs.Bounded nt nm ∧ ds.Bounded nt nm := by
  simp [Bounded, or_imp, forall_and]

theorem ModExpr.Bounded.mono {m : ModExpr} {nm nm'} (h : m.Bounded nm) (hm : nm ≤ nm') :
    m.Bounded nm' :=
  (m.bounded_iff nm').mpr fun v hv => ((m.bounded_iff nm).mp h v hv).trans_le hm

theorem TypeExpr.Bounded.mono {a : Ty} {nt nm nt' nm'} (h : a.Bounded nt nm)
    (ht : nt ≤ nt') (hm : nm ≤ nm') : a.Bounded nt' nm' := by
  obtain ⟨ha, hb⟩ := (a.bounded_iff nt nm).mp h
  exact (a.bounded_iff nt' nm').mpr
    ⟨fun v hv => (ha v hv).trans_le ht, fun v hv => (hb v hv).trans_le hm⟩

theorem Constraint.Bounded.mono {c : Constraint} {nt nm nt' nm'} (h : c.Bounded nt nm)
    (ht : nt ≤ nt') (hm : nm ≤ nm') : c.Bounded nt' nm' := by
  obtain ⟨ha, hb⟩ := (c.bounded_iff nt nm).mp h
  exact (c.bounded_iff nt' nm').mpr
    ⟨fun v hv => (ha v hv).trans_le ht, fun v hv => (hb v hv).trans_le hm⟩

theorem Bounds.Bounded.mono {cs : Bounds} {nt nm nt' nm'} (h : cs.Bounded nt nm)
    (ht : nt ≤ nt') (hm : nm ≤ nm') : cs.Bounded nt' nm' :=
  fun c hc => (h c hc).mono ht hm

theorem ModExpr.Bounded.subst {m : ModExpr} {nm nm'} {σ : ModVar → ModExpr} (h : m.Bounded nm)
    (hσ : ∀ v, v.index < nm → (σ v).Bounded nm') : (m.subst σ).Bounded nm' := by
  induction m <;> simp_all [ModExpr.Bounded, ModExpr.subst]

theorem TypeExpr.Bounded.subst {a : Ty} {nt nm nt' nm'}
    {σ : TypeVar → Ty} {μ : ModVar → ModExpr} (h : a.Bounded nt nm)
    (hσ : ∀ v, v.index < nt → (σ v).Bounded nt' nm')
    (hμ : ∀ v, v.index < nm → (μ v).Bounded nm') : (a.subst σ μ).Bounded nt' nm' := by
  induction a <;> simp_all [TypeExpr.Bounded, TypeExpr.subst]
  exact h.2.subst hμ

theorem ModExpr.Bounded.normalize {m : ModExpr} {nm} (h : m.Bounded nm) :
    m.normalize.Bounded nm := by
  simpa only [ModExpr.bounded_iff, ModExpr.normalize_vars] using h

theorem TypeExpr.Bounded.normalize {a : Ty} {nt nm} (h : a.Bounded nt nm) :
    a.normalize.Bounded nt nm := by
  induction a <;> simp only [TypeExpr.normalize]
  all_goals try solve | simp_all [TypeExpr.Bounded]
  rename_i a m ih
  have ha := ih h.1
  have hm := h.2.normalize
  split
  · rename_i b k hk
    have hb : b.Bounded nt nm ∧ k.Bounded nm := by simpa only [hk, TypeExpr.Bounded] using ha
    exact ⟨hb.1, ModExpr.Bounded.normalize (And.intro hb.2 hm)⟩
  · split
    · exact ha
    · exact ⟨ha, hm⟩

theorem Constraint.Bounded.normalize {c : Constraint} {nt nm} (h : c.Bounded nt nm) :
    c.normalize.Bounded nt nm := by
  cases c <;> simp only [Constraint.normalize, Constraint.Bounded] at *
  all_goals aesop (add safe apply [TypeExpr.Bounded.normalize, ModExpr.Bounded.normalize])

theorem TypeExpr.Bounded.outer {a : Ty} {nt nm} (h : a.Bounded nt nm) :
    a.outer.1.Bounded nt nm ∧ a.outer.2.Bounded nm := by
  induction a <;> simp_all [TypeExpr.outer, TypeExpr.Bounded, ModExpr.Bounded, ModExpr.epsilon]

theorem TypeExpr.Bounded.wellFormedBounds {a : Ty} {nt nm} (ha : a.Bounded nt nm) :
    a.wellFormedBounds.Bounded nt nm := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, TypeExpr.Bounded, Constraint.Bounded]

structure Substitution.Bounded (nt nm : Nat) (σ : Substitution) : Prop where
  types : ∀ n a, (n, a) ∈ σ.types → n < nt ∧ a.Bounded nt nm
  modes : ∀ n m, (n, m) ∈ σ.modes → n < nm ∧ m.Bounded nm

theorem Substitution.Bounded.mono {σ : Substitution} {nt nm nt' nm'} (h : σ.Bounded nt nm)
    (ht : nt ≤ nt') (hm : nm ≤ nm') : σ.Bounded nt' nm' :=
  ⟨fun n a ha => ⟨(h.types n a ha).1.trans_le ht, (h.types n a ha).2.mono ht hm⟩,
    fun n m hh => ⟨(h.modes n m hh).1.trans_le hm, (h.modes n m hh).2.mono hm⟩⟩

theorem Substitution.Bounded.type {σ : Substitution} {nt nm} (hσ : σ.Bounded nt nm)
    (v : TypeVar) (hv : v.index < nt) : (σ.type v).Bounded nt nm := by
  cases v with
  | rigid n => exact hv
  | flex n =>
    cases he : σ.types.lookup n
    · simpa [Substitution.type, he, TypeExpr.Bounded] using hv
    · obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [Substitution.type, he, Option.getD_some] using
        (hσ.types n _ (by simp [hh])).2

theorem Substitution.Bounded.mode {σ : Substitution} {nt nm} (hσ : σ.Bounded nt nm)
    (v : ModVar) (hv : v.index < nm) : (σ.mode v).Bounded nm := by
  cases v with
  | rigid n => exact hv
  | flex n =>
    cases he : σ.modes.lookup n
    · simpa [Substitution.mode, he, ModExpr.Bounded] using hv
    · obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [Substitution.mode, he, Option.getD_some] using
        (hσ.modes n _ (by simp [hh])).2

theorem Substitution.Bounded.ty {σ : Substitution} {nt nm} (hσ : σ.Bounded nt nm)
    {a : Ty} (ha : a.Bounded nt nm) : (σ.ty a).Bounded nt nm := ha.subst hσ.type hσ.mode

theorem Substitution.Bounded.constraint {σ : Substitution} {nt nm} (hσ : σ.Bounded nt nm)
    {c : Constraint} (hc : c.Bounded nt nm) : (σ.constraint c).Bounded nt nm := by
  cases c <;> simp only [Substitution.constraint, Constraint.subst, Constraint.Bounded] at *
  case sub a b | equiv a b => exact ⟨hσ.ty hc.1, hσ.ty hc.2⟩
  case mode a b => exact ⟨hc.1.subst hσ.mode, hc.2.subst hσ.mode⟩
  case defined a => exact hc.subst hσ.mode
  case equal v a =>
    cases v with
    | rigid n => exact ⟨hc.1, hσ.ty hc.2⟩
    | flex n =>
      cases he : σ.types.lookup n <;> simp only [he]
      · exact ⟨hc.1, hσ.ty hc.2⟩
      · have hn := hσ.type (.flex n) hc.1
        simp only [Substitution.type, he, Option.getD_some] at hn
        exact ⟨hn, hσ.ty hc.2⟩

theorem Substitution.Bounded.bounds {σ : Substitution} {nt nm} (hσ : σ.Bounded nt nm)
    {cs : Bounds} (hc : cs.Bounded nt nm) : (σ.bounds cs).Bounded nt nm := by
  rintro _ hh
  obtain ⟨c, hm, rfl⟩ := List.mem_map.mp hh
  exact hσ.constraint (hc c hm)

theorem Substitution.bounded_empty (nt nm : Nat) : ({} : Substitution).Bounded nt nm :=
  ⟨by simp, by simp⟩

theorem Substitution.bounded_singleType {n a nt nm} (hn : n < nt) (ha : TypeExpr.Bounded nt nm a) :
    ({types := [(n, a)]} : Substitution).Bounded nt nm := by
  exact ⟨by simpa using And.intro hn ha, by simp⟩

theorem Substitution.Bounded.extendType {σ : Substitution} {nt nm} (hσ : σ.Bounded nt nm)
    {n a} (hn : n < nt) (ha : TypeExpr.Bounded nt nm a) : (σ.extendType n a).Bounded nt nm := by
  refine ⟨?_, hσ.modes⟩
  intro k b hb
  simp only [Substitution.extendType, List.mem_cons, List.mem_map, List.mem_filter,
    Prod.exists, Prod.mk.injEq] at hb
  rcases hb with ⟨rfl, rfl⟩ | ⟨j, c, ⟨hc, _⟩, rfl, rfl⟩
  · exact ⟨hn, ha⟩
  · exact ⟨(hσ.types j c hc).1,
      (Substitution.bounded_singleType hn ha).ty (hσ.types j c hc).2⟩

theorem Substitution.Bounded.type_above {σ : Substitution} {nt nm} (hσ : σ.Bounded nt nm)
    {n : Nat} (hn : nt ≤ n) : σ.type (.flex n) = .var (.flex n) := by
  apply σ.type_fresh
  intro hkey
  obtain ⟨⟨k, a⟩, ha, rfl⟩ := List.mem_map.mp hkey
  have hk := (hσ.types k a ha).1
  omega

theorem Substitution.Bounded.mode_above {σ : Substitution} {nt nm} (hσ : σ.Bounded nt nm)
    {n : Nat} (hn : nm ≤ n) : σ.mode (.flex n) = .var (.flex n) := by
  cases he : σ.modes.lookup n
  · simp [Substitution.mode, he]
  · rename_i m
    obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
    have hk := (hσ.modes n m (by simp [hh])).1
    omega

end ModalityInference
