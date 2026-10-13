import ModalityInference.Proofs.SubstitutionSupport
import ModalityInference.Proofs.Normalization

/-! Syntactic preservation of the absence of rigid identifiers. -/
namespace ModalityInference

def ModExpr.Flexible : ModExpr → Prop
  | .const _ => True
  | .var v => ∃ n, v = .flex n
  | .compose a b | .meet a b | .join a b | .leftResidual a b | .rightResidual a b =>
    a.Flexible ∧ b.Flexible
  | .close a | .closeInv a | .future a | .capture a => a.Flexible

def TypeExpr.Flexible : Ty → Prop
  | .var v => ∃ n, v = .flex n
  | .unit | .credit => True
  | .prod a b | .sum a b | .fn a b => a.Flexible ∧ b.Flexible
  | .modal a m => a.Flexible ∧ m.Flexible

def Constraint.Flexible : Constraint → Prop
  | .sub a b | .equiv a b => a.Flexible ∧ b.Flexible
  | .equal v a => (∃ n, v = .flex n) ∧ a.Flexible
  | .mode a b => a.Flexible ∧ b.Flexible
  | .defined a => a.Flexible

def Bounds.Flexible (cs : Bounds) : Prop := ∀ c ∈ cs, c.Flexible

theorem ModExpr.flexible_iff (m : ModExpr) :
    m.Flexible ↔ ∀ v ∈ m.vars, ∃ n, v = .flex n := by
  induction m <;> simp_all [Flexible, vars, or_imp, forall_and]

theorem TypeExpr.flexible_iff (a : Ty) : a.Flexible ↔
    (∀ v ∈ a.typeVars, ∃ n, v = .flex n) ∧ (∀ v ∈ a.modVars, ∃ n, v = .flex n) := by
  induction a <;> simp_all [Flexible, typeVars, modVars, ModExpr.flexible_iff,
    or_imp, forall_and, and_assoc, and_left_comm, and_comm]

theorem Constraint.flexible_iff (c : Constraint) : c.Flexible ↔
    (∀ v ∈ c.typeVars, ∃ n, v = .flex n) ∧ (∀ v ∈ c.modVars, ∃ n, v = .flex n) := by
  cases c <;> simp [Flexible, typeVars, modVars, TypeExpr.flexible_iff, ModExpr.flexible_iff,
    or_imp, forall_and, and_assoc, and_left_comm, and_comm]

theorem Bounds.flexible_iff (cs : Bounds) : cs.Flexible ↔
    (∀ v ∈ cs.typeVars, ∃ n, v = .flex n) ∧ (∀ v ∈ cs.modVars, ∃ n, v = .flex n) := by
  simp only [Flexible, Constraint.flexible_iff, forall_and, mem_typeVars_iff, mem_modVars_iff]
  aesop

@[simp] theorem Bounds.flexible_nil : Bounds.Flexible [] := by simp [Flexible]

@[simp] theorem Bounds.flexible_cons {c : Constraint} {cs : Bounds} :
    Bounds.Flexible (c :: cs) ↔ c.Flexible ∧ cs.Flexible := by
  simp [Flexible]

@[simp] theorem Bounds.flexible_append {cs ds : Bounds} :
    (cs ++ ds).Flexible ↔ cs.Flexible ∧ ds.Flexible := by
  simp [Flexible, or_imp, forall_and]

theorem ModExpr.Flexible.subst {m : ModExpr} {σ : ModVar → ModExpr} (h : m.Flexible)
    (hσ : ∀ n, (σ (.flex n)).Flexible) : (m.subst σ).Flexible := by
  induction m <;> simp_all [ModExpr.Flexible, ModExpr.subst]
  obtain ⟨n, rfl⟩ := h
  exact hσ n

theorem TypeExpr.Flexible.subst {a : Ty} {σ : TypeVar → Ty} {μ : ModVar → ModExpr}
    (h : a.Flexible) (hσ : ∀ n, (σ (.flex n)).Flexible)
    (hμ : ∀ n, (μ (.flex n)).Flexible) : (a.subst σ μ).Flexible := by
  induction a <;> simp_all [TypeExpr.Flexible, TypeExpr.subst]
  · obtain ⟨n, rfl⟩ := h
    exact hσ n
  · exact h.2.subst hμ

theorem ModExpr.Flexible.foldConstants {m : ModExpr} (h : m.Flexible) :
    m.foldConstants.Flexible := by
  unfold ModExpr.foldConstants
  split
  · trivial
  · split <;> repeat' split
    all_goals simp_all [ModExpr.Flexible]

theorem ModExpr.Flexible.normalize {m : ModExpr} (h : m.Flexible) : m.normalize.Flexible := by
  induction m <;> simp only [ModExpr.normalize]
  all_goals first | exact h | apply Flexible.foldConstants
  all_goals simp_all [ModExpr.Flexible]

theorem TypeExpr.Flexible.normalize {a : Ty} (h : a.Flexible) : a.normalize.Flexible := by
  induction a <;> simp only [TypeExpr.normalize]
  all_goals try solve | simp_all [TypeExpr.Flexible]
  rename_i a m ih
  have ha := ih h.1
  have hm := h.2.normalize
  split
  · rename_i b k hk
    have hb : b.Flexible ∧ k.Flexible := by simpa only [hk, TypeExpr.Flexible] using ha
    exact ⟨hb.1, ModExpr.Flexible.normalize (And.intro hb.2 hm)⟩
  · split
    · exact ha
    · exact ⟨ha, hm⟩

theorem Constraint.Flexible.normalize {c : Constraint} (h : c.Flexible) : c.normalize.Flexible := by
  cases c <;> simp only [Constraint.normalize, Constraint.Flexible] at *
  all_goals aesop (add safe apply [TypeExpr.Flexible.normalize, ModExpr.Flexible.normalize])

theorem TypeExpr.Flexible.outer {a : Ty} (h : a.Flexible) :
    a.outer.1.Flexible ∧ a.outer.2.Flexible := by
  induction a <;> simp_all [TypeExpr.outer, TypeExpr.Flexible, ModExpr.Flexible, ModExpr.epsilon]

structure Substitution.Flexible (σ : Substitution) : Prop where
  types : ∀ n a, (n, a) ∈ σ.types → a.Flexible
  modes : ∀ n m, (n, m) ∈ σ.modes → m.Flexible

theorem Substitution.Flexible.type {σ : Substitution} (hσ : σ.Flexible) (n : Nat) :
    (σ.type (.flex n)).Flexible := by
  cases he : σ.types.lookup n
  · simp [Substitution.type, he, TypeExpr.Flexible]
  · obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
    simpa only [Substitution.type, he, Option.getD_some] using
      hσ.types n _ (by simp [hh])

theorem Substitution.Flexible.mode {σ : Substitution} (hσ : σ.Flexible) (n : Nat) :
    (σ.mode (.flex n)).Flexible := by
  cases he : σ.modes.lookup n
  · simp [Substitution.mode, he, ModExpr.Flexible]
  · obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
    simpa only [Substitution.mode, he, Option.getD_some] using
      hσ.modes n _ (by simp [hh])

theorem Substitution.Flexible.ty {σ : Substitution} (hσ : σ.Flexible) {a : Ty}
    (ha : a.Flexible) : (σ.ty a).Flexible := ha.subst hσ.type hσ.mode

theorem Substitution.Flexible.constraint {σ : Substitution} (hσ : σ.Flexible)
    {c : Constraint} (hc : c.Flexible) : (σ.constraint c).Flexible := by
  cases c <;> simp only [Substitution.constraint, Constraint.subst, Constraint.Flexible] at *
  case sub a b | equiv a b => exact ⟨hσ.ty hc.1, hσ.ty hc.2⟩
  case mode a b => exact ⟨hc.1.subst hσ.mode, hc.2.subst hσ.mode⟩
  case defined a => exact hc.subst hσ.mode
  case equal v a =>
    obtain ⟨⟨n, rfl⟩, ha⟩ := hc
    cases he : σ.types.lookup n <;> simp only [he]
    · exact ⟨⟨n, rfl⟩, hσ.ty ha⟩
    · have hn := hσ.type n
      simp only [Substitution.type, he, Option.getD_some] at hn
      exact ⟨hn, hσ.ty ha⟩

theorem Substitution.Flexible.bounds {σ : Substitution} (hσ : σ.Flexible)
    {cs : Bounds} (hc : cs.Flexible) : (σ.bounds cs).Flexible := by
  rintro _ hh
  obtain ⟨c, hm, rfl⟩ := List.mem_map.mp hh
  exact hσ.constraint (hc c hm)

theorem Substitution.flexible_empty : ({} : Substitution).Flexible := ⟨by simp, by simp⟩

theorem Substitution.flexible_singleType {n a} (ha : TypeExpr.Flexible a) :
    ({types := [(n, a)]} : Substitution).Flexible := by
  exact ⟨by simpa using ha, by simp⟩

theorem Substitution.Flexible.extendType {σ : Substitution} (hσ : σ.Flexible)
    {n a} (ha : TypeExpr.Flexible a) : (σ.extendType n a).Flexible := by
  refine ⟨?_, hσ.modes⟩
  intro k b hb
  simp only [Substitution.extendType, List.mem_cons, List.mem_map, List.mem_filter,
    Prod.exists, Prod.mk.injEq] at hb
  rcases hb with ⟨rfl, rfl⟩ | ⟨j, c, ⟨hc, _⟩, rfl, rfl⟩
  · exact ha
  · exact (Substitution.flexible_singleType ha).ty (hσ.types j c hc)

theorem TypeExpr.Flexible.wellFormedBounds {a : Ty} (ha : a.Flexible) :
    a.wellFormedBounds.Flexible := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, TypeExpr.Flexible,
    Constraint.Flexible]

end ModalityInference
