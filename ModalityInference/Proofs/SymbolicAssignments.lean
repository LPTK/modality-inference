import ModalityInference.Proofs.SymbolicReduction
import ModalityInference.Proofs.SolverFresh

namespace ModalityInference.SymbolicSolver

def putType (σ : Substitution) (n : Nat) (a : Ty) : Substitution :=
  {σ with types := (n, a) :: σ.types}

def putMode (σ : Substitution) (n : Nat) (m : ModExpr) : Substitution :=
  {σ with modes := (n, m) :: σ.modes}

@[simp] theorem putType_type (σ : Substitution) (n : Nat) (a : Ty) (v : TypeVar) :
    (putType σ n a).type v = if v = .flex n then a else σ.type v := by
  cases v with
  | rigid k => rfl
  | flex k =>
    by_cases h : k = n
    · simp [putType, Substitution.type, h]
    · simp [putType, Substitution.type, List.lookup_cons, h, beq_eq_false_iff_ne.mpr h]

@[simp] theorem putType_mode (σ : Substitution) (n : Nat) (a : Ty) (v : ModVar) :
    (putType σ n a).mode v = σ.mode v := rfl

@[simp] theorem putMode_type (σ : Substitution) (n : Nat) (m : ModExpr) (v : TypeVar) :
    (putMode σ n m).type v = σ.type v := rfl

@[simp] theorem putMode_mode (σ : Substitution) (n : Nat) (m : ModExpr) (v : ModVar) :
    (putMode σ n m).mode v = if v = .flex n then m else σ.mode v := by
  cases v with
  | rigid k => rfl
  | flex k =>
    by_cases h : k = n
    · simp [putMode, Substitution.mode, h]
    · simp [putMode, Substitution.mode, List.lookup_cons, h, beq_eq_false_iff_ne.mpr h]

theorem putType_wellFormed {σ Δ n a} (hσ : σ.WellFormedUnder Δ)
    (ha : a.DefinedUnder Δ) : (putType σ n a).WellFormedUnder Δ := by
  refine ⟨fun v => ?_, hσ.modes⟩
  simp only [putType_type]
  split <;> first | exact ha | exact hσ.types v

theorem putMode_wellFormed {σ Δ n m} (hσ : σ.WellFormedUnder Δ)
    (hm : Entails Δ (.defined m)) : (putMode σ n m).WellFormedUnder Δ := by
  refine ⟨hσ.types, fun v => ?_⟩
  simp only [putMode_mode]
  split <;> first | exact hm | exact hσ.modes v

def AgreesBelow (σ τ : Substitution) (nt nm : Nat) : Prop :=
  (∀ v, v.index < nt → σ.type v = τ.type v) ∧
  (∀ v, v.index < nm → σ.mode v = τ.mode v)

theorem AgreesBelow.refl (σ : Substitution) (nt nm : Nat) : AgreesBelow σ σ nt nm :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem AgreesBelow.ty {σ τ nt nm} (h : AgreesBelow σ τ nt nm) {a : Ty}
    (ha : a.Bounded nt nm) : σ.ty a = τ.ty a :=
  a.subst_congr (fun v hv => h.1 v (((a.bounded_iff nt nm).mp ha).1 v hv))
    (fun v hv => h.2 v (((a.bounded_iff nt nm).mp ha).2 v hv))

theorem AgreesBelow.mode {σ τ nt nm} (h : AgreesBelow σ τ nt nm) {m : ModExpr}
    (hm : m.Bounded nm) : m.subst σ.mode = m.subst τ.mode :=
  m.subst_congr (fun v hv => h.2 v ((m.bounded_iff nm).mp hm v hv))

theorem AgreesBelow.constraint {σ τ nt nm} (h : AgreesBelow σ τ nt nm)
    {c : Constraint} (hc : c.Bounded nt nm) {Δ} :
    Entails Δ (σ.constraint c) ↔ Entails Δ (τ.constraint c) := by
  rw [σ.constraint_subst_entails, τ.constraint_subst_entails]
  rw [c.subst_congr (fun v hv => h.1 v (((c.bounded_iff nt nm).mp hc).1 v hv))
    (fun v hv => h.2 v (((c.bounded_iff nt nm).mp hc).2 v hv))]

theorem AgreesBelow.solution {σ τ nt nm} (h : AgreesBelow σ τ nt nm)
    {cs : Bounds} (hc : cs.Bounded nt nm) {Δ} (hs : Solution cs Δ τ) : Solution cs Δ σ := by
  intro c hc'
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc'
  exact (h.constraint (hc d hd)).mpr (hs _ (List.mem_map.mpr ⟨d, hd, rfl⟩))

theorem tag_outer (a : Ty) : SymbolicInversion.tag a.outer.1 = SymbolicInversion.tag a := by
  simp only [SymbolicInversion.tag, TypeExpr.outer_comparisonShape]

theorem skeleton_assign {Δ : Bounds} {s : SolverState} {a target : Ty} {σ : Substitution}
    (hσ : σ.WellFormedUnder Δ) (ht : target.DefinedUnder Δ)
    (ha : ∀ v, a ≠ .var v) (hm : ∀ t m, a ≠ .modal t m)
    (hh : SymbolicInversion.tag target = SymbolicInversion.tag a) :
    ∃ τ : Substitution, τ.WellFormedUnder Δ ∧
      τ.ty (s.skeleton a).1 = .modal target.outer.1 target.outer.2 ∧
      AgreesBelow τ σ s.nextType s.nextMode := by
  have hd := TypeExpr.definedUnder_modal.mp ((target.outer_definedUnder Δ).mpr ht)
  have ho := target.outer_not_modal
  have hh' := (tag_outer target).trans hh
  cases a <;> try solve | exact False.elim (ha _ rfl) | exact False.elim (hm _ _ rfl)
  all_goals cases he : target.outer.1 <;>
    simp only [he, SymbolicInversion.tag, ComparisonShape.ofTy,
      ComparisonStructuralProjection.rootTag] at hh'
  all_goals try contradiction
  all_goals try solve | exact False.elim (ho _ _ he)
  case unit.unit | credit.credit =>
    refine ⟨putMode σ s.nextMode target.outer.2, putMode_wellFormed hσ hd.2, ?_, ?_⟩
    · simp [SolverState.skeleton, SolverState.freshMode, Substitution.ty, TypeExpr.subst,
        ModExpr.subst]
    · refine ⟨fun _ _ => rfl, fun v hv => ?_⟩
      rw [putMode_mode, if_neg]
      intro h
      subst v
      exact Nat.lt_irrefl _ hv
  case prod.prod left right x y | sum.sum left right x y | fn.fn left right x y =>
    have hxy : x.DefinedUnder Δ ∧ y.DefinedUnder Δ := by
      simpa only [he, TypeExpr.definedUnder_prod, TypeExpr.definedUnder_sum,
        TypeExpr.definedUnder_fn] using hd.1
    let τ := putMode (putType (putType σ s.nextType x) (s.nextType + 1) y)
      s.nextMode target.outer.2
    refine ⟨τ, putMode_wellFormed
      (putType_wellFormed (putType_wellFormed hσ hxy.1) hxy.2) hd.2, ?_, ?_⟩
    · simp [τ, SolverState.skeleton, SolverState.freshMode, SolverState.freshType,
        Substitution.ty, TypeExpr.subst, ModExpr.subst]
    · constructor
      · intro v hv
        have h0 : v ≠ .flex s.nextType := by intro h; subst v; exact Nat.lt_irrefl _ hv
        have h1 : v ≠ .flex (s.nextType + 1) := by
          intro h
          subst v
          simp only [TypeVar.index] at hv
          omega
        simp [τ, h0, h1]
      · intro v hv
        have h0 : v ≠ .flex s.nextMode := by intro h; subst v; exact Nat.lt_irrefl _ hv
        simp [τ, h0]

end ModalityInference.SymbolicSolver
