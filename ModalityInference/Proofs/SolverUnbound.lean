import ModalityInference.Proofs.SolverFresh

/-! Worklist entries contain no identifiers already eliminated by the saved substitution. -/
namespace ModalityInference

def Constraint.Unbound (σ : Substitution) (c : Constraint) : Prop :=
  ∀ n ∈ σ.types.map Prod.fst, .flex n ∉ c.typeVars

structure SolverState.Unbound (s : SolverState) : Prop where
  modes : s.substitution.modes = []
  pending : ∀ c ∈ s.pending, c.Unbound s.substitution
  bounds : ∀ c ∈ s.bounds, c.Unbound s.substitution
  seen : ∀ c ∈ s.seen, c.Unbound s.substitution

@[simp] theorem Constraint.normalize_typeVars (c : Constraint) : c.normalize.typeVars = c.typeVars := by
  cases c <;> simp [normalize, typeVars]

theorem Constraint.Unbound.normalize {σ : Substitution} {c : Constraint}
    (hc : c.Unbound σ) : c.normalize.Unbound σ := by
  simpa only [Unbound, Constraint.normalize_typeVars] using hc

theorem Constraint.modality_unbound {c : Constraint} (hc : c.IsModality) (σ : Substitution) :
    c.Unbound σ := by
  cases c <;> simp_all [IsModality, Unbound, typeVars]

theorem Constraint.Unbound.fixed {σ : Substitution} {c : Constraint}
    (hc : c.Unbound σ) (hm : σ.modes = []) : σ.constraint c = c := by
  cases c <;> simp only [Unbound, typeVars, Finset.mem_union, Finset.mem_insert,
    not_or, forall_and] at hc
  case sub a b => exact congrArg₂ Constraint.sub (σ.ty_fixed a hm hc.1) (σ.ty_fixed b hm hc.2)
  case equiv a b => exact congrArg₂ Constraint.equiv (σ.ty_fixed a hm hc.1) (σ.ty_fixed b hm hc.2)
  case mode a b => exact Constraint.modality_substitution (c := .mode a b) trivial hm
  case defined a => exact Constraint.modality_substitution (c := .defined a) trivial hm
  case equal v a =>
    cases v <;> simp only [Substitution.constraint, σ.ty_fixed a hm hc.2]
    case flex n =>
      cases he : σ.types.lookup n <;> try rfl
      obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
      exact False.elim (hc.1 n (by simp [hh]) rfl)

theorem Constraint.singleType_avoids (c : Constraint) (a : Ty) (n k : Nat)
    (ha : .flex k ∉ a.typeVars) (hc : k = n ∨ .flex k ∉ c.typeVars) :
    .flex k ∉ (({types := [(n, a)]} : Substitution).constraint c).typeVars := by
  cases c <;> simp only [Substitution.constraint, Constraint.subst, Constraint.typeVars] at *
  case equal v t =>
    cases v <;> simp_all [List.lookup_cons]
    case rigid => exact t.singleType_avoids a n k ha hc
    case flex j =>
      cases he : (j == n) <;> simp_all [beq_iff_eq]
      case false => exact ⟨by aesop, t.singleType_avoids a n k ha (by aesop)⟩
      case true => exact t.singleType_avoids a n k ha (by aesop)
  all_goals simp only [Finset.mem_union, not_or, Finset.notMem_empty, not_false_eq_true]
  case sub x y | equiv x y =>
    exact ⟨x.singleType_avoids a n k ha (by aesop), y.singleType_avoids a n k ha (by aesop)⟩

theorem Constraint.Unbound.singleType {σ : Substitution} {c : Constraint}
    (hc : c.Unbound σ) {n a} (hn : n ∉ σ.types.map Prod.fst)
    (ha : ∀ k ∈ n :: σ.types.map Prod.fst, .flex k ∉ a.typeVars) :
    (({types := [(n, a)]} : Substitution).constraint c).Unbound (σ.extendType n a) :=
  fun k hk =>
    let hk' : k ∈ n :: σ.types.map Prod.fst := by simpa only [σ.extendType_keys hn] using hk
    c.singleType_avoids a n k (ha k hk') ((List.mem_cons.mp hk').imp id (fun hh => hc k hh))

theorem Constraint.unbound_empty (c : Constraint) : c.Unbound {} := by simp [Unbound]

theorem Substitution.constraint_unbound {σ : Substitution} (hσ : σ.Acyclic) (c : Constraint) :
    (σ.constraint c).Unbound σ := by
  cases c <;> simp only [Constraint.Unbound, Substitution.constraint, Constraint.subst,
    Constraint.typeVars, Finset.mem_union, not_or, forall_and]
  case sub a b | equiv a b =>
    exact ⟨fun _ hk => σ.ty_avoids hσ hk a, fun _ hk => σ.ty_avoids hσ hk b⟩
  case mode | defined => simp
  case equal v a =>
    cases v <;> simp only [Finset.mem_insert, not_or, forall_and]
    case rigid => exact ⟨by simp, fun _ hk => σ.ty_avoids hσ hk a⟩
    case flex j =>
      cases he : σ.types.lookup j <;> simp only [Finset.mem_union,
        Finset.mem_insert, not_or, forall_and]
      all_goals exact ⟨fun k hk => by
        simpa [Substitution.type, he, TypeExpr.typeVars] using σ.type_avoids hσ hk (.flex j),
        fun _ hk => σ.ty_avoids hσ hk a⟩

theorem SolverState.Unbound.emit {s : SolverState} (hs : s.Unbound)
    (r : RewriteRule) {cs : Bounds} (hc : ∀ c ∈ cs, c.Unbound s.substitution) :
    (s.emit r cs).Unbound :=
  ⟨hs.modes, fun c hm => (List.mem_append.mp hm).elim (hc c) (hs.pending c), hs.bounds, hs.seen⟩

theorem SolverState.Unbound.retain {s : SolverState} (hs : s.Unbound)
    (r : RewriteRule) {c : Constraint} (hc : c.Unbound s.substitution) :
    (s.retain r c).Unbound := by
  unfold SolverState.retain
  split
  · exact ⟨hs.modes, hs.pending, hs.bounds, hs.seen⟩
  · exact ⟨hs.modes, hs.pending, fun d hd => (List.mem_cons.mp hd).elim
      (fun he => he ▸ hc) (hs.bounds d), hs.seen⟩

theorem SolverState.Unbound.advance {s : SolverState} (hs : s.Unbound)
    (hσ : s.substitution.Acyclic) {c rest seen} (hp : s.pending = c :: rest)
    (hv : seen ⊆ (s.substitution.constraint c).normalize :: s.seen) :
    {s with pending := rest, seen := seen}.Unbound :=
  ⟨hs.modes, fun d hd => hs.pending d (by simp [hp, hd]), hs.bounds,
    fun d hd => (List.mem_cons.mp (hv hd)).elim
      (fun he => he ▸ (s.substitution.constraint_unbound hσ c).normalize) (hs.seen d)⟩

theorem SolverState.Unbound.skeleton {s : SolverState} (hs : s.Unbound) (a : Ty) :
    (s.skeleton a).2.Unbound := by
  cases a <;> exact ⟨hs.modes, hs.pending, hs.bounds, hs.seen⟩

theorem SolverState.Fresh.skeleton_unbound {s : SolverState} (hs : s.Fresh)
    (hσ : s.substitution.Acyclic) {a : Ty} (ha : Shape a (s.skeleton a).1) :
    ∀ k ∈ s.substitution.types.map Prod.fst, .flex k ∉ (s.skeleton a).1.typeVars := by
  simpa only [hs.skeleton_fixed ha] using fun k hk =>
    s.substitution.ty_avoids hσ hk (s.skeleton a).1

theorem stepMode_unbound {s a b t} (hs : SolverState.Unbound s)
    (h : stepMode s a b = .success t) : t.Unbound := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals first
    | exact hs.emit _ (by simp [Constraint.Unbound, Constraint.typeVars])
    | exact hs.retain _ (by simp [Constraint.Unbound, Constraint.typeVars])
    | exact (hs.retain _ (by simp [Constraint.Unbound, Constraint.typeVars])).emit _
        (by simp [Constraint.Unbound, Constraint.typeVars])

theorem SolverState.Fresh.skeleton_unbound_of {s : SolverState} (hs : s.Fresh)
    (hσ : s.substitution.Acyclic) {a : Ty}
    (ha : ∀ k ∈ s.substitution.types.map Prod.fst, .flex k ∉ a.typeVars) :
    ∀ k ∈ s.substitution.types.map Prod.fst, .flex k ∉ (s.skeleton a).1.typeVars := by
  cases a <;> first
    | exact ha
    | exact hs.skeleton_unbound hσ (s.skeleton_shape (by simp) (by simp))

set_option maxHeartbeats 400000 in
theorem stepType_unbound {s a b t} (hs : SolverState.Unbound s) (hf : s.Fresh)
    (hσ : s.substitution.Acyclic) (hc : (Constraint.sub a b).Unbound s.substitution)
    (h : stepType s a b = .success t) : t.Unbound := by
  have ho : ∀ k ∈ s.substitution.types.map Prod.fst,
      .flex k ∉ a.outer.1.typeVars ∧ .flex k ∉ b.outer.1.typeVars := by
    simpa [Constraint.Unbound, Constraint.typeVars] using hc
  have hna := hf.skeleton_unbound_of hσ (fun k hk => (ho k hk).1)
  have hnb := hf.skeleton_unbound_of hσ (fun k hk => (ho k hk).2)
  simp only [stepType, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  case h_1.refl =>
    exact (hs.retain _ (by simpa [Constraint.Unbound, Constraint.typeVars, TypeExpr.typeVars]
      using ho)).emit _ (by simp [Constraint.Unbound, Constraint.typeVars])
  case h_2.isFalse.refl =>
    exact (hs.skeleton b.outer.1).emit _ (by
      simp_all [Constraint.Unbound, Constraint.typeVars, TypeExpr.typeVars,
        SolverState.skeleton_substitution, forall_and]
      tauto)
  case h_3.isFalse.refl =>
    exact (hs.skeleton a.outer.1).emit _ (by
      simp_all [Constraint.Unbound, Constraint.typeVars, TypeExpr.typeVars,
        SolverState.skeleton_substitution, forall_and]
      tauto)
  all_goals exact hs.emit _ (by
    simp_all [Constraint.Unbound, Constraint.typeVars, TypeExpr.typeVars, forall_and] <;> tauto)

theorem TypeExpr.wellFormedBounds_unbound (a : Ty) (σ : Substitution) :
    ∀ c ∈ a.wellFormedBounds, c.Unbound σ := by
  induction a <;> simp_all [wellFormedBounds, Constraint.Unbound, Constraint.typeVars, or_imp, forall_and] <;> tauto

theorem solverStep_unbound {s t} (hs : s.Unbound) (hf : s.Fresh)
    (hσ : s.substitution.Acyclic) (h : solverStep s = .success t) : t.Unbound := by
  have hnorm := fun c => (s.substitution.constraint_unbound hσ c).normalize
  simp only [solverStep, bind, pure, RunResult.bind] at h
  repeat' split at h
  case h_2 =>
    rename_i pending c rest hp hseen normalized a b he
    exact stepType_unbound
      (s := {s with pending := rest, seen := (s.substitution.constraint c).normalize :: s.seen})
      (hs.advance hσ hp (by simp)) (hf.advance hp (by simp)) hσ (he ▸ hnorm c) h
  all_goals first
    | exact stepMode_unbound (hs.advance hσ ‹s.pending = _ :: _› (by simp)) h
    | skip
  all_goals cases h
  case h_2.isFalse.isFalse.refl =>
    rename_i pending c rest hp hseen normalized a v n he hsame hoccurs
    obtain ⟨hn, ha⟩ := s.substitution.normalized_equal_fresh hσ he
    refine ⟨hs.modes, ?_, by simp, by simp⟩
    simp only [Substitution.bounds, List.forall_mem_map]
    suffices hbase : ∀ d ∈ rest ++ s.bounds ++ a.wellFormedBounds, d.Unbound s.substitution from
      fun d hd => (hbase d hd).singleType hn (by
        simpa using And.intro (show .flex n ∉ a.typeVars by simpa using hoccurs) ha)
    simp only [List.mem_append, or_imp, forall_and]
    exact ⟨⟨fun d hd => hs.pending d (by simp [hp, hd]), hs.bounds⟩,
      a.wellFormedBounds_unbound s.substitution⟩
  all_goals try exact hs
  case h_1.refl =>
    rename_i pending c rest hp hseen normalized a b he
    have hc : (Constraint.equiv a b).Unbound s.substitution := he ▸ hnorm c
    exact (hs.advance hσ hp (by simp)).emit _ (by
      simpa [Constraint.Unbound, Constraint.typeVars, TypeExpr.typeVars,
        forall_and, and_assoc, and_left_comm, and_comm] using hc)
  case h_2.isFalse.isTrue.refl =>
    rename_i pending c rest hp hseen normalized a v n he hsame hoccurs
    have hc : (Constraint.equal (.flex n) a).Unbound s.substitution := he ▸ hnorm c
    exact (hs.advance hσ hp (by simp)).emit _ (by
      simpa [Constraint.Unbound, Constraint.typeVars, TypeExpr.typeVars,
        forall_and, and_assoc, and_left_comm, and_comm] using hc)
  all_goals first
    | exact hs.advance hσ ‹s.pending = _ :: _› (by simp)
    | exact (hs.advance hσ ‹s.pending = _ :: _› (by simp)).emit _
        (by simp [Constraint.Unbound, Constraint.typeVars])
    | exact (hs.advance hσ ‹s.pending = _ :: _› (by simp)).retain _
        (by simp_all [Constraint.Unbound, Constraint.typeVars])

theorem runWorklist_unbound {fuel s t} (hs : s.Unbound) (hf : s.Fresh)
    (hσ : s.substitution.Acyclic) (h : runWorklist fuel s = .success t) : t.Unbound := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · exact RunResult.success.inj h ▸ hs
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_unbound hs hf hσ ht) (solverStep_fresh hf ht) (solverStep_acyclic hσ ht) h

theorem runSolver_worklist {fuel s t} (h : runSolver fuel s = .success t) :
    runWorklist fuel s = .success t := by
  simpa only [runSolver, (s.substitution.checkAcyclic_iff).mpr (runSolver_input_acyclic h),
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind, RunResult.bind,
    runSolver_shape_precheck h] using h

theorem runSolver_unbound {fuel s t} (hs : s.Unbound) (hf : s.Fresh)
    (h : runSolver fuel s = .success t) : t.Unbound :=
  runWorklist_unbound hs hf (runSolver_input_acyclic h) (runSolver_worklist h)

theorem Substitution.bounds_fixed {σ : Substitution} {cs : Bounds}
    (hm : σ.modes = []) (hc : ∀ c ∈ cs, c.Unbound σ) : σ.bounds cs = cs :=
  (List.map_congr_left (g := id) (fun c hh => (hc c hh).fixed hm)).trans (List.map_id cs)

theorem SolverState.Unbound.fixed {s : SolverState} (hs : s.Unbound) :
    s.substitution.bounds s.pending = s.pending ∧ s.substitution.bounds s.bounds = s.bounds ∧
      s.substitution.bounds s.seen = s.seen :=
  ⟨Substitution.bounds_fixed hs.modes hs.pending, Substitution.bounds_fixed hs.modes hs.bounds,
    Substitution.bounds_fixed hs.modes hs.seen⟩

theorem solveFrom_unbound {fuel nt nm cs result} (hc : cs.Bounded nt nm)
    (h : solveFrom fuel nt nm cs = .success result) :
    result.substitution.modes = [] ∧ ∀ c ∈ result.bounds, c.Unbound result.substitution := by
  unfold solveFrom at h
  cases hr : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hr, bind, RunResult.bind] at h
  split at h <;> cases h
  have ht := runSolver_unbound (s := {pending := cs, nextType := nt, nextMode := nm})
    ⟨rfl, fun c _ => c.unbound_empty, by simp, by simp⟩
    ⟨hc, Bounds.bounded_nil _ _, Bounds.bounded_nil _ _, Substitution.bounded_empty _ _⟩ hr
  exact ⟨ht.modes, ht.bounds⟩

theorem solve_unbound {fuel cs result} (h : solve fuel cs = .success result) :
    result.substitution.modes = [] ∧ ∀ c ∈ result.bounds, c.Unbound result.substitution :=
  solveFrom_unbound cs.bounded_freshIndices h

theorem solve_bounds_fixed {fuel cs result} (h : solve fuel cs = .success result) :
    result.substitution.bounds result.bounds = result.bounds :=
  Substitution.bounds_fixed (solve_unbound h).1 (solve_unbound h).2

end ModalityInference
