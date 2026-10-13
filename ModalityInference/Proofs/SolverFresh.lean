import ModalityInference.Proofs.BoundedSupport
import ModalityInference.Proofs.ModeSeen
import ModalityInference.Proofs.SubsumptionScope

/-! Fresh identifier supplies are preserved through the complete solver. -/
namespace ModalityInference

structure SolverState.Fresh (s : SolverState) : Prop where
  pending : s.pending.Bounded s.nextType s.nextMode
  bounds : s.bounds.Bounded s.nextType s.nextMode
  seen : s.seen.Bounded s.nextType s.nextMode
  substitution : s.substitution.Bounded s.nextType s.nextMode

theorem SolverState.Fresh.emit {s : SolverState} (hs : s.Fresh)
    (r : RewriteRule) {cs : Bounds} (hc : cs.Bounded s.nextType s.nextMode) :
    (s.emit r cs).Fresh :=
  ⟨Bounds.bounded_append.mpr ⟨hc, hs.pending⟩, hs.bounds, hs.seen, hs.substitution⟩

theorem SolverState.Fresh.retain {s : SolverState} (hs : s.Fresh)
    (r : RewriteRule) {c : Constraint} (hc : c.Bounded s.nextType s.nextMode) :
    (s.retain r c).Fresh := by
  unfold SolverState.retain
  split
  · exact ⟨hs.pending, hs.bounds, hs.seen, hs.substitution⟩
  · exact ⟨hs.pending, Bounds.bounded_cons.mpr ⟨hc, hs.bounds⟩, hs.seen, hs.substitution⟩

theorem SolverState.skeleton_counters (s : SolverState) (a : Ty) :
    s.nextType ≤ (s.skeleton a).2.nextType ∧ s.nextMode ≤ (s.skeleton a).2.nextMode := by
  cases a <;> simp [SolverState.skeleton, SolverState.freshType, SolverState.freshMode]
  all_goals omega

theorem SolverState.skeleton_bounded {s : SolverState} {a : Ty}
    (ha : a.Bounded s.nextType s.nextMode) :
    (s.skeleton a).1.Bounded (s.skeleton a).2.nextType (s.skeleton a).2.nextMode := by
  cases a <;> simp only [SolverState.skeleton, SolverState.freshType, SolverState.freshMode]
  all_goals first
    | exact ⟨ha.mono (by omega) (by omega), by simp [ModExpr.Bounded, ModVar.index]⟩
    | simp [TypeExpr.Bounded, ModExpr.Bounded, TypeVar.index, ModVar.index]
  all_goals omega

theorem SolverState.Fresh.skeleton {s : SolverState} (hs : s.Fresh) (a : Ty) :
    (s.skeleton a).2.Fresh := by
  obtain ⟨ht, hm⟩ := s.skeleton_counters a
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(s.skeleton_frame a).1]
    exact hs.pending.mono ht hm
  · rw [(s.skeleton_frame a).2.1]
    exact hs.bounds.mono ht hm
  · rw [(s.skeleton_frame a).2.2]
    exact hs.seen.mono ht hm
  · rw [s.skeleton_substitution]
    exact hs.substitution.mono ht hm

theorem recordModeBound_fresh {s : SolverState} (hs : s.Fresh)
    {a b : ModExpr} (ha : a.Bounded s.nextMode) (hb : b.Bounded s.nextMode) :
    (recordModeBound s a b).Fresh := hs.retain .modeBound (And.intro ha hb)

theorem stepMode_fresh {s a b t} (hs : SolverState.Fresh s)
    (ha : ModExpr.Bounded s.nextMode a) (hb : b.Bounded s.nextMode)
    (h : stepMode s a b = .success t) : t.Fresh := by
  unfold stepMode at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals repeat' first
    | apply recordModeBound_fresh
    | apply SolverState.Fresh.emit
    | apply SolverState.Fresh.retain
  all_goals first | exact hs | simp_all [Constraint.Bounded, ModExpr.Bounded,
    recordModeBound, SolverState.retain]

theorem stepType_fresh {s a b t} (hs : SolverState.Fresh s)
    (ha : TypeExpr.Bounded s.nextType s.nextMode a) (hb : b.Bounded s.nextType s.nextMode)
    (h : stepType s a b = .success t) : t.Fresh := by
  have hla := ha.outer
  have hrb := hb.outer
  have hl := hla.2.normalize
  have hr := hrb.2.normalize
  unfold stepType at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals try solve
    | exact hs.emit _ (by simp_all [Constraint.Bounded, TypeExpr.Bounded,
        ModExpr.Bounded, ModExpr.top])
    | exact (hs.retain _ (by simp_all [Constraint.Bounded, TypeExpr.Bounded])).emit _
        (by simp_all [Constraint.Bounded, SolverState.retain])
  all_goals
    have hcount := Eq.mp (congrArg (fun p : Ty × SolverState =>
      s.nextType ≤ p.2.nextType ∧ s.nextMode ≤ p.2.nextMode) ‹s.skeleton _ = (_, _)›)
      (s.skeleton_counters _)
    have hshape := Eq.mp (congrArg (fun p : Ty × SolverState =>
      p.1.Bounded p.2.nextType p.2.nextMode) ‹s.skeleton _ = (_, _)›)
      (SolverState.skeleton_bounded (s := s) (by simp_all))
    have hf := Eq.mp (congrArg (fun p : Ty × SolverState => p.2.Fresh)
      ‹s.skeleton _ = (_, _)›) (hs.skeleton _)
    have hla' := hla.1.mono hcount.1 hcount.2
    have hrb' := hrb.1.mono hcount.1 hcount.2
    have hl' := hl.mono hcount.2
    have hr' := hr.mono hcount.2
    exact hf.emit _ (by simp_all [Constraint.Bounded, TypeExpr.Bounded, TypeVar.index])

theorem SolverState.Fresh.normalized_head {s : SolverState} (hs : s.Fresh)
    {c rest} (hp : s.pending = c :: rest) :
    (s.substitution.constraint c).normalize.Bounded s.nextType s.nextMode :=
  (hs.substitution.constraint (Bounds.bounded_cons.mp (hp ▸ hs.pending)).1).normalize

theorem SolverState.Fresh.advance {s : SolverState} (hs : s.Fresh)
    {c rest seen} (hp : s.pending = c :: rest)
    (hv : seen ⊆ (s.substitution.constraint c).normalize :: s.seen) :
    {s with pending := rest, seen := seen}.Fresh := by
  refine ⟨(Bounds.bounded_cons.mp (hp ▸ hs.pending)).2, hs.bounds, ?_, hs.substitution⟩
  intro d hd
  rcases List.mem_cons.mp (hv hd) with rfl | hd
  · exact hs.normalized_head hp
  · exact hs.seen d hd

theorem solverStep_fresh {s t} (hs : s.Fresh) (h : solverStep s = .success t) : t.Fresh := by
  unfold solverStep at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq] at h
  all_goals try have hc := hs.normalized_head ‹s.pending = _ :: _›
  all_goals first
    | exact stepType_fresh (hs.advance ‹s.pending = _ :: _› (by simp))
        (by simp_all [Constraint.Bounded]) (by simp_all [Constraint.Bounded]) h
    | exact stepMode_fresh (hs.advance ‹s.pending = _ :: _› (by simp))
        (by simp_all [Constraint.Bounded]) (by simp_all [Constraint.Bounded]) h
    | skip
  all_goals cases h
  all_goals try exact hs
  all_goals try solve
    | exact hs.advance ‹s.pending = _ :: _› (by simp)
    | exact (hs.advance ‹s.pending = _ :: _› (by simp)).emit _
        (by simp_all [Constraint.Bounded, TypeExpr.Bounded])
    | exact (hs.advance ‹s.pending = _ :: _› (by simp)).retain _
        (by simp_all [Constraint.Bounded])
  simp only [‹(s.substitution.constraint _).normalize = .equal _ _›,
    Constraint.Bounded, TypeVar.index] at hc
  refine ⟨(Substitution.bounded_singleType hc.1 hc.2).bounds ?_, Bounds.bounded_nil _ _,
    Bounds.bounded_nil _ _, hs.substitution.extendType hc.1 hc.2⟩
  exact Bounds.bounded_append.mpr ⟨Bounds.bounded_append.mpr
    ⟨(Bounds.bounded_cons.mp (‹s.pending = _ :: _› ▸ hs.pending)).2, hs.bounds⟩,
    hc.2.wellFormedBounds⟩

theorem runWorklist_fresh {fuel s t} (hs : s.Fresh)
    (h : runWorklist fuel s = .success t) : t.Fresh := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h
      exact hs
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_fresh hs ht) h

theorem runSolver_fresh {fuel s t} (hs : s.Fresh)
    (h : runSolver fuel s = .success t) : t.Fresh := by
  have hσ := runSolver_input_acyclic h
  simp only [runSolver, (s.substitution.checkAcyclic_iff).mpr hσ, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, bind, RunResult.bind] at h
  split at h <;> first | exact runWorklist_fresh hs h | cases h

theorem solveFrom_fresh {fuel nt nm cs result} (hc : cs.Bounded nt nm)
    (h : solveFrom fuel nt nm cs = .success result) :
    result.bounds.Bounded result.nextType result.nextMode ∧
      result.substitution.Bounded result.nextType result.nextMode := by
  unfold solveFrom at h
  cases hs : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hs, bind, RunResult.bind] at h
  split at h <;> cases h
  have hf := runSolver_fresh
    ⟨hc, Bounds.bounded_nil _ _, Bounds.bounded_nil _ _, Substitution.bounded_empty _ _⟩ hs
  exact ⟨hf.bounds, hf.substitution⟩

theorem Bounds.bounded_freshIndices (cs : Bounds) :
    cs.Bounded cs.freshTypeIndex cs.freshModeIndex :=
  (cs.bounded_iff _ _).mpr
    ⟨fun _ hv => Bounds.lt_freshTypeIndex (by simpa using hv),
      fun _ hv => Bounds.lt_freshModeIndex (by simpa using hv)⟩

theorem solve_fresh {fuel cs result} (h : solve fuel cs = .success result) :
    result.bounds.Bounded result.nextType result.nextMode ∧
      result.substitution.Bounded result.nextType result.nextMode :=
  solveFrom_fresh cs.bounded_freshIndices h

theorem TypeExpr.outer_not_modal (a : Ty) : ∀ b m, a.outer.1 ≠ .modal b m := by
  induction a <;> simp_all [TypeExpr.outer]

theorem SolverState.skeleton_shape (s : SolverState) {a : Ty}
    (hv : ∀ v, a ≠ .var v) (hm : ∀ b m, a ≠ .modal b m) : Shape a (s.skeleton a).1 := by
  cases a <;> simp_all
  all_goals constructor
  all_goals change s.nextType ≠ s.nextType + 1
  all_goals omega

theorem SolverState.skeleton_identifiers (s : SolverState) {a : Ty}
    (h : Shape a (s.skeleton a).1) :
    (∀ v ∈ (s.skeleton a).1.typeVars, s.nextType ≤ v.index) ∧
      (∀ v ∈ (s.skeleton a).1.modVars, s.nextMode ≤ v.index) := by
  cases a <;> try cases h
  all_goals simp [SolverState.skeleton, SolverState.freshType, SolverState.freshMode,
    TypeExpr.typeVars, TypeExpr.modVars, ModExpr.vars, TypeVar.index, ModVar.index, or_imp, forall_and]

theorem SolverState.skeleton_mode_mem (s : SolverState) (a : Ty) :
    .flex s.nextMode ∈ (s.skeleton a).1.modVars := by
  cases a <;> simp [SolverState.skeleton, SolverState.freshType, SolverState.freshMode,
    TypeExpr.modVars, ModExpr.vars]

theorem SolverState.skeleton_normalize (s : SolverState) {a : Ty}
    (h : Shape a (s.skeleton a).1) : (s.skeleton a).1.normalize = (s.skeleton a).1 := by
  cases a <;> try cases h
  all_goals rfl

theorem SolverState.Fresh.config_bounded {s : SolverState} (hs : s.Fresh) :
    (∀ v ∈ (⟨s.pending, s.bounds, s.substitution⟩ : RewriteConfig).typeVars, v.index < s.nextType) ∧
      (∀ v ∈ (⟨s.pending, s.bounds, s.substitution⟩ : RewriteConfig).modVars, v.index < s.nextMode) := by
  have hb := ((s.pending ++ s.bounds).bounded_iff _ _).mp
    (Bounds.bounded_append.mpr ⟨hs.pending, hs.bounds⟩)
  constructor <;> intro v hv
  all_goals simp only [RewriteConfig.typeVars, RewriteConfig.modVars, RewriteConfig.constraints,
    Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_cons, List.mem_append,
    TypeExpr.mem_typeVariables, TypeExpr.mem_modeVariables, ModExpr.mem_freeVariables] at hv
  case left =>
    rcases hv with hv | ⟨⟨n, a⟩, ha, hv⟩
    · exact hb.1 v hv
    · rcases hv with rfl | hv
      · exact (hs.substitution.types n a ha).1
      · exact ((a.bounded_iff _ _).mp (hs.substitution.types n a ha).2).1 v hv
  case right =>
    rcases hv with hv | ⟨⟨n, a⟩, ha, hv⟩ | ⟨⟨n, m⟩, hm, hv⟩
    · exact hb.2 v hv
    · exact ((a.bounded_iff _ _).mp (hs.substitution.types n a ha).2).2 v hv
    · rcases hv with rfl | hv
      · exact (hs.substitution.modes n m hm).1
      · exact (m.bounded_iff _).mp (hs.substitution.modes n m hm).2 v hv

theorem SolverState.Fresh.skeleton_freshFor {s : SolverState} (hs : s.Fresh)
    {a old} (ha : Shape a (s.skeleton a).1) (hc : old.Bounded s.nextType s.nextMode) :
    FreshFor old (s.skeleton a).1 ⟨s.pending, s.bounds, s.substitution⟩ := by
  have hnew := s.skeleton_identifiers ha
  have hconfig := hs.config_bounded
  have hold := (old.bounded_iff _ _).mp hc
  constructor
  · intro v hv hh
    have hlt := (Finset.mem_union.mp hh).elim (hold.1 v) (hconfig.1 v)
    have hle := hnew.1 v hv
    omega
  · intro v hv hh
    have hlt := (Finset.mem_union.mp hh).elim (hold.2 v) (hconfig.2 v)
    have hle := hnew.2 v hv
    omega

theorem SolverState.Fresh.skeleton_equal_not_seen {s : SolverState} (hs : s.Fresh)
    (v : TypeVar) (a : Ty) : .equal v (s.skeleton a).1 ∉ s.seen := by
  intro hc
  have hm := ((Constraint.equal v (s.skeleton a).1).bounded_iff _ _).mp (hs.seen _ hc)
  have hh := hm.2 (.flex s.nextMode) (s.skeleton_mode_mem a)
  simp [ModVar.index] at hh

theorem SolverState.Fresh.skeleton_fixed {s : SolverState} (hs : s.Fresh) {a : Ty}
    (ha : Shape a (s.skeleton a).1) :
    s.substitution.ty (s.skeleton a).1 = (s.skeleton a).1 := by
  have ht := hs.substitution.type_above (n := s.nextType) (by omega)
  have ht' := hs.substitution.type_above (n := s.nextType + 1) (by omega)
  have hm := hs.substitution.mode_above (n := s.nextMode) (by omega)
  cases a <;> try cases ha
  all_goals simp [SolverState.skeleton, SolverState.freshType, SolverState.freshMode,
    Substitution.ty, TypeExpr.subst, ModExpr.subst, ht, ht', hm]

theorem SolverState.Fresh.skeleton_equal_normalized {s : SolverState} (hs : s.Fresh)
    {a n} (ha : Shape a (s.skeleton a).1) (hn : n ∉ s.substitution.types.map Prod.fst) :
    (s.substitution.constraint (.equal (.flex n) (s.skeleton a).1)).normalize =
      .equal (.flex n) (s.skeleton a).1 := by
  have he : s.substitution.types.lookup n = none := by
    cases he : s.substitution.types.lookup n
    · rfl
    · obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
      exact False.elim (hn (by simp [hh]))
  simp only [Substitution.constraint, he, hs.skeleton_fixed ha, Constraint.normalize,
    s.skeleton_normalize ha]

theorem SolverState.Fresh.skeleton_eliminated {s : SolverState} (hs : s.Fresh)
    {a n} (ha : Shape a (s.skeleton a).1) (hn : n < s.nextType)
    (hkey : n ∉ s.substitution.types.map Prod.fst) (old : Constraint) :
    let shape := (s.skeleton a).1
    let u := (s.skeleton a).2
    let one : Substitution := {types := [(n, shape)]}
    solverStep (u.emit .expand [.equal (.flex n) shape, old]) =
      .success {u with
        pending := one.bounds ((old :: u.pending) ++ u.bounds ++ shape.wellFormedBounds)
        bounds := []
        seen := []
        substitution := u.substitution.extendType n shape
        trace := .substitute :: .expand :: u.trace} := by
  dsimp only
  have hcache : .equal (.flex n) (s.skeleton a).1 ∉ (s.skeleton a).2.seen := by
    simpa only [(s.skeleton_frame a).2.2] using hs.skeleton_equal_not_seen (.flex n) a
  have hneq : (s.skeleton a).1 ≠ .var (.flex n) := by
    cases a <;> simp [SolverState.skeleton, SolverState.freshType, SolverState.freshMode]
  have hocc : .flex n ∉ (s.skeleton a).1.typeVars := by
    intro hh
    have hle := (s.skeleton_identifiers ha).1 (.flex n) hh
    change s.nextType ≤ n at hle
    omega
  simp [solverStep, SolverState.emit, SolverState.skeleton_substitution,
    hs.skeleton_equal_normalized ha hkey, hcache, beq_iff_eq, hneq,
    TypeExpr.mem_typeVariables, hocc, bind, pure, RunResult.bind]

theorem SolverState.Fresh.skeleton_expandLeft {s : SolverState} (hs : s.Fresh)
    {a n l r} (ha : Shape a (s.skeleton a).1)
    (hc : (Constraint.sub (.modal (.var (.flex n)) l) (.modal a r)).Bounded s.nextType s.nextMode) :
    let c := Constraint.sub (.modal (.var (.flex n)) l) (.modal a r)
    Rewrites ⟨c :: s.pending, s.bounds, s.substitution⟩
      ⟨.equal (.flex n) (s.skeleton a).1 :: c :: s.pending, s.bounds, s.substitution⟩ :=
  Rewrites.expandLeft ha (hs.skeleton_freshFor ha hc)

theorem SolverState.Fresh.skeleton_expandRight {s : SolverState} (hs : s.Fresh)
    {a n l r} (ha : Shape a (s.skeleton a).1)
    (hc : (Constraint.sub (.modal a l) (.modal (.var (.flex n)) r)).Bounded s.nextType s.nextMode) :
    let c := Constraint.sub (.modal a l) (.modal (.var (.flex n)) r)
    Rewrites ⟨c :: s.pending, s.bounds, s.substitution⟩
      ⟨.equal (.flex n) (s.skeleton a).1 :: c :: s.pending, s.bounds, s.substitution⟩ :=
  Rewrites.expandRight ha (hs.skeleton_freshFor ha hc)

@[simp] theorem TypeExpr.outer_typeVars (a : Ty) : a.outer.1.typeVars = a.typeVars := by
  induction a <;> simp_all [TypeExpr.outer, TypeExpr.typeVars]

theorem TypeExpr.outer_var_mem {a : Ty} {v : TypeVar} (h : a.outer.1 = .var v) :
    v ∈ a.typeVars := by
  rw [← a.outer_typeVars, h]
  simp [TypeExpr.typeVars]

theorem Substitution.normalized_sub_fresh {σ : Substitution} (hσ : σ.Acyclic)
    {c a b} (h : (σ.constraint c).normalize = .sub a b) :
    ∀ k ∈ σ.types.map Prod.fst, .flex k ∉ a.typeVars ∧ .flex k ∉ b.typeVars := by
  cases c <;> simp only [Substitution.constraint, Constraint.subst, Constraint.normalize] at h
  all_goals try contradiction
  case sub x y =>
    cases h
    intro k hk
    simpa only [TypeExpr.normalize_typeVars] using
      And.intro (σ.ty_avoids hσ hk x) (σ.ty_avoids hσ hk y)
  case equal v x =>
    cases v <;> simp only [reduceCtorEq] at h
    rename_i n
    cases he : σ.types.lookup n <;> simp [he] at h

theorem Substitution.normalized_sub_left_fresh {σ : Substitution} (hσ : σ.Acyclic)
    {c a b n} (h : (σ.constraint c).normalize = .sub a b)
    (ha : a.outer.1 = .var (.flex n)) : n ∉ σ.types.map Prod.fst :=
  fun hn => (σ.normalized_sub_fresh hσ h n hn).1 (TypeExpr.outer_var_mem ha)

theorem Substitution.normalized_sub_right_fresh {σ : Substitution} (hσ : σ.Acyclic)
    {c a b n} (h : (σ.constraint c).normalize = .sub a b)
    (hb : b.outer.1 = .var (.flex n)) : n ∉ σ.types.map Prod.fst :=
  fun hn => (σ.normalized_sub_fresh hσ h n hn).2 (TypeExpr.outer_var_mem hb)

end ModalityInference
