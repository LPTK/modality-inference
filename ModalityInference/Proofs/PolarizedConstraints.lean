import ModalityInference.PolarizedConstraints
import ModalityInference.Proofs.Generation
import ModalityInference.ModeConsistency
import ModalityInference.Proofs.HornPropagation

namespace ModalityInference

namespace BoolExpr.IsHorn

theorem all {xs : List BoolExpr} (h : ∀ x ∈ xs, x.IsHorn) : (BoolExpr.all xs).IsHorn := by
  induction xs with
  | nil => exact .const true
  | cons x xs ih => exact .and (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

end BoolExpr.IsHorn

namespace ModExpr

theorem IsMonomial.isPolar {m : ModExpr} (h : m.IsMonomial) (p : Polarity) : m.IsPolar p := by
  induction m generalizing p <;> simp_all [IsMonomial, IsPolar]

theorem IsMonomial.project_both {m : ModExpr} (h : m.IsMonomial) :
    m.project.IsPolar .positive ∧ m.project.IsPolar .negative := by
  induction m <;> simp only [IsMonomial, ModExpr.project, Projection.IsPolar] at * <;>
    aesop (add safe constructors [BoolExpr.IsPositive, BoolExpr.IsHorn])

theorem IsMonomial.project {m : ModExpr} (h : m.IsMonomial) (p : Polarity) :
    m.project.IsPolar p := by
  cases p
  · exact h.project_both.1
  · exact h.project_both.2


theorem IsPolar.project {m : ModExpr} {p : Polarity} (h : m.IsPolar p) :
    m.project.IsPolar p := by
  induction m generalizing p with
  | const m => cases p <;> exact ⟨.const _, .const _, .const _, .const _⟩
  | var v => cases p <;> exact ⟨.atom _, .atom _, .atom _, .const _⟩
  | compose a b ia ib =>
    cases p <;> have xa := ia h.1 <;> have xb := ib h.2 <;> exact ⟨.and xa.1 xb.1, .and xa.2.1 xb.2.1,
      .and xa.2.2.1 xb.2.2.1, .and xa.2.2.2 xb.2.2.2⟩
  | join a b ia ib =>
    cases p with
    | negative => exact False.elim h
    | positive =>
      have xa := ia h.1
      have xb := ib h.2
      exact ⟨.or xa.1 xb.1, .or xa.2.1 xb.2.1,
        .and xa.2.2.1 xb.2.2.1, .and xa.2.2.2 xb.2.2.2⟩
  | meet a b ia ib =>
    cases p with
    | positive => exact False.elim h
    | negative =>
      have xa := ia h.1
      have xb := ib h.2
      exact ⟨.and xa.1 xb.1, .and xa.2.1 xb.2.1,
        .or xa.2.2.1 xb.2.2.1, .and xa.2.2.2 xb.2.2.2⟩
  | leftResidual a b ia ib =>
    cases p with
    | negative => exact False.elim h
    | positive =>
      have xa := ia h.1
      have xb := ib h.2
      exact ⟨xa.1, xa.2.1, .imp xb.2.2.1 xa.2.2.1,
        .and xa.2.2.2 (.and xb.2.2.2 (.and (.imp xa.1 xb.1)
          (.and (.imp xa.2.1 xb.2.1) (.const true))))⟩
  | rightResidual a b ia ib =>
    cases p with
    | positive => exact False.elim h
    | negative =>
      have xa := ia h.1
      have xb := ib h.2
      exact ⟨.imp xa.1 xb.1, .imp xa.2.1 xb.2.1, xb.2.2.1,
        .and xa.2.2.2 (.and xb.2.2.2 (.and (.imp xb.2.2.1 xa.2.2.1) (.const true)))⟩
  | close a ia =>
    cases p <;> have xa := ia h <;> exact ⟨.const _, xa.2.2.1, .const _, xa.2.2.2⟩
  | closeInv a ia =>
    cases p <;> have xa := ia h <;> exact ⟨.const _, .const _, xa.2.1, xa.2.2.2⟩
  | future a ia =>
    cases p <;> have xa := ia h <;> exact ⟨xa.1, xa.2.1, .const _, xa.2.2.2⟩
  | capture a _ =>
    have xa := (show a.IsMonomial from by cases p <;> exact h).project_both
    cases p
    · exact ⟨xa.1.1, xa.1.2.1, xa.2.2.1, xa.1.2.2.2⟩
    · exact ⟨xa.2.1, xa.2.2.1, xa.1.2.1, xa.2.2.2.2⟩

theorem IsPolar.defined {m : ModExpr} {p : Polarity} (h : m.IsPolar p) :
    m.project.defined.IsHorn := by
  cases p <;> exact h.project.2.2.2


theorem IsMonomial.subst {m : ModExpr} (h : m.IsMonomial) {σ : ModVar → ModExpr}
    (hs : ∀ v, (σ v).IsMonomial) : (m.subst σ).IsMonomial := by
  induction m <;> simp_all [ModExpr.subst, IsMonomial]

theorem IsPolar.subst {m : ModExpr} {p : Polarity} (h : m.IsPolar p)
    {σ : ModVar → ModExpr} (hs : ∀ v, (σ v).IsMonomial) : (m.subst σ).IsPolar p := by
  induction m generalizing p <;> cases p <;>
    simp_all [ModExpr.subst, IsPolar, Polarity.flip, IsMonomial.subst, IsMonomial.isPolar]


theorem IsMonomial.foldConstants {m : ModExpr} (h : m.IsMonomial) :
    m.foldConstants.IsMonomial := by
  unfold ModExpr.foldConstants
  split
  · trivial
  · split <;> repeat' split
    all_goals simp_all [ModExpr.IsMonomial]

theorem IsMonomial.normalize {m : ModExpr} (h : m.IsMonomial) : m.normalize.IsMonomial := by
  induction m <;> simp only [ModExpr.normalize]
  all_goals first | exact h | apply IsMonomial.foldConstants
  all_goals simp_all [ModExpr.IsMonomial]

theorem IsPolar.foldConstants {m : ModExpr} {p : Polarity} (h : m.IsPolar p) :
    m.foldConstants.IsPolar p := by
  unfold ModExpr.foldConstants
  split
  · cases p <;> trivial
  · split <;> repeat' split
    all_goals cases p <;> simp_all [ModExpr.IsPolar]

theorem IsPolar.normalize {m : ModExpr} {p : Polarity} (h : m.IsPolar p) :
    m.normalize.IsPolar p := by
  induction m generalizing p <;> simp only [ModExpr.normalize]
  all_goals first | exact h | apply IsPolar.foldConstants
  all_goals cases p <;> simp_all [ModExpr.IsPolar, Polarity.flip, IsMonomial.normalize]


end ModExpr

theorem Modality.toExpr_monomial (m : Modality) : m.toExpr.IsMonomial := by
  induction m <;> simp_all [Modality.toExpr, ModExpr.IsMonomial]

theorem PolarMod.toExpr_polar {p : Polarity} (m : PolarMod p) : m.toExpr.IsPolar p := by
  induction m <;> simp_all [PolarMod.toExpr, ModExpr.IsPolar, Polarity.flip,
    Modality.toExpr_monomial, ModExpr.IsMonomial.isPolar]

namespace TypeExpr

theorem IsMonomial.isPolar {t : Ty} (h : t.IsMonomial) (p : Polarity) : t.IsPolar p := by
  induction t generalizing p <;>
    simp_all [IsMonomial, IsPolar, ModExpr.IsMonomial.isPolar]

theorem IsMonomial.subst {t : Ty} (h : t.IsMonomial) {ts : TypeVar → Ty}
    {ms : ModVar → ModExpr} (ht : ∀ v, (ts v).IsMonomial)
    (hm : ∀ v, (ms v).IsMonomial) : (t.subst ts ms).IsMonomial := by
  induction t <;> simp_all [TypeExpr.subst, IsMonomial, ModExpr.IsMonomial.subst]

theorem IsPolar.subst {t : Ty} {p : Polarity} (h : t.IsPolar p) {ts : TypeVar → Ty}
    {ms : ModVar → ModExpr} (ht : ∀ v, (ts v).IsMonomial)
    (hm : ∀ v, (ms v).IsMonomial) : (t.subst ts ms).IsPolar p := by
  induction t generalizing p <;>
    simp_all [TypeExpr.subst, IsPolar, IsMonomial.isPolar, ModExpr.IsPolar.subst]

theorem IsMonomial.normalize {a : Ty} (h : a.IsMonomial) : a.normalize.IsMonomial := by
  induction a <;> simp only [TypeExpr.normalize]
  all_goals try solve | simp_all [TypeExpr.IsMonomial]
  rename_i a m ih
  have ha := ih h.1
  have hm := h.2.normalize
  split
  · rename_i b k hk
    have hb : b.IsMonomial ∧ k.IsMonomial := by simpa only [hk, TypeExpr.IsMonomial] using ha
    exact ⟨hb.1, ModExpr.IsMonomial.normalize (And.intro hb.2 hm)⟩
  · split
    · exact ha
    · exact ⟨ha, hm⟩

theorem IsMonomial.outer {a : Ty} (h : a.IsMonomial) :
    a.outer.1.IsMonomial ∧ a.outer.2.IsMonomial := by
  induction a <;> simp_all [TypeExpr.outer, TypeExpr.IsMonomial,
    ModExpr.IsMonomial, ModExpr.epsilon]


end TypeExpr

theorem PolarTy.toTy_polar {p : Polarity} (t : PolarTy p) : t.toTy.IsPolar p := by
  induction t <;> simp_all [PolarTy.toTy, TypeExpr.IsPolar, PolarMod.toExpr_polar]

theorem modeFormula_isHorn {a b : ModExpr}
    (ha : a.IsPolar .positive) (hb : b.IsPolar .negative) : (modeFormula a b).IsHorn := by
  exact .and ha.defined (.and hb.defined (.and (.imp ha.project.1 hb.project.1)
    (.and (.imp ha.project.2.1 hb.project.2.1)
      (.and (.imp hb.project.2.2.1 ha.project.2.2.1) (.const true)))))

theorem Constraint.IsPolar.formula {c : Constraint} (h : c.IsPolar) :
    (constraintModeFormula c).IsHorn := by
  cases c with
  | sub | equal | equiv => exact .const true
  | mode a b => exact modeFormula_isHorn h.1 h.2
  | defined m => obtain ⟨p, h⟩ := h; exact h.defined

theorem Bounds.IsPolar.formula {cs : Bounds} (h : cs.IsPolar) :
    (boundsModeFormula cs).IsHorn := by
  exact BoolExpr.IsHorn.all (by simpa [List.mem_map] using fun c hc => (h c hc).formula)

theorem Constraint.IsInference.isPolar {c : Constraint} (h : c.IsInference) : c.IsPolar := by
  cases c <;> simp_all [Constraint.IsInference, Constraint.IsPolar,
    TypeExpr.IsMonomial.isPolar]

theorem Bounds.IsInference.isPolar {cs : Bounds} (h : cs.IsInference) : cs.IsPolar :=
  fun c hc => (h c hc).isPolar

theorem Bounds.IsInference.formula {cs : Bounds} (h : cs.IsInference) :
    (boundsModeFormula cs).IsHorn := h.isPolar.formula


@[simp] theorem Bounds.isInference_nil : Bounds.IsInference [] := by simp [IsInference]

@[simp] theorem Bounds.isInference_cons {c : Constraint} {cs : Bounds} :
    Bounds.IsInference (c :: cs) ↔ c.IsInference ∧ cs.IsInference := by simp [IsInference]

@[simp] theorem Bounds.isInference_append {cs ds : Bounds} :
    (cs ++ ds).IsInference ↔ cs.IsInference ∧ ds.IsInference := by
  simp [IsInference, or_imp, forall_and]

theorem Constraint.IsInference.normalize {c : Constraint} (h : c.IsInference) :
    c.normalize.IsInference := by
  cases c <;> simp only [Constraint.normalize, Constraint.IsInference, Constraint.IsPolar] at *
  all_goals aesop (add safe apply [TypeExpr.IsMonomial.normalize, ModExpr.IsPolar.normalize])

theorem TypeExpr.IsMonomial.wellFormedBounds {a : Ty} (h : a.IsMonomial) :
    a.wellFormedBounds.IsInference := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, TypeExpr.IsMonomial,
    Constraint.IsInference, Constraint.IsPolar]
  exact ⟨.positive, h.2.isPolar .positive⟩


theorem Substitution.IsMonomial.type {σ : Substitution} (hσ : σ.IsMonomial) (v : TypeVar) :
    (σ.type v).IsMonomial := by
  cases v with
  | rigid _ => trivial
  | flex n =>
    cases he : σ.types.lookup n
    · simp [Substitution.type, he, TypeExpr.IsMonomial]
    · obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [Substitution.type, he, Option.getD_some] using
        hσ.types n _ (by simp [hh])

theorem Substitution.IsMonomial.mode {σ : Substitution} (hσ : σ.IsMonomial) (v : ModVar) :
    (σ.mode v).IsMonomial := by
  cases v with
  | rigid _ => trivial
  | flex n =>
    cases he : σ.modes.lookup n
    · simp [Substitution.mode, he, ModExpr.IsMonomial]
    · obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
      simpa only [Substitution.mode, he, Option.getD_some] using
        hσ.modes n _ (by simp [hh])

theorem Substitution.IsMonomial.ty {σ : Substitution} (hσ : σ.IsMonomial) {a : Ty}
    (ha : a.IsMonomial) : (σ.ty a).IsMonomial := ha.subst hσ.type hσ.mode

theorem Substitution.IsMonomial.constraint {σ : Substitution} (hσ : σ.IsMonomial)
    {c : Constraint} (hc : c.IsInference) : (σ.constraint c).IsInference := by
  cases c <;>
    simp only [Substitution.constraint, Constraint.subst, Constraint.IsInference, Constraint.IsPolar] at *
  case sub a b | equiv a b => exact ⟨hσ.ty hc.1, hσ.ty hc.2⟩
  case mode a b => exact ⟨hc.1.subst hσ.mode, hc.2.subst hσ.mode⟩
  case defined a => obtain ⟨p, hc⟩ := hc; exact ⟨p, hc.subst hσ.mode⟩
  case equal v a =>
    cases v with
    | rigid n => exact hσ.ty hc
    | flex n =>
      cases he : σ.types.lookup n <;> simp only [he]
      · exact hσ.ty hc
      · have hn := hσ.type (.flex n)
        simp only [Substitution.type, he, Option.getD_some] at hn
        exact ⟨hn, hσ.ty hc⟩

theorem Substitution.IsMonomial.bounds {σ : Substitution} (hσ : σ.IsMonomial)
    {cs : Bounds} (hc : cs.IsInference) : (σ.bounds cs).IsInference := by
  rintro _ hh
  obtain ⟨c, hm, rfl⟩ := List.mem_map.mp hh
  exact hσ.constraint (hc c hm)

theorem Substitution.isMonomial_empty : ({} : Substitution).IsMonomial := ⟨by simp, by simp⟩

theorem Substitution.isMonomial_singleType {n a} (ha : TypeExpr.IsMonomial a) :
    ({types := [(n, a)]} : Substitution).IsMonomial := ⟨by simpa using ha, by simp⟩

theorem Substitution.IsMonomial.extendType {σ : Substitution} (hσ : σ.IsMonomial)
    {n a} (ha : TypeExpr.IsMonomial a) : (σ.extendType n a).IsMonomial := by
  refine ⟨?_, hσ.modes⟩
  intro k b hb
  simp only [Substitution.extendType, List.mem_cons, List.mem_map, List.mem_filter,
    Prod.exists, Prod.mk.injEq] at hb
  rcases hb with ⟨rfl, rfl⟩ | ⟨j, c, ⟨hc, _⟩, rfl, rfl⟩
  · exact ha
  · exact (Substitution.isMonomial_singleType ha).ty (hσ.types j c hc)


theorem SolverState.IsInference.emit {s : SolverState} (hs : s.IsInference)
    (r : RewriteRule) {cs : Bounds} (hc : cs.IsInference) : (s.emit r cs).IsInference :=
  ⟨Bounds.isInference_append.mpr ⟨hc, hs.pending⟩, hs.bounds, hs.substitution⟩

theorem SolverState.IsInference.retain {s : SolverState} (hs : s.IsInference)
    (r : RewriteRule) {c : Constraint} (hc : c.IsInference) : (s.retain r c).IsInference := by
  unfold SolverState.retain
  split
  · exact ⟨hs.pending, hs.bounds, hs.substitution⟩
  · exact ⟨hs.pending, Bounds.isInference_cons.mpr ⟨hc, hs.bounds⟩, hs.substitution⟩

theorem SolverState.IsInference.skeleton {s : SolverState} (hs : s.IsInference)
    {a : Ty} (ha : a.IsMonomial) :
    (s.skeleton a).1.IsMonomial ∧ (s.skeleton a).2.IsInference := by
  cases a <;> refine ⟨?_, ⟨hs.pending, hs.bounds, hs.substitution⟩⟩
  all_goals simp_all [SolverState.skeleton, SolverState.freshType,
    SolverState.freshMode, TypeExpr.IsMonomial, ModExpr.IsMonomial]

theorem recordModeBound_isInference {s : SolverState} (hs : s.IsInference)
    {a b : ModExpr} (ha : a.IsPolar .positive) (hb : b.IsPolar .negative) :
    (recordModeBound s a b).IsInference := hs.retain .modeBound (And.intro ha hb)

set_option maxHeartbeats 800000 in
theorem stepMode_isInference {s a b t} (hs : SolverState.IsInference s)
    (ha : ModExpr.IsPolar .positive a) (hb : b.IsPolar .negative)
    (h : stepMode s a b = .success t) : t.IsInference := by
  have hga : Constraint.IsInference (.defined a) := ⟨.positive, ha⟩
  have hgb : Constraint.IsInference (.defined b) := ⟨.negative, hb⟩
  unfold stepMode at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals repeat' first
    | apply recordModeBound_isInference
    | apply SolverState.IsInference.emit
    | apply SolverState.IsInference.retain
  all_goals first | exact hs | simp_all [Constraint.IsInference, Constraint.IsPolar, ModExpr.IsPolar,
    Bounds.isInference_cons, Polarity.flip]


theorem ModExpr.IsMonomial.exists_polar {m : ModExpr} (h : m.IsMonomial) :
    ∃ p, m.IsPolar p := ⟨.positive, h.isPolar .positive⟩

set_option maxHeartbeats 800000 in
theorem stepType_isInference {s a b t} (hs : SolverState.IsInference s)
    (ha : TypeExpr.IsMonomial a) (hb : b.IsMonomial)
    (h : stepType s a b = .success t) : t.IsInference := by
  have hla := ha.outer
  have hrb := hb.outer
  have hl := hla.2.normalize
  have hr := hrb.2.normalize
  unfold stepType at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind, reduceCtorEq] at h
  all_goals cases h
  all_goals try solve
    | exact hs.emit _ (by simp_all [Constraint.IsInference, Constraint.IsPolar,
        TypeExpr.IsMonomial, ModExpr.IsPolar, ModExpr.top,
        ModExpr.IsMonomial.isPolar])
    | exact (hs.retain _ (by simp_all [Constraint.IsInference, TypeExpr.IsMonomial])).emit _
        (by simp_all [Constraint.IsInference, Constraint.IsPolar, ModExpr.IsMonomial.exists_polar])
  all_goals
    have hf := Eq.mp (congrArg (fun p : Ty × SolverState => p.1.IsMonomial ∧ p.2.IsInference)
      ‹s.skeleton _ = (_, _)›) (hs.skeleton (by simp_all))
    exact hf.2.emit _ (by simp_all [Constraint.IsInference, TypeExpr.IsMonomial])


theorem SolverState.IsInference.advance {s : SolverState} (hs : s.IsInference)
    {c rest seen} (hp : s.pending = c :: rest) :
    {s with pending := rest, seen := seen}.IsInference :=
  ⟨(Bounds.isInference_cons.mp (hp ▸ hs.pending)).2, hs.bounds, hs.substitution⟩

theorem SolverState.IsInference.normalized_head {s : SolverState} (hs : s.IsInference)
    {c rest} (hp : s.pending = c :: rest) : (s.substitution.constraint c).normalize.IsInference :=
  (hs.substitution.constraint (Bounds.isInference_cons.mp (hp ▸ hs.pending)).1).normalize

set_option maxHeartbeats 800000 in
theorem solverStep_isInference {s t} (hs : SolverState.IsInference s)
    (h : solverStep s = .success t) : t.IsInference := by
  unfold solverStep at h
  repeat' split at h
  all_goals simp only [bind, pure, RunResult.bind] at h
  all_goals repeat' split at h
  all_goals try simp only [reduceCtorEq] at h
  all_goals try have hc := hs.normalized_head ‹s.pending = _ :: _›
  all_goals first
    | exact stepType_isInference (hs.advance ‹s.pending = _ :: _›)
        (by simp_all [Constraint.IsInference]) (by simp_all [Constraint.IsInference]) h
    | exact stepMode_isInference (hs.advance ‹s.pending = _ :: _›)
        (by simp_all [Constraint.IsInference, Constraint.IsPolar])
        (by simp_all [Constraint.IsInference, Constraint.IsPolar]) h
    | skip
  all_goals cases h
  all_goals try exact hs
  all_goals try solve
    | exact hs.advance ‹s.pending = _ :: _›
    | exact (hs.advance ‹s.pending = _ :: _›).emit _
        (by simp_all [Constraint.IsInference, TypeExpr.IsMonomial])
    | exact (hs.advance ‹s.pending = _ :: _›).retain _
        (by simp_all [Constraint.IsInference, Constraint.IsPolar])
    | simp_all [Constraint.IsInference]
  simp only [‹(s.substitution.constraint _).normalize = .equal _ _›, Constraint.IsInference] at hc
  refine ⟨(Substitution.isMonomial_singleType hc).bounds ?_, Bounds.isInference_nil,
    hs.substitution.extendType hc⟩
  exact Bounds.isInference_append.mpr ⟨Bounds.isInference_append.mpr
    ⟨(hs.advance (seen := []) ‹s.pending = _ :: _›).pending, hs.bounds⟩,
    hc.wellFormedBounds⟩

theorem runWorklist_isInference {fuel s t} (hs : SolverState.IsInference s)
    (h : runWorklist fuel s = .success t) : t.IsInference := by
  induction fuel generalizing s with
  | zero => cases h
  | succ fuel ih =>
    simp only [runWorklist] at h
    split at h
    · cases h; exact hs
    · cases ht : solverStep s <;> simp [ht, bind, RunResult.bind] at h
      exact ih (solverStep_isInference hs ht) h

theorem runSolver_isInference {fuel s t} (hs : SolverState.IsInference s)
    (h : runSolver fuel s = .success t) : t.IsInference := by
  simp only [runSolver, bind, RunResult.bind] at h
  repeat' split at h
  all_goals first | exact runWorklist_isInference hs h | contradiction

theorem solveFrom_isInference {fuel nt nm cs result} (hc : Bounds.IsInference cs)
    (h : solveFrom fuel nt nm cs = .success result) :
    result.bounds.IsInference ∧ result.substitution.IsMonomial := by
  unfold solveFrom at h
  cases hs : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} <;>
    simp [hs, bind, RunResult.bind] at h
  split at h <;> cases h
  have ht := runSolver_isInference ⟨hc, Bounds.isInference_nil, Substitution.isMonomial_empty⟩ hs
  exact ⟨ht.bounds, ht.substitution⟩

theorem solve_isInference {fuel cs result} (hc : Bounds.IsInference cs)
    (h : solve fuel cs = .success result) :
    result.bounds.IsInference ∧ result.substitution.IsMonomial := solveFrom_isInference hc h


theorem Scheme.freshSubstitution_isMonomial (s : Scheme) (nt nm : Nat) (rigid : Bool := false) :
    (s.freshSubstitution nt nm rigid).IsMonomial := by
  constructor <;> intro n a ha <;>
    simp only [Scheme.freshSubstitution, List.mem_map, Prod.exists, Prod.mk.injEq] at ha
  all_goals obtain ⟨p, i, _, rfl, rfl⟩ := ha; trivial

theorem Scheme.IsInference.instantiate {s : Scheme} (hs : s.IsInference) (nt nm : Nat)
    (rigid : Bool := false) :
    (s.instantiate nt nm rigid).1.IsInference ∧ (s.instantiate nt nm rigid).2.IsMonomial :=
  ⟨(s.freshSubstitution_isMonomial nt nm rigid).bounds hs.2,
    (s.freshSubstitution_isMonomial nt nm rigid).ty hs.1⟩

theorem Scheme.IsInference.share {s : Scheme} (hs : s.IsInference) : s.share.IsInference := by
  simp_all [Scheme.IsInference, Scheme.share, Constraint.IsInference,
    TypeExpr.IsMonomial, ModExpr.IsMonomial]

theorem Scheme.IsInference.lock {s : Scheme} {m} (hs : s.IsInference) (hm : m.IsMonomial) :
    (s.lock m).IsInference := by
  simp_all [Scheme.IsInference, Scheme.lock, Constraint.IsInference,
    TypeExpr.IsMonomial, ModExpr.IsMonomial]

@[simp] theorem AlgorithmicContext.isInference_nil : AlgorithmicContext.IsInference [] := by
  simp [IsInference]

@[simp] theorem AlgorithmicContext.isInference_cons {e : ContextEntry} {Γ : AlgorithmicContext} :
    AlgorithmicContext.IsInference (e :: Γ) ↔ e.IsInference ∧ Γ.IsInference := by
  simp [IsInference]

theorem lookupScheme_isInference {Γ i s} (hΓ : AlgorithmicContext.IsInference Γ)
    (h : lookupScheme Γ i = .success s) : s.IsInference := by
  have hh := lookupScheme_sound h
  clear h
  induction hh with
  | here => exact (AlgorithmicContext.isInference_cons.mp hΓ).1
  | there h ih => exact ih (AlgorithmicContext.isInference_cons.mp hΓ).2
  | locked h ih =>
    exact (ih (AlgorithmicContext.isInference_cons.mp hΓ).2).lock
      (AlgorithmicContext.isInference_cons.mp hΓ).1

theorem UsageSplit.isInference {Γ Γ₁ Γ₂} (h : UsageSplit Γ Γ₁ Γ₂)
    (hΓ : AlgorithmicContext.IsInference Γ) :
    AlgorithmicContext.IsInference Γ₁ ∧ AlgorithmicContext.IsInference Γ₂ := by
  induction h <;> simp_all [ContextEntry.IsInference, Scheme.IsInference,
    Constraint.IsInference, TypeExpr.IsMonomial, ModExpr.IsMonomial]

theorem splitContext_isInference {Γ : AlgorithmicContext} (hΓ : Γ.IsInference) (X Y : Finset Nat) :
    AlgorithmicContext.IsInference (splitContext X Y Γ).1 ∧
      AlgorithmicContext.IsInference (splitContext X Y Γ).2 :=
  (splitContext_spec Γ X Y).isInference hΓ


set_option maxHeartbeats 800000 in
/-- Every successful generation from a proper source context preserves the
monomial type and polarized constraint domain, including closed definitions. -/
theorem generate_isInference {fuel Γ t s r} (h : generate fuel Γ t s = .success r)
    (hΓ : AlgorithmicContext.IsInference Γ) (hs : s.constraints.IsInference) :
    r.type.IsMonomial ∧ r.state.constraints.IsInference := by
  induction fuel generalizing Γ t s r
  case zero => cases h
  case succ n ih =>
    cases t
    case defn rhs body =>
      simp only [generate, bind, pure, RunResult.bind] at h
      repeat' (split at h <;> try contradiction)
      cases h
      rename_i hclosed _ rr hr _ solved hsolve _ br hb
      have hrr := ih hr AlgorithmicContext.isInference_nil Bounds.isInference_nil
      have hsol := solveFrom_isInference hrr.2 hsolve
      apply ih hb ?_ hs
      simpa [ContextEntry.IsInference, Scheme.IsInference, Scheme.generalize] using
        And.intro (And.intro (hsol.2.ty hrr.1) hsol.1) hΓ
    all_goals simp only [generate, bind, pure, RunResult.bind] at h
    all_goals repeat' (split at h <;> try contradiction)
    all_goals cases h
    all_goals try have hv :=
      (lookupScheme_isInference hΓ ‹lookupScheme Γ _ = .success _›).instantiate s.nextType s.nextMode
    all_goals simp [InferenceState.freshType, InferenceState.freshMode,
      InferenceState.emit, InferenceState.instantiate, TypeExpr.IsMonomial, ModExpr.IsMonomial,
      Constraint.IsInference, Constraint.IsPolar, ModExpr.IsPolar,
      ModExpr.bottom, Scheme.mono] at *
    all_goals grind only [splitContext_isInference, AlgorithmicContext.isInference_cons,
      TypeExpr.IsMonomial.wellFormedBounds,
      ContextEntry.IsInference, Scheme.IsInference, TypeExpr.IsMonomial, ModExpr.IsMonomial,
      Constraint.IsInference, Constraint.IsPolar, ModExpr.IsPolar,
      Bounds.isInference_append, Bounds.isInference_cons, Bounds.isInference_nil]

/-- In particular, ordinary closed inference needs no assumed grammar invariant. -/
theorem generate_closed_isInference {fuel t s r}
    (h : generate fuel [] t s = .success r) (hs : s.constraints = []) :
    r.type.IsMonomial ∧ r.state.constraints.IsInference :=
  generate_isInference h AlgorithmicContext.isInference_nil (hs ▸ Bounds.isInference_nil)


@[simp] theorem Context.isInference_nil : Context.IsInference [] := by simp [IsInference]

theorem Context.IsInference.algorithmic {Γ : Context} (hΓ : Γ.IsInference) :
    AlgorithmicContext.IsInference (Γ.map ContextEntry.binding) := by
  intro e he
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
  cases o with
  | none => trivial
  | some t => exact hΓ _ ho t rfl

theorem infer_isInference {fuel Γ t result} (h : infer fuel Γ t = .success result)
    (hΓ : Context.IsInference Γ) :
    result.scheme.IsInference ∧ result.residual.IsInference ∧ result.substitution.IsMonomial := by
  simp only [infer, bind, pure, RunResult.bind] at h
  repeat' (split at h <;> try contradiction)
  cases h
  have hg := generate_isInference ‹generate fuel _ t _ = .success _› hΓ.algorithmic
    (by simp [initialInferenceState])
  have hs := solveFrom_isInference hg.2 ‹solveFrom fuel _ _ _ = .success _›
  exact ⟨⟨hs.2.ty hg.1, hs.1⟩, hs.1, hs.2⟩

theorem infer_closed_isInference {fuel t result} (h : infer fuel [] t = .success result) :
    result.scheme.IsInference ∧ result.residual.IsInference ∧ result.substitution.IsMonomial :=
  infer_isInference h Context.isInference_nil

/-- The consistency query after successful structural rewriting is in the direct
Horn grammar; no residual-definedness premise is omitted. -/
theorem runSolver_isHorn {fuel s result} (hs : SolverState.IsInference s)
    (h : runSolver fuel s = .success result) :
    (boundsModeFormula result.bounds).IsHorn := (runSolver_isInference hs h).bounds.formula

/-- An executable generator result supplies the complete consistency-query
invariant, even before the query has selected a witness. -/
theorem generated_runSolver_isHorn {fuel Γ t s generated solveFuel nt nm result}
    (hg : generate fuel Γ t s = .success generated)
    (hΓ : AlgorithmicContext.IsInference Γ) (hs : s.constraints.IsInference)
    (hr : runSolver solveFuel {pending := generated.state.constraints, nextType := nt, nextMode := nm} = .success result) :
    (boundsModeFormula result.bounds).IsHorn :=
  runSolver_isHorn ⟨(generate_isInference hg hΓ hs).2, Bounds.isInference_nil,
    Substitution.isMonomial_empty⟩ hr

theorem infer_closed_isHorn {fuel t result} (h : infer fuel [] t = .success result) :
    (boundsModeFormula result.residual).IsHorn := (infer_closed_isInference h).2.1.formula


/-- Proper inference bounds are accepted by the actual executable Horn parser. -/
theorem Bounds.IsInference.isPolarized {cs : Bounds} (h : cs.IsInference) :
    ModeConsistency.isPolarized cs = true := by
  obtain ⟨r, hr⟩ := (HornPropagation.horn_domain_iff _).mpr h.formula
  simp [ModeConsistency.isPolarized, hr]

theorem ModeConsistency.solve_eq_horn_of_isInference {cs : Bounds}
    (h : cs.IsInference) (fuel : Nat) :
    ModeConsistency.solve fuel cs = HornPropagation.satisfiableModes fuel cs := by
  simp [ModeConsistency.solve, h.isPolarized]

/-- Structural solving of a generated query always selects direct Horn
propagation at the consistency stage, for every checking budget. -/
theorem generated_runSolver_uses_horn {fuel Γ t s generated solveFuel nt nm result}
    (hg : generate fuel Γ t s = .success generated)
    (hΓ : AlgorithmicContext.IsInference Γ) (hs : s.constraints.IsInference)
    (hr : runSolver solveFuel {pending := generated.state.constraints, nextType := nt, nextMode := nm} =
      .success result) (checkFuel : Nat) :
    ModeConsistency.solve checkFuel result.bounds =
      HornPropagation.satisfiableModes checkFuel result.bounds :=
  ModeConsistency.solve_eq_horn_of_isInference
    (runSolver_isInference ⟨(generate_isInference hg hΓ hs).2, Bounds.isInference_nil,
      Substitution.isMonomial_empty⟩ hr).bounds checkFuel

/-- No source-context or grammar hypothesis is required for the closed pipeline. -/
theorem generated_closed_runSolver_uses_horn {fuel t initialType initialMode generated solveFuel nt nm result}
    (hg : generate fuel [] t {nextType := initialType, nextMode := initialMode} = .success generated)
    (hr : runSolver solveFuel {pending := generated.state.constraints, nextType := nt, nextMode := nm} =
      .success result) (checkFuel : Nat) :
    ModeConsistency.solve checkFuel result.bounds =
      HornPropagation.satisfiableModes checkFuel result.bounds :=
  generated_runSolver_uses_horn hg AlgorithmicContext.isInference_nil
    Bounds.isInference_nil hr checkFuel


/-- This equality also covers structural rejection or exhaustion and does not
assume that either the consistency query or its enclosing term succeeds. -/
theorem generated_consistency_pipeline_uses_horn {fuel Γ t s generated solveFuel nt nm}
    (hg : generate fuel Γ t s = .success generated)
    (hΓ : AlgorithmicContext.IsInference Γ) (hs : s.constraints.IsInference) (checkFuel : Nat) :
    (do
      let residual ← runSolver solveFuel
        {pending := generated.state.constraints, nextType := nt, nextMode := nm}
      ModeConsistency.solve checkFuel residual.bounds) =
    (do
      let residual ← runSolver solveFuel
        {pending := generated.state.constraints, nextType := nt, nextMode := nm}
      HornPropagation.satisfiableModes checkFuel residual.bounds) := by
  cases hr : runSolver solveFuel
      {pending := generated.state.constraints, nextType := nt, nextMode := nm} with
  | success result =>
    simpa only [hr, bind, RunResult.bind] using generated_runSolver_uses_horn hg hΓ hs hr checkFuel
  | rejected message => simp [bind, RunResult.bind]
  | exhausted => simp [bind, RunResult.bind]

/-- Every definition RHS is generated with this empty context and empty bounds,
regardless of its enclosing context or whether the enclosing run later succeeds. -/
theorem generated_closed_consistency_pipeline_uses_horn
    {fuel t initialType initialMode generated solveFuel nt nm}
    (hg : generate fuel [] t {nextType := initialType, nextMode := initialMode} = .success generated)
    (checkFuel : Nat) :
    (do
      let residual ← runSolver solveFuel
        {pending := generated.state.constraints, nextType := nt, nextMode := nm}
      ModeConsistency.solve checkFuel residual.bounds) =
    (do
      let residual ← runSolver solveFuel
        {pending := generated.state.constraints, nextType := nt, nextMode := nm}
      HornPropagation.satisfiableModes checkFuel residual.bounds) :=
  generated_consistency_pipeline_uses_horn hg AlgorithmicContext.isInference_nil
    Bounds.isInference_nil checkFuel


/-- The complete solver call, including rejected and exhausted outcomes, agrees
with a call whose consistency stage directly uses the Horn checker. -/
theorem solveFrom_eq_horn {cs : Bounds} (hc : cs.IsInference) (fuel nt nm : Nat) :
    solveFrom fuel nt nm cs = (do
      let s ← runSolver fuel {pending := cs, nextType := nt, nextMode := nm}
      let witness ← HornPropagation.satisfiableModes fuel s.bounds
      return ⟨s.substitution, s.bounds, witness, s.nextType, s.nextMode, s.trace.reverse⟩) := by
  unfold solveFrom
  cases hr : runSolver fuel {pending := cs, nextType := nt, nextMode := nm} with
  | success result =>
    have hd := (runSolver_isInference
      ⟨hc, Bounds.isInference_nil, Substitution.isMonomial_empty⟩ hr).bounds
    simp only [bind, RunResult.bind, satisfiableModes,
      ModeConsistency.solve_eq_horn_of_isInference hd]
  | rejected message => rfl
  | exhausted => rfl

/-- Every reached definition check uses Horn propagation. The enclosing
computation and the check itself may succeed, reject, or exhaust their budgets. -/
theorem generate_defn_eq_horn (fuel : Nat) (Γ : AlgorithmicContext)
    (rhs body : RawTerm) (s : InferenceState) :
    generate (fuel + 1) Γ (.defn rhs body) s = (do
      if rhs.freeVars != ∅ then return ← .rejected "def RHS must be closed in term variables"
      let r ← generate fuel [] rhs {nextType := s.nextType, nextMode := s.nextMode}
      let solved ← (do
        let state ← runSolver fuel
          {pending := r.state.constraints, nextType := r.state.nextType, nextMode := r.state.nextMode}
        let witness ← HornPropagation.satisfiableModes fuel state.bounds
        return (⟨state.substitution, state.bounds, witness, state.nextType,
          state.nextMode, state.trace.reverse⟩ : Solved))
      let scheme := Scheme.generalize solved.bounds (solved.substitution.ty r.type)
      let result ← generate fuel (.binding (some scheme) :: Γ) body
        {s with nextType := solved.nextType, nextMode := solved.nextMode}
      return ⟨result.type, .defn r.term result.term, result.state⟩) := by
  simp only [generate]
  split
  · rfl
  · cases hg : generate fuel [] rhs {nextType := s.nextType, nextMode := s.nextMode} with
    | success generated =>
      have hc := (generate_closed_isInference hg rfl).2
      simp only [bind, pure, RunResult.bind, solveFrom_eq_horn hc]
    | rejected message => rfl
    | exhausted => rfl


/-- Final inference also selects the direct checker without any hypothesis on its
outcome. Nested definition checks are covered independently by `generate_defn_eq_horn`. -/
theorem infer_eq_horn {Γ : Context} (hΓ : Γ.IsInference) (fuel : Nat) (term : RawTerm) :
    infer fuel Γ term = (do
      let r ← generate fuel (Γ.map ContextEntry.binding) term (initialInferenceState Γ)
      let s ← (do
        let state ← runSolver fuel
          {pending := r.state.constraints, nextType := r.state.nextType, nextMode := r.state.nextMode}
        let witness ← HornPropagation.satisfiableModes fuel state.bounds
        return (⟨state.substitution, state.bounds, witness, state.nextType,
          state.nextMode, state.trace.reverse⟩ : Solved))
      let context := Γ.map (Option.map (fun t => t.subst s.substitution))
      let scheme := generalizeOver context s.bounds (s.substitution.ty r.type)
      return ⟨scheme, r.term, s.substitution, s.bounds, s.trace⟩) := by
  unfold infer
  cases hg : generate fuel (Γ.map ContextEntry.binding) term (initialInferenceState Γ) with
  | success generated =>
    have hc := (generate_isInference hg hΓ.algorithmic (by simp [initialInferenceState])).2
    simp only [bind, pure, RunResult.bind, solveFrom_eq_horn hc]
  | rejected message => rfl
  | exhausted => rfl


end ModalityInference
