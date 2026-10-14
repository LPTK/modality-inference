import ModalityInference.Proofs.ShapeCompleteness
import ModalityInference.Proofs.WorklistOrder

/-! Finite shape models used to bound type expansion and substitution. -/
namespace ModalityInference

@[simp] theorem TypeExpr.shapeUnder_outer (a : Ty) (ρ : TypeVar → Ty) :
    a.outer.1.shapeUnder ρ = a.shapeUnder ρ := by
  induction a <;> simp_all [TypeExpr.outer, TypeExpr.shapeUnder]

@[simp] theorem TypeExpr.shapeUnder_normalize (a : Ty) (ρ : TypeVar → Ty) :
    a.normalize.shapeUnder ρ = a.shapeUnder ρ := by
  induction a <;> simp_all [TypeExpr.normalize, TypeExpr.shapeUnder]
  split <;> simp_all [TypeExpr.shapeUnder]
  split <;> simp_all [TypeExpr.shapeUnder]

theorem TypeExpr.shapeUnder_congr (a : Ty) {ρ η : TypeVar → Ty}
    (h : ∀ v ∈ a.typeVars, ρ v = η v) : a.shapeUnder ρ = a.shapeUnder η := by
  induction a <;> simp_all [TypeExpr.shapeUnder, TypeExpr.typeVars, or_imp, forall_and]

theorem TypeExpr.shapeUnder_singleType (a : Ty) {ρ : TypeVar → Ty} {n t}
    (he : ρ (.flex n) = t.shapeUnder ρ) :
    (({types := [(n, t)]} : Substitution).ty a).shapeUnder ρ = a.shapeUnder ρ := by
  rw [Substitution.ty, TypeExpr.shapeUnder_subst]
  apply a.shapeUnder_congr
  intro v _
  cases v <;> simp [Substitution.type, TypeExpr.shapeUnder, List.lookup_cons]
  split <;> simp_all [TypeExpr.shapeUnder, beq_iff_eq]

namespace SolverShape

def mass (ρ : TypeVar → Ty) (keys : List Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => mass ρ keys n + if n ∈ keys then 0 else (ρ (.flex n)).shapeSize

theorem mass_congr {ρ η : TypeVar → Ty} {keys others : List Nat} {nt : Nat}
    (hv : ∀ n < nt, ρ (.flex n) = η (.flex n))
    (hk : ∀ n < nt, n ∈ keys ↔ n ∈ others) : mass ρ keys nt = mass η others nt := by
  induction nt with
  | zero => rfl
  | succ nt ih =>
    simp only [mass, ih (fun n hn => hv n (by omega)) (fun n hn => hk n (by omega)),
      hv nt (by omega), hk nt (by omega)]

theorem mass_eliminate (ρ : TypeVar → Ty) (keys : List Nat) {n nt : Nat}
    (hn : n < nt) (hk : n ∉ keys) :
    mass ρ (n :: keys) nt + (ρ (.flex n)).shapeSize = mass ρ keys nt := by
  induction nt with
  | zero => omega
  | succ nt ih =>
    by_cases he : n = nt
    · subst n
      have hm : mass ρ (nt :: keys) nt = mass ρ keys nt :=
        mass_congr (by simp) (by simp; omega)
      simp [mass, hm, hk]
    · simp only [mass, List.mem_cons, show nt ≠ n by omega, false_or]
      have hh := ih (by omega)
      omega

def expand (ρ : TypeVar → Ty) (nt : Nat) : Ty → TypeVar → Ty
  | .prod a b | .sum a b | .fn a b => fun v =>
      if v = .flex nt then a.shapeUnder ρ
      else if v = .flex (nt + 1) then b.shapeUnder ρ else ρ v
  | _ => ρ

theorem expand_below (ρ : TypeVar → Ty) (a : Ty) {nt v} (hv : v.index < nt) :
    expand ρ nt a v = ρ v := by
  have h₁ : v ≠ .flex nt := by intro h; subst v; exact Nat.lt_irrefl _ hv
  have h₂ : v ≠ .flex (nt + 1) := by intro h; subst v; change nt + 1 < nt at hv; omega
  cases a <;> simp [expand, h₁, h₂]

theorem expand_type (ρ : TypeVar → Ty) (a : Ty) {nt nm} {t : Ty} (ht : t.Bounded nt nm) :
    t.shapeUnder (expand ρ nt a) = t.shapeUnder ρ :=
  t.shapeUnder_congr (fun v hv => expand_below ρ a (((t.bounded_iff nt nm).mp ht).1 v hv))

theorem expand_skeleton (ρ : TypeVar → Ty) (s : SolverState) (a : Ty) :
    (s.skeleton a).1.shapeUnder (expand ρ s.nextType a) = a.shapeUnder ρ := by
  cases a <;> simp [SolverState.skeleton, SolverState.freshType, SolverState.freshMode,
    TypeExpr.shapeUnder, expand]

theorem mass_expansion (ρ : TypeVar → Ty) (s : SolverState) (keys : List Nat) {a n}
    (ha : Shape a (s.skeleton a).1) (hn : n < s.nextType) (hk : n ∉ keys)
    (hkeys : ∀ k ∈ keys, k < s.nextType) (he : ρ (.flex n) = a.shapeUnder ρ) :
    mass (expand ρ s.nextType a) (n :: keys) (s.skeleton a).2.nextType <
      mass ρ keys s.nextType := by
  have hbase : mass (expand ρ s.nextType a) keys s.nextType = mass ρ keys s.nextType :=
    mass_congr (fun k hh => expand_below ρ a hh) (by simp)
  have hn' : n < (s.skeleton a).2.nextType :=
    lt_of_lt_of_le hn (s.skeleton_counters a).1
  have helim := mass_eliminate (expand ρ s.nextType a) keys hn' hk
  rw [expand_below ρ a hn, he] at helim
  have hfresh : s.nextType ∉ keys ∧ s.nextType + 1 ∉ keys := by
    constructor <;> intro hh <;> have := hkeys _ hh <;> omega
  cases a <;> try cases ha
  all_goals simp only [SolverState.skeleton, SolverState.freshType, SolverState.freshMode,
    mass, hfresh.1, hfresh.2, ↓reduceIte, hbase] at helim ⊢
  all_goals simp [expand, TypeExpr.shapeUnder, TypeExpr.shapeSize, hfresh,
    show s.nextType ≠ n by omega, show s.nextType + 1 ≠ n by omega] at helim ⊢
  all_goals omega

def Satisfies (ρ : TypeVar → Ty) : Constraint → Prop
  | .sub a b | .equiv a b => a.shapeUnder ρ = b.shapeUnder ρ
  | .equal v t => ρ v = t.shapeUnder ρ
  | .mode _ _ | .defined _ => True

def Models (ρ : TypeVar → Ty) (cs : Bounds) : Prop := ∀ c ∈ cs, Satisfies ρ c

@[simp] theorem satisfies_normalize (ρ : TypeVar → Ty) (c : Constraint) :
    Satisfies ρ c.normalize ↔ Satisfies ρ c := by
  cases c <;> simp [Constraint.normalize, Satisfies]

@[simp] theorem models_cons {ρ c cs} : Models ρ (c :: cs) ↔ Satisfies ρ c ∧ Models ρ cs := by
  simp [Models]

@[simp] theorem models_append {ρ cs ds} : Models ρ (cs ++ ds) ↔ Models ρ cs ∧ Models ρ ds := by
  simp [Models, or_imp, forall_and]

theorem satisfies_singleType {ρ : TypeVar → Ty} {n t}
    (he : ρ (.flex n) = t.shapeUnder ρ) (c : Constraint) :
    Satisfies ρ (({types := [(n, t)]} : Substitution).constraint c) ↔ Satisfies ρ c := by
  have ht := fun a => TypeExpr.shapeUnder_singleType a he
  simp only [Substitution.ty] at ht
  cases c <;> simp only [Substitution.constraint, Constraint.subst, Substitution.ty, Satisfies, ht]
  rename_i v a
  cases v with
  | flex k =>
    cases h : k == n
    · simp [List.lookup_cons, h, ht]
    · have hk : k = n := by simpa only [beq_iff_eq] using h
      subst k
      simp [ht, he]
  | rigid k => simp [ht]

theorem models_singleType {ρ : TypeVar → Ty} {n t cs}
    (he : ρ (.flex n) = t.shapeUnder ρ) (h : Models ρ cs) :
    Models ρ (({types := [(n, t)]} : Substitution).bounds cs) := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  exact (satisfies_singleType he d).mpr (h d hd)

theorem satisfies_expand (ρ : TypeVar → Ty) (a : Ty) {nt nm c}
    (hc : Constraint.Bounded nt nm c) :
    Satisfies (expand ρ nt a) c ↔ Satisfies ρ c := by
  cases c <;> simp_all only [Constraint.Bounded, Satisfies]
  case sub | equiv => rw [expand_type ρ a hc.1, expand_type ρ a hc.2]
  case equal => rw [expand_below ρ a hc.1, expand_type ρ a hc.2]

theorem models_expand {ρ : TypeVar → Ty} {cs nt nm} (a : Ty)
    (hb : cs.Bounded nt nm) (h : Models ρ cs) : Models (expand ρ nt a) cs :=
  fun c hc => (satisfies_expand ρ a (hb c hc)).mpr (h c hc)

theorem models_wellFormedBounds (ρ : TypeVar → Ty) (a : Ty) : Models ρ a.wellFormedBounds := by
  induction a <;> simp_all [TypeExpr.wellFormedBounds, Models, Satisfies, or_imp]

def StateModels (ρ : TypeVar → Ty) (s : SolverState) : Prop :=
  Models ρ s.pending ∧ Models ρ s.bounds

def weight (ρ : TypeVar → Ty) (s : SolverState) : Nat :=
  mass ρ (s.substitution.types.map Prod.fst) s.nextType

theorem StateModels.emit {ρ s} (hs : StateModels ρ s) (r : RewriteRule) {cs}
    (hc : Models ρ cs) : StateModels ρ (s.emit r cs) :=
  ⟨models_append.mpr ⟨hc, hs.1⟩, hs.2⟩

theorem StateModels.retain {ρ s} (hs : StateModels ρ s) (r : RewriteRule) {c}
    (hc : Satisfies ρ c) : StateModels ρ (s.retain r c) := by
  unfold SolverState.retain
  split
  · exact hs
  · exact ⟨hs.1, models_cons.mpr ⟨hc, hs.2⟩⟩

theorem stepMode_models {ρ s a b t} (hs : StateModels ρ s)
    (h : stepMode s a b = .success t) : StateModels ρ t := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  all_goals first
    | exact hs.emit _ (by simp [Models, Satisfies])
    | exact hs.retain _ trivial
    | exact (hs.retain _ (c := .mode _ _) trivial).emit _ (by simp [Models, Satisfies])

theorem expansion_progress {ρ : TypeVar → Ty} {s : SolverState} (hs : s.Fresh)
    {a n old} (ha : Shape a (s.skeleton a).1) (hn : n < s.nextType)
    (hk : n ∉ s.substitution.types.map Prod.fst)
    (he : ρ (.flex n) = a.shapeUnder ρ) (hm : StateModels ρ s)
    (ho : Satisfies ρ old) (hb : old.Bounded s.nextType s.nextMode) :
    ∃ u η, solverStep ((s.skeleton a).2.emit .expand
        [.equal (.flex n) (s.skeleton a).1, old]) = .success u ∧
      StateModels η u ∧ weight η u < weight ρ s := by
  refine ⟨_, expand ρ s.nextType a, hs.skeleton_eliminated ha hn hk old, ?_, ?_⟩
  · constructor
    · apply models_singleType (by rw [expand_below ρ a hn, expand_skeleton]; exact he)
      simp only [models_append, models_cons, (s.skeleton_frame a).1, (s.skeleton_frame a).2.1]
      exact ⟨⟨⟨(satisfies_expand ρ a hb).mpr ho, models_expand a hs.pending hm.1⟩,
        models_expand a hs.bounds hm.2⟩, models_wellFormedBounds _ _⟩
    · simp [Models]
  · simp only [weight, SolverState.skeleton_substitution, Substitution.extendType_keys _ hk]
    apply mass_expansion ρ s _ ha hn hk _ he
    intro k hk
    obtain ⟨⟨_, t⟩, ht, rfl⟩ := List.mem_map.mp hk
    exact (hs.substitution.types _ _ ht).1

theorem models_of_ground {ρ cs} (h : GroundModels ρ cs) :
    Models (fun v => (ρ.types v).shape) cs := by
  intro c hc
  have hs := h c hc
  cases c
  case mode | defined => trivial
  case sub a b =>
    obtain ⟨x, y, hx, hy, hxy⟩ := hs
    exact (TypeExpr.realize_shape hx).trans ((GroundOrder.of_subtype hxy).shape_eq.trans
      (TypeExpr.realize_shape hy).symm)
  case equiv a b =>
    obtain ⟨x, y, hx, hy, hxy, _⟩ := hs
    exact (TypeExpr.realize_shape hx).trans ((GroundOrder.of_subtype hxy).shape_eq.trans
      (TypeExpr.realize_shape hy).symm)
  case equal v a =>
    obtain ⟨y, hy, hxy, _⟩ := hs
    exact (GroundOrder.of_subtype hxy).shape_eq.trans (TypeExpr.realize_shape hy).symm

end SolverShape
end ModalityInference
