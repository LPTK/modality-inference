import ModalityInference.Proofs.ComparisonReduction

/-! Successful reduction leaves only opaque type inequalities and scalar
obligations. This closure fact turns their separate semantic certificates into
the residual state invariant used by reduction reconstruction. -/
namespace ModalityInference.ComparisonReduction

def Scalar : Constraint → Prop
  | .mode _ _ | .defined _ => True
  | _ => False

def ScalarModes (s : State) : Prop := ∀ c ∈ s.modes, Scalar c

theorem initial_scalarModes (bounds : Bounds) (source target : Ty) :
    ScalarModes (initial bounds source target) := by
  intro c hc
  obtain ⟨_, hc⟩ := List.mem_filter.mp hc
  cases c <;> simp_all [Scalar]

theorem step_scalarModes {s next : State} (h : step s = .success next)
    (hs : ScalarModes s) : ScalarModes next := by
  unfold step at h
  repeat' first
    | contradiction
    | (cases h; exact hs)
    | (split at h <;> try simp only at h)
  all_goals cases h
  all_goals simpa only [ScalarModes, List.forall_mem_cons, Scalar, true_and] using hs

theorem run_scalarModes {fuel : Nat} {s next : State} (h : run fuel s = .success next)
    (hs : ScalarModes s) : ScalarModes next := by
  induction fuel generalizing s with
  | zero => contradiction
  | succ fuel ih =>
    simp only [run, bind, RunResult.bind] at h
    split at h
    · cases h; exact hs
    · cases hstep : step s <;> simp only [hstep] at h <;> try contradiction
      exact ih h (step_scalarModes hstep hs)

theorem prepare_closed {fuel : Nat} {p : SchemePreparation.Prepared}
    {templates : ComparisonSkeleton.Templates} {bare : List Nat}
    {known : List ModExpr} {shared : Bool} {result : State}
    (h : prepare fuel p templates bare known shared = .success result) :
    result.pending = [] ∧ result.bareBounds = [] ∧ ScalarModes result := by
  simp only [prepare, bind, RunResult.bind] at h
  split at h
  · next reduced hfirst =>
    have hscalar := run_scalarModes hfirst (by
      exact initial_scalarModes (templates.substitution.bounds p.sourceBounds)
        (templates.substitution.ty p.sourceType) p.targetType)
    refine ⟨run_pending_empty h, ?_, run_scalarModes h (by exact hscalar)⟩
    have hs := run_bare_scope h (by simp)
    have hm := (run_metadata h).2.2.1
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro b hb
    simpa only [hm, List.not_mem_nil] using hs b hb
  · contradiction
  · contradiction

theorem scalarModes_entails {Δ : Bounds} {σ : CompareSubstitution} {s : State}
    (hs : ScalarModes s)
    (hm : ∀ a b, Constraint.mode a b ∈ s.modes →
      Submode Δ (a.subst σ.mode) (b.subst σ.mode))
    (hd : ∀ m, Constraint.defined m ∈ s.modes →
      Entails Δ (.defined (m.subst σ.mode))) : AlgebraEntailsAll Δ (σ.bounds s.modes) := by
  intro c hc
  obtain ⟨d, hd', rfl⟩ := List.mem_map.mp hc
  have hscalar := hs d hd'
  cases d <;> try contradiction
  · exact hm _ _ hd'
  · exact hd _ hd'

theorem prepare_holds {Δ : Bounds} {σ : CompareSubstitution} {fuel : Nat}
    {p : SchemePreparation.Prepared} {templates : ComparisonSkeleton.Templates}
    {bare : List Nat} {known : List ModExpr} {shared : Bool} {result : State}
    (h : prepare fuel p templates bare known shared = .success result)
    (hi : ∀ pair ∈ result.inequalities, PairHolds Δ σ pair)
    (hm : ∀ a b, Constraint.mode a b ∈ result.modes →
      Submode Δ (a.subst σ.mode) (b.subst σ.mode))
    (hd : ∀ m, Constraint.defined m ∈ result.modes →
      Entails Δ (.defined (m.subst σ.mode))) : Holds Δ σ result := by
  obtain ⟨hp, hb, hs⟩ := prepare_closed h
  exact ⟨by simp only [hp, List.not_mem_nil, false_implies, implies_true], hi,
    scalarModes_entails hs hm hd,
    by simp only [hb, List.not_mem_nil, false_implies, implies_true]⟩

end ModalityInference.ComparisonReduction
