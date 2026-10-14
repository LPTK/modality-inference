import ModalityInference.Proofs.SolverShape
import ModalityInference.Proofs.ModeWorklist

/-! Termination of the mixed worklist under a finite shape model. -/
namespace ModalityInference
namespace SolverShape

theorem stepType_progress {ρ : TypeVar → Ty} {s : SolverState} (hs : s.Fresh)
    {a b t c} (ha : a.Bounded s.nextType s.nextMode) (hb : b.Bounded s.nextType s.nextMode)
    (hf : ∀ k ∈ s.substitution.types.map Prod.fst,
      .flex k ∉ a.typeVars ∧ .flex k ∉ b.typeVars)
    (hm : StateModels ρ s) (hc : a.shapeUnder ρ = b.shapeUnder ρ)
    (he : c.normalize = .sub a b) (h : stepType s a b = .success t) :
    (StateModels ρ t ∧ weight ρ t = weight ρ s ∧
      WorklistOrder.Lt t.pending (c :: s.pending)) ∨
    ∃ u η, solverStep t = .success u ∧ StateModels η u ∧ weight η u < weight ρ s := by
  have ho : a.outer.1.shapeUnder ρ = b.outer.1.shapeUnder ρ := by simpa using hc
  have hmodel : Satisfies ρ (.sub (.modal a.outer.1 a.outer.2.normalize)
      (.modal b.outer.1 b.outer.2.normalize)) := by simpa [Satisfies, TypeExpr.shapeUnder] using hc
  have hbound : (Constraint.sub (.modal a.outer.1 a.outer.2.normalize)
      (.modal b.outer.1 b.outer.2.normalize)).Bounded s.nextType s.nextMode :=
    ⟨⟨ha.outer.1, ha.outer.2.normalize⟩, ⟨hb.outer.1, hb.outer.2.normalize⟩⟩
  simp only [stepType, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h
  case h_2.isFalse.refl =>
    rename_i x y n hva hnv hocc
    right
    apply expansion_progress hs (s.skeleton_shape hnv b.outer_not_modal)
    · simpa only [hva, TypeExpr.Bounded, TypeVar.index] using ha.outer.1
    · exact fun hk => (hf n hk).1 (TypeExpr.outer_var_mem hva)
    · simpa only [hva, TypeExpr.shapeUnder] using ho
    · exact hm
    · exact hmodel
    · exact hbound
  case h_3.isFalse.refl =>
    rename_i x y n hvb hnv hnf hocc
    right
    apply expansion_progress hs (s.skeleton_shape hnv a.outer_not_modal)
    · simpa only [hvb, TypeExpr.Bounded, TypeVar.index] using hb.outer.1
    · exact fun hk => (hf n hk).2 (TypeExpr.outer_var_mem hvb)
    · simpa only [hvb, TypeExpr.shapeUnder] using ho.symm
    · exact hm
    · exact hmodel
    · exact hbound
  all_goals left; refine ⟨?_, rfl, ?_⟩
  all_goals first
    | solve | exact hm.emit _ (by simp_all [Models, Satisfies, TypeExpr.shapeUnder])
    | solve | exact (hm.retain _ hmodel).emit _ (by simp [Models, Satisfies])
    | skip
  all_goals apply WorklistOrder.replace_head
  all_goals intro d hd; apply WorklistOrder.rank_type
  all_goals rw [← Constraint.normalize_typeRank c, he]
  all_goals revert d
  all_goals simp [Constraint.typeRank, ← a.outer_shapeSize, ← b.outer_shapeSize,
    *, TypeExpr.shapeSize, or_imp, forall_and]
  all_goals grind

theorem stepMode_weight {ρ s a b t} (h : stepMode s a b = .success t) :
    weight ρ t = weight ρ s := by
  simp only [stepMode, bind, pure, RunResult.bind] at h
  repeat' split at h
  all_goals cases h <;> rfl

def Descends (ρ : TypeVar → Ty) (s : SolverState) (η : TypeVar → Ty) (t : SolverState) : Prop :=
  Prod.Lex (· < ·) WorklistOrder.Lt (weight η t, t.pending) (weight ρ s, s.pending)

theorem descends_weight {ρ s η t} (h : weight η t < weight ρ s) : Descends ρ s η t :=
  Prod.Lex.left _ _ h

theorem descends_pending {ρ s η t} (he : weight η t = weight ρ s)
    (h : WorklistOrder.Lt t.pending s.pending) : Descends ρ s η t := by
  unfold Descends
  rw [he]
  exact Prod.Lex.right _ h

theorem solverStep_progress {ρ : TypeVar → Ty} {s t : SolverState}
    (hs : s.Fresh) (hu : s.Unbound) (hσ : s.substitution.Acyclic)
    (hp : s.pending ≠ []) (hm : StateModels ρ s) (h : solverStep s = .success t) :
    (∃ η, StateModels η t ∧ Descends ρ s η t) ∨
    ∃ u η, solverStep t = .success u ∧ StateModels η u ∧ Descends ρ s η u := by
  have hnorm : ∀ c rest, s.pending = c :: rest →
      Satisfies ρ (s.substitution.constraint c).normalize := by
    intro c rest he
    rw [(hu.pending c (by simp [he])).fixed hu.modes]
    exact (satisfies_normalize ρ c).mpr (hm.1 c (by simp [he]))
  have htail : ∀ c rest seen, s.pending = c :: rest →
      StateModels ρ {s with pending := rest, seen := seen} :=
    fun c rest _ he => ⟨fun d hd => hm.1 d (by simp [he, hd]), hm.2⟩
  simp only [solverStep, bind, pure, RunResult.bind] at h
  repeat' split at h
  case h_2 =>
    rename_i pending c rest hpend hseen normalized a b he
    have hfix := (hu.pending c (by simp [hpend])).fixed hu.modes
    rcases stepType_progress (hs.advance hpend (by simp))
        (he ▸ hs.normalized_head hpend).1 (he ▸ hs.normalized_head hpend).2
        (s.substitution.normalized_sub_fresh hσ he) (htail c rest _ hpend)
        (by simpa only [he, Satisfies] using hnorm c rest hpend)
        (hfix ▸ he) h with ⟨htm, hw, hr⟩ | ⟨u, η, hh, hum, hw⟩
    · exact .inl ⟨ρ, htm, descends_pending hw (by simpa only [hpend] using hr)⟩
    · exact .inr ⟨u, η, hh, hum, descends_weight hw⟩
  case h_3 =>
    rename_i pending c rest hpend hseen normalized a b he
    have hfix := (hu.pending c (by simp [hpend])).fixed hu.modes
    refine .inl ⟨ρ, stepMode_models (htail c rest _ hpend) h, descends_pending ?_ ?_⟩
    · have hw := stepMode_weight (ρ := ρ) h
      exact hw
    · simpa only [hpend] using WorklistOrder.stepMode_decreases (hfix ▸ he) h
  all_goals cases h
  all_goals try exact False.elim (hp ‹s.pending = []›)
  case h_2.isFalse.isFalse.refl =>
    rename_i pending c rest hpend hseen normalized a v n he hrefl hocc
    have heq : ρ (.flex n) = a.shapeUnder ρ := by
      simpa only [he, Satisfies] using hnorm c rest hpend
    have hk := (s.substitution.normalized_equal_fresh hσ he).1
    have hn : n < s.nextType := (he ▸ hs.normalized_head hpend).1
    refine .inl ⟨ρ, ⟨?_, by simp [Models]⟩, descends_weight ?_⟩
    · apply models_singleType heq
      exact models_append.mpr ⟨models_append.mpr ⟨(htail c rest [] hpend).1, hm.2⟩,
        models_wellFormedBounds ρ a⟩
    · have hh := mass_eliminate ρ (s.substitution.types.map Prod.fst) hn hk
      have hpos := (ρ (.flex n)).shapeSize_pos
      simp only [weight, Substitution.extendType_keys _ hk]
      omega
  all_goals left; refine ⟨ρ, ?_, descends_pending rfl ?_⟩
  all_goals first
    | exact htail _ _ _ ‹s.pending = _ :: _›
    | solve |
        apply (htail _ _ _ ‹s.pending = _ :: _›).emit
        have hh := hnorm _ _ ‹s.pending = _ :: _›
        simp_all [Models, Satisfies, eq_comm]
    | exact (htail _ _ _ ‹s.pending = _ :: _›).retain _ (hnorm _ _ ‹s.pending = _ :: _›)
    | skip
  case h_4.isTrue.isTrue.refl.h.refine_1 =>
    exact ⟨fun d hd => hm.1 d (by rw [‹s.pending = _ :: _›]; exact List.mem_cons_of_mem _ hd), hm.2⟩
  case h_2.isFalse.isTrue.refl.h.refine_1 =>
    rename_i pending c rest hpend hseen normalized a v n he hrefl hocc
    have hh := hnorm c rest hpend
    rw [he] at hh
    apply (htail c rest _ hpend).emit
    simpa [Models, Satisfies, TypeExpr.shapeUnder] using And.intro hh (Eq.symm hh)
  all_goals rw [‹s.pending = _ :: _›]
  all_goals try exact WorklistOrder.tail _ _
  case h_1.refl.h.refine_2 =>
    rename_i pending c rest hpend hseen normalized a b he
    have hfix := (hu.pending c (by simp [hpend])).fixed hu.modes
    apply WorklistOrder.replace_head
    intro d hd
    apply WorklistOrder.rank_type
    rw [← Constraint.normalize_typeRank c, ← hfix, he]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [Constraint.typeRank, Nat.add_comm]
  case h_2.isFalse.isTrue.refl.h.refine_2 =>
    rename_i pending c rest hpend hseen normalized a v n he hrefl hocc
    have hfix := (hu.pending c (by simp [hpend])).fixed hu.modes
    apply WorklistOrder.replace_head
    intro d hd
    apply WorklistOrder.rank_type
    rw [← Constraint.normalize_typeRank c, ← hfix, he]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> simp [Constraint.typeRank, TypeExpr.shapeSize, Nat.add_comm]

theorem descends_wellFounded : WellFounded
    (fun q p : SolverState × (TypeVar → Ty) => Descends p.2 p.1 q.2 q.1) :=
  InvImage.wf (fun p : SolverState × (TypeVar → Ty) => (weight p.2 p.1, p.1.pending))
    (Nat.lt_wfRel.wf.prod_lex WorklistOrder.wellFounded)

theorem eventually_of_step {s t : SolverState} (he : solverStep s = .success t)
    (ht : ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, runWorklist fuel t = result) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, runWorklist fuel s = result := by
  by_cases hp : s.pending = []
  · refine ⟨1, .success s, by simp, fun fuel hf => ?_⟩
    cases fuel with
    | zero => omega
    | succ fuel => simp [runWorklist, hp]
  obtain ⟨n, result, hn, hr⟩ := ht
  refine ⟨n + 1, result, hn, fun fuel hf => ?_⟩
  cases fuel with
  | zero => omega
  | succ fuel => simpa [runWorklist, hp, he, bind, RunResult.bind] using hr fuel (by omega)

theorem runWorklist_eventually {ρ : TypeVar → Ty} {s : SolverState}
    (hs : s.Fresh) (hu : s.Unbound) (hσ : s.substitution.Acyclic) (hm : StateModels ρ s) :
    ∃ n result, result ≠ .exhausted ∧ ∀ fuel ≥ n, runWorklist fuel s = result := by
  generalize hp : (s, ρ) = p
  induction p using descends_wellFounded.induction generalizing s ρ with
  | h p ih =>
    subst p
    by_cases hp : s.pending = []
    · refine ⟨1, .success s, by simp, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel => simp [runWorklist, hp]
    cases he : solverStep s with
    | exhausted => exact False.elim (solverStep_ne_exhausted s he)
    | rejected reason =>
      refine ⟨1, .rejected reason, by simp, fun fuel hf => ?_⟩
      cases fuel with
      | zero => omega
      | succ fuel => simp [runWorklist, hp, he, bind, RunResult.bind]
    | success t =>
      have htf := solverStep_fresh hs he
      have htu := solverStep_unbound hu hs hσ he
      have htσ := solverStep_acyclic hσ he
      apply eventually_of_step he
      rcases solverStep_progress hs hu hσ hp hm he with ⟨η, htm, hlt⟩ | ⟨u, η, hh, hum, hlt⟩
      · exact ih (t, η) hlt htf htu htσ htm rfl
      · apply eventually_of_step hh
        exact ih (u, η) hlt (solverStep_fresh htf hh) (solverStep_unbound htu htf htσ hh)
          (solverStep_acyclic htσ hh) hum rfl

end SolverShape
end ModalityInference
