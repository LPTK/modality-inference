import ModalityInference.Proofs.GuardedRefinedContexts

/-! Guarded comparisons for the three shared operands of reuse. -/
namespace ModalityInference

theorem UsageSplit.declarative_refined_guarded_reuse {Γ Γ₁ Γ₂ Γ₃ Γ₂₃ : AlgorithmicContext}
    {Δ : Bounds} {p : Nat} (h1 : UsageSplit Γ Γ₁ Γ₂₃) (h2 : UsageSplit Γ₂₃ Γ₂ Γ₃)
    (hf : Γ.RefinementFresh p Δ) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars) :
    ∃ left middle right joined23 joined,
      GuardedContextLe Δ left (Γ₁.refinedContext p ms) ∧
      GuardedContextLe Δ middle (Γ₂.refinedContext p ms) ∧
      GuardedContextLe Δ right (Γ₃.refinedContext p ms) ∧
      ContextJoin Δ middle right joined23 ∧ ContextJoin Δ left joined23 joined ∧
      GuardedContextLe Δ (Γ.refinedContext p ms) joined := by
  induction h1 generalizing Γ₂ Γ₃ ms <;> cases h2
  case share.share Γ Γ₁ Γ₂₃ s shared h1 he ih Γ₂ Γ₃ shared₂ he₂ h2 =>
    subst shared shared₂
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    let sh := ((s.share.refineMode p).lockAll ms).withAssumptions
    have hj := s.refined_shared_lockAll_join (ms := ms) (hf.1 s List.mem_cons_self).2
    have hplain := (s.share.refineMode_lockAll_subsumes_shared_plain
      (by simpa only [Scheme.share_freshModeIndex] using (hf.1 s List.mem_cons_self).1) hm Δ).under_of_guardsBody
        (s.share.refined_lock_guardsBody p ms)
    exact ⟨some (sh.modal (.const Mode.many)) :: left, some sh :: middle, some sh :: right,
      some (sh.modal (.const Mode.many)) :: joined23,
      some ((sh.modal (.const Mode.many)).modal (.const Mode.many)) :: joined,
      .keep hl ((sh.modal_many_subsumes Δ).under_of_guardsBody
        ((s.share.refined_lock_guardsBody p ms).modal_const Mode.many)), .keep hm' hplain, .keep hr hplain,
      hj.append hj2, hj.many.append hj1,
      .keep hc ((s.refineMode_lockAll_subsumes_shared_twice (hf.1 s List.mem_cons_self).1 hm Δ).under_of_guardsBody
        (s.refined_lock_guardsBody p ms))⟩
  case nil.nil => exact ⟨[], [], [], [], [], .nil, .nil, .nil, .nil, .nil, .nil⟩
  case lock.lock Γ Γ₁ Γ₂₃ m h1 ih Γ₂ Γ₃ h2 =>
    apply ih h2 hf.tail (ms ++ [m])
    simpa [List.mem_append, or_imp, forall_and] using
      And.intro hm (hf.2 m List.mem_cons_self)
  case drop.drop Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2
     | drop.left Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2
     | drop.right Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2
     | right.drop Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2 =>
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    exact ⟨none :: left, none :: middle, none :: right, none :: joined23, none :: joined,
      .drop hl, .drop hm', .drop hr, .unused hj2, .unused hj1, .drop hc⟩
  case left.drop Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2
     | left.left Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2
     | left.right Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2 =>
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    cases s with
    | none =>
      exact ⟨none :: left, none :: middle, none :: right, none :: joined23, none :: joined,
        .drop hl, .drop hm', .drop hr, .unused hj2, .unused hj1, .drop hc⟩
    | some s =>
      exact ⟨some ((s.refineMode p).lockAll ms).withAssumptions :: left,
        none :: middle, none :: right, none :: joined23,
        some ((s.refineMode p).lockAll ms).withAssumptions :: joined,
        .same hl, .drop hm', .drop hr, .unused hj2, .left hj1, .same hc⟩
  case right.left Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2
     | right.right Γ Γ₁ Γ₂₃ s h1 ih Γ₂ Γ₃ h2 =>
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    cases s with
    | none =>
      exact ⟨none :: left, none :: middle, none :: right, none :: joined23, none :: joined,
        .drop hl, .drop hm', .drop hr, .unused hj2, .unused hj1, .drop hc⟩
    | some s =>
      let head := ((s.refineMode p).lockAll ms).withAssumptions
      first
      | exact ⟨none :: left, some head :: middle, none :: right, some head :: joined23,
          some head :: joined, .drop hl, .same hm', .drop hr,
          .left hj2, .right hj1, .same hc⟩
      | exact ⟨none :: left, none :: middle, some head :: right, some head :: joined23,
          some head :: joined, .drop hl, .drop hm', .same hr,
          .right hj2, .right hj1, .same hc⟩
  case right.share Γ Γ₁ Γ₂₃ h1 ih Γ₂ Γ₃ s shared he h2 =>
    subst shared
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    let sh := ((s.share.refineMode p).lockAll ms).withAssumptions
    exact ⟨none :: left, some sh :: middle, some sh :: right,
      some (sh.modal (.const Mode.many)) :: joined23, some (sh.modal (.const Mode.many)) :: joined,
      .drop hl, .same hm', .same hr,
      (s.refined_shared_lockAll_join (ms := ms) (hf.1 s List.mem_cons_self).2).append hj2,
      .right hj1, .keep hc ((s.refineMode_lockAll_subsumes_refined_shared
        (hf.1 s List.mem_cons_self).1 (hf.1 s List.mem_cons_self).1 hm hm Δ).under_of_guardsBody
          (s.refined_lock_guardsBody p ms))⟩
  case share.drop Γ Γ₁ Γ₂₃ s shared h1 he ih Γ₂ Γ₃ h2 =>
    subst shared
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    let sh := ((s.share.refineMode p).lockAll ms).withAssumptions
    exact ⟨some sh :: left, none :: middle, none :: right, none :: joined23, some sh :: joined,
      .same hl, .drop hm', .drop hr, .unused hj2, .left hj1,
      .keep hc ((s.refineMode_lockAll_subsumes_shared_plain (hf.1 s List.mem_cons_self).1 hm Δ).under_of_guardsBody
        (s.refined_lock_guardsBody p ms))⟩
  case share.left Γ Γ₁ Γ₂₃ s shared h1 he ih Γ₂ Γ₃ h2
     | share.right Γ Γ₁ Γ₂₃ s shared h1 he ih Γ₂ Γ₃ h2 =>
    subst shared
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    let sh := ((s.share.refineMode p).lockAll ms).withAssumptions
    have hjoin := (s.refined_shared_lockAll_join (ms := ms) (hf.1 s List.mem_cons_self).2).append hj1
    have hsource := GuardedContextLe.keep hc ((s.refineMode_lockAll_subsumes_refined_shared
      (hf.1 s List.mem_cons_self).1 (hf.1 s List.mem_cons_self).1 hm hm Δ).under_of_guardsBody
        (s.refined_lock_guardsBody p ms))
    first
    | exact ⟨some sh :: left, some sh :: middle, none :: right, some sh :: joined23,
        some (sh.modal (.const Mode.many)) :: joined,
        .same hl, .same hm', .drop hr, .left hj2, hjoin, hsource⟩
    | exact ⟨some sh :: left, none :: middle, some sh :: right, some sh :: joined23,
        some (sh.modal (.const Mode.many)) :: joined,
        .same hl, .drop hm', .same hr, .right hj2, hjoin, hsource⟩

end ModalityInference
