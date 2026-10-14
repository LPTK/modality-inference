import ModalityInference.Proofs.RefinedContexts

/-! Compatible declarative joins for the three operands of reuse. -/
namespace ModalityInference

theorem Scheme.modal_many_subsumes (s : Scheme) (Δ : Bounds) :
    Subsumes Δ (s.modal (.const Mode.many)) s := by
  refine Subsumes.of_instances (fun Ξ θ hi hb => ⟨θ, hi, hb, ?_⟩)
  exact (Subtype.congr .refl (.valid fun _ _ => ⟨_, _, rfl, rfl, by decide⟩)).trans .identity

theorem Scheme.refineMode_lockAll_subsumes_shared_plain {s : Scheme} {p : Nat}
    {ms : List ModExpr} (hp : s.freshModeIndex ≤ p)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars) (Δ : Bounds) :
    Subsumes Δ ((s.refineMode p).lockAll ms).withAssumptions
      ((s.share.refineMode p).lockAll ms).withAssumptions := by
  refine Subsumes.of_instances (fun Ξ θ hi hb => ?_)
  obtain ⟨τ, hτ, hbounds, hsub, _⟩ :=
    s.refined_shared_lockAll_instance hi hp hp hm hm hb.of_subst_assumptions
  exact ⟨τ, hτ, hbounds.subst_assumptions, hsub⟩

theorem Scheme.refineMode_lockAll_subsumes_shared_twice {s : Scheme} {p : Nat}
    {ms : List ModExpr} (hp : s.freshModeIndex ≤ p)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars) (Δ : Bounds) :
    Subsumes Δ ((s.refineMode p).lockAll ms).withAssumptions
      ((((s.share.refineMode p).lockAll ms).withAssumptions.modal (.const Mode.many)).modal (.const Mode.many)) := by
  refine Subsumes.of_instances (fun Ξ θ hi hb => ?_)
  obtain ⟨τ, hτ, hbounds, hsub, _⟩ :=
    s.refined_shared_lockAll_instance hi hp hp hm hm hb.of_subst_assumptions
  have hmany := Scheme.refined_shared_lockAll_many hb.of_subst_assumptions
  exact ⟨τ, hτ, hbounds.subst_assumptions,
    hsub.trans (hmany.trans (hmany.modal_many (m := .const Mode.many) (fun _ _ => rfl)))⟩

def Context.many (Γ : Context) : Context := Γ.map (Option.map (fun s => s.modal (.const Mode.many)))

theorem ContextJoin.many {Δ Γ Γ₁ Γ₂} (h : ContextJoin Δ Γ₁ Γ₂ Γ) :
    ContextJoin Δ Γ₁.many Γ₂.many Γ.many := by
  induction h with
  | nil => exact .nil
  | unused h ih => exact .unused ih
  | left h ih => exact .left ih
  | right h ih => exact .right ih
  | shared h hf ha ih => exact .shared ih hf (ha.modal_aliased (fun _ _ => rfl))

theorem UsageSplit.declarative_refined_reuse {Γ Γ₁ Γ₂ Γ₃ Γ₂₃ : AlgorithmicContext}
    {Δ : Bounds} {p : Nat} (h1 : UsageSplit Γ Γ₁ Γ₂₃) (h2 : UsageSplit Γ₂₃ Γ₂ Γ₃)
    (hf : Γ.RefinementFresh p Δ) (ms : List ModExpr)
    (hm : ∀ m ∈ ms, .flex p ∉ m.vars) :
    ∃ left middle right joined23 joined,
      ContextLe Δ left (Γ₁.refinedContext p ms) ∧
      ContextLe Δ middle (Γ₂.refinedContext p ms) ∧
      ContextLe Δ right (Γ₃.refinedContext p ms) ∧
      ContextJoin Δ middle right joined23 ∧ ContextJoin Δ left joined23 joined ∧
      ContextLe Δ (Γ.refinedContext p ms) joined := by
  induction h1 generalizing Γ₂ Γ₃ ms <;> cases h2
  case share.share Γ Γ₁ Γ₂₃ s shared h1 he ih Γ₂ Γ₃ shared₂ he₂ h2 =>
    subst shared shared₂
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    let sh := ((s.share.refineMode p).lockAll ms).withAssumptions
    have hj := s.refined_shared_lockAll_join (ms := ms) (hf.1 s List.mem_cons_self).2
    have hplain := s.share.refineMode_lockAll_subsumes_shared_plain
      (by simpa only [Scheme.share_freshModeIndex] using (hf.1 s List.mem_cons_self).1) hm Δ
    exact ⟨some (sh.modal (.const Mode.many)) :: left, some sh :: middle, some sh :: right,
      some (sh.modal (.const Mode.many)) :: joined23,
      some ((sh.modal (.const Mode.many)).modal (.const Mode.many)) :: joined,
      .keep hl (sh.modal_many_subsumes Δ), .keep hm' hplain, .keep hr hplain,
      hj.append hj2, hj.many.append hj1,
      .keep hc (s.refineMode_lockAll_subsumes_shared_twice (hf.1 s List.mem_cons_self).1 hm Δ)⟩
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
        .keep hl (.refl _ _), .drop hm', .drop hr, .unused hj2, .left hj1, .keep hc (.refl _ _)⟩
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
          some head :: joined, .drop hl, .keep hm' (.refl _ _), .drop hr,
          .left hj2, .right hj1, .keep hc (.refl _ _)⟩
      | exact ⟨none :: left, none :: middle, some head :: right, some head :: joined23,
          some head :: joined, .drop hl, .drop hm', .keep hr (.refl _ _),
          .right hj2, .right hj1, .keep hc (.refl _ _)⟩
  case right.share Γ Γ₁ Γ₂₃ h1 ih Γ₂ Γ₃ s shared he h2 =>
    subst shared
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    let sh := ((s.share.refineMode p).lockAll ms).withAssumptions
    exact ⟨none :: left, some sh :: middle, some sh :: right,
      some (sh.modal (.const Mode.many)) :: joined23, some (sh.modal (.const Mode.many)) :: joined,
      .drop hl, .keep hm' (.refl _ _), .keep hr (.refl _ _),
      (s.refined_shared_lockAll_join (ms := ms) (hf.1 s List.mem_cons_self).2).append hj2,
      .right hj1, .keep hc (s.refineMode_lockAll_subsumes_refined_shared
        (hf.1 s List.mem_cons_self).1 (hf.1 s List.mem_cons_self).1 hm hm Δ)⟩
  case share.drop Γ Γ₁ Γ₂₃ s shared h1 he ih Γ₂ Γ₃ h2 =>
    subst shared
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    let sh := ((s.share.refineMode p).lockAll ms).withAssumptions
    exact ⟨some sh :: left, none :: middle, none :: right, none :: joined23, some sh :: joined,
      .keep hl (.refl _ _), .drop hm', .drop hr, .unused hj2, .left hj1,
      .keep hc (s.refineMode_lockAll_subsumes_shared_plain (hf.1 s List.mem_cons_self).1 hm Δ)⟩
  case share.left Γ Γ₁ Γ₂₃ s shared h1 he ih Γ₂ Γ₃ h2
     | share.right Γ Γ₁ Γ₂₃ s shared h1 he ih Γ₂ Γ₃ h2 =>
    subst shared
    obtain ⟨left, middle, right, joined23, joined, hl, hm', hr, hj2, hj1, hc⟩ :=
      ih h2 hf.tail ms hm
    let sh := ((s.share.refineMode p).lockAll ms).withAssumptions
    have hjoin := (s.refined_shared_lockAll_join (ms := ms) (hf.1 s List.mem_cons_self).2).append hj1
    have hsource := ContextLe.keep hc (s.refineMode_lockAll_subsumes_refined_shared
      (hf.1 s List.mem_cons_self).1 (hf.1 s List.mem_cons_self).1 hm hm Δ)
    first
    | exact ⟨some sh :: left, some sh :: middle, none :: right, some sh :: joined23,
        some (sh.modal (.const Mode.many)) :: joined,
        .keep hl (.refl _ _), .keep hm' (.refl _ _), .drop hr, .left hj2, hjoin, hsource⟩
    | exact ⟨some sh :: left, none :: middle, some sh :: right, some sh :: joined23,
        some (sh.modal (.const Mode.many)) :: joined,
        .keep hl (.refl _ _), .drop hm', .keep hr (.refl _ _), .right hj2, hjoin, hsource⟩

end ModalityInference
