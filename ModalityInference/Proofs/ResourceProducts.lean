import ModalityInference.Proofs.ResourceApplication
import ModalityInference.Proofs.AllocationCells

/-! Product construction preserves complete field interpretations and separates
the allocated cell from both fields. Heap and stack allocation use the same
resource contract, with stack liveness supplied by the current world. -/
namespace ModalityInference

theorem ResourceInterpretation.pair {w : World} {a b m l x y first second}
    (hl : w.Live l) (hlocal : m.isLocal = true ∨ HeapLocation l)
    (hx : ResourceInterpretation w a m x first)
    (hy : ResourceInterpretation w b m y second)
    (hcx : Disjoint (cellResources m l) first)
    (hcy : Disjoint (cellResources m l) second) (hxy : Disjoint first second) :
    ResourceInterpretation w (.prod a b m) Mode.identity (.pair l x y)
      (cellResources m l ∪ first ∪ second) := by
  simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity]
  refine ⟨?_, ?_, hlocal, first, second, hx, hy, hcx, hcy, hxy, rfl⟩
  · intro k hk
    cases hk with
    | pairCell => exact hl
    | pairLeft hk => exact hx.valid k hk
    | pairRight hk => exact hy.valid k hk
  · intro k hk
    rcases hk with (hk | hk) | hk
    · obtain rfl := Set.mem_singleton_iff.mp (cellResources_subset m l hk)
      exact .pairCell
    · exact .pairLeft (hx.references k hk)
    · exact .pairRight (hy.references k hk)

theorem Typing.resource_pair {Δ t u a b m} {Γ Γ₁ Γ₂ : Context}
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ) {ρ} (hΔ : GroundModels ρ Δ)
    (iht : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₁.restrict t.freeVars) γ reserved →
      (TypeExpr.modal a m).realize ρ = some ground →
      ResourceSemanticEvaluation w γ t ground (ContextResources (Γ₁.restrict t.freeVars) reserved))
    (ihu : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₂.restrict u.freeVars) γ reserved →
      (TypeExpr.modal b m).realize ρ = some ground →
      ResourceSemanticEvaluation w γ u ground (ContextResources (Γ₂.restrict u.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (Term.pair t u).freeVars) γ reserved)
    (ha : (TypeExpr.modal (.prod a b) m).realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.pair t u) ground
      (ContextResources (Γ.restrict (Term.pair t u).freeVars) reserved) := by
  cases ha' : a.realize ρ <;> cases hb' : b.realize ρ <;>
    cases hm' : m.eval (some ∘ ρ.modes) <;>
    simp [TypeExpr.realize, ha', hb', hm', GroundTy.modal] at ha
  rename_i firstTy secondTy n
  subst ground
  obtain ⟨left, right, hleft, hright, hl, hr, hd⟩ :=
    hj.resource_used (X := t.freeVars) (Y := u.freeVars) hΔ hγ
  intro supplies hsup
  obtain ⟨x, first, hex, hx, hfirst⟩ := iht (ground := firstTy.modal n) hleft
    (by simp [TypeExpr.realize, ha', hm'])
    (supplies.afterHeap.branch 2 0) (hsup.afterHeap.branch (by decide) 0)
  obtain ⟨y, second, hey, hy, hsecond⟩ := ihu (ground := secondTy.modal n) hright
    (by simp [TypeExpr.realize, hb', hm'])
    (supplies.afterHeap.branch 2 1) (hsup.afterHeap.branch (by decide) 1)
  have hxy := hsup.afterHeap.separate_branches hleft.references hright.references hd
    (by decide) (by decide) (by decide) hfirst hsecond
  have hcx := hsup.disjoint_fresh_cell (m := n) supplies.heap_fresh
    (fun hf => supplies.heap_not_fresh_afterHeap hsup.1 (Supplies.fresh_branch hf))
    hleft.references hfirst
  have hcy := hsup.disjoint_fresh_cell (m := n) supplies.heap_fresh
    (fun hf => supplies.heap_not_fresh_afterHeap hsup.1 (Supplies.fresh_branch hf))
    hright.references hsecond
  refine ⟨_, _, .pair hex hey, ResourceInterpretation.pair trivial (Or.inr trivial)
    (by simpa using ResourceInterpretation.modal_iff.mp hx)
    (by simpa using ResourceInterpretation.modal_iff.mp hy) hcx hcy hxy, ?_⟩
  refine Set.union_subset (Set.union_subset ?_
    (hfirst.trans (Set.union_subset_union hl
      (fun _ h => Supplies.fresh_afterHeap (Supplies.fresh_branch h)))))
    (hsecond.trans (Set.union_subset_union hr
      (fun _ h => Supplies.fresh_afterHeap (Supplies.fresh_branch h))))
  intro l hl
  obtain rfl := Set.mem_singleton_iff.mp (cellResources_subset n _ hl)
  exact Or.inr supplies.heap_fresh

theorem Typing.resource_stackPair {Δ t u a b m n} {Γ Γ₁ Γ₂ : Context}
    (hj : ContextJoin Δ Γ₁ Γ₂ Γ)
    (hmn : Submode Δ m n) (hlocal : Submode Δ (.const Mode.localLower) n) {ρ} (hΔ : GroundModels ρ Δ)
    (iht : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₁.restrict t.freeVars) γ reserved →
      (TypeExpr.modal a m).realize ρ = some ground →
      ResourceSemanticEvaluation w γ t ground (ContextResources (Γ₁.restrict t.freeVars) reserved))
    (ihu : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ₂.restrict u.freeVars) γ reserved →
      (TypeExpr.modal b m).realize ρ = some ground →
      ResourceSemanticEvaluation w γ u ground (ContextResources (Γ₂.restrict u.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (Term.stackPair t u).freeVars) γ reserved)
    (ha : (TypeExpr.modal (.prod a b) n).realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.stackPair t u) ground
      (ContextResources (Γ.restrict (Term.stackPair t u).freeVars) reserved) := by
  cases ha' : a.realize ρ <;> cases hb' : b.realize ρ <;>
    cases hn' : n.eval (some ∘ ρ.modes) <;>
    simp [TypeExpr.realize, ha', hb', hn', GroundTy.modal] at ha
  rename_i firstTy secondTy q
  subst ground
  obtain ⟨p, q', hm', hn'', hpq⟩ := hmn.denote hΔ.modeModels
  have he : q' = q := Option.some.inj (hn''.symm.trans hn')
  subst q'
  have hq : q.isLocal = true := by
    have hh := hlocal.denote hΔ.modeModels
    simp only [ModExpr.Below, ModExpr.eval, hn', Option.some.injEq] at hh
    obtain ⟨_, _, rfl, rfl, hh⟩ := hh
    exact ((Mode.le_iff _ _).mp hh).1 rfl
  obtain ⟨left, right, hleft, hright, hl, hr, hd⟩ :=
    hj.resource_used (X := t.freeVars) (Y := u.freeVars) hΔ hγ
  intro supplies hsup
  obtain ⟨x, first, hex, hx, hfirst⟩ := iht (ground := firstTy.modal p) hleft
    (by simp [TypeExpr.realize, ha', hm'])
    (supplies.afterStack.branch 2 0) (hsup.afterStack.branch (by decide) 0)
  obtain ⟨y, second, hey, hy, hsecond⟩ := ihu (ground := secondTy.modal p) hright
    (by simp [TypeExpr.realize, hb', hm'])
    (supplies.afterStack.branch 2 1) (hsup.afterStack.branch (by decide) 1)
  obtain ⟨first', hfirst', hx'⟩ := ResourceInterpretation.mode_mono hpq
    (show ResourceInterpretation w firstTy p x first by
      simpa using ResourceInterpretation.modal_iff.mp hx)
  obtain ⟨second', hsecond', hy'⟩ := ResourceInterpretation.mode_mono hpq
    (show ResourceInterpretation w secondTy p y second by
      simpa using ResourceInterpretation.modal_iff.mp hy)
  replace hfirst := hfirst'.trans hfirst
  replace hsecond := hsecond'.trans hsecond
  have hxy := hsup.afterStack.separate_branches hleft.references hright.references hd
    (by decide) (by decide) (by decide) hfirst hsecond
  have hcx := hsup.disjoint_fresh_cell (m := q) supplies.stack_fresh
    (fun hf => supplies.stack_not_fresh_afterStack hsup.1 (Supplies.fresh_branch hf))
    hleft.references hfirst
  have hcy := hsup.disjoint_fresh_cell (m := q) supplies.stack_fresh
    (fun hf => supplies.stack_not_fresh_afterStack hsup.1 (Supplies.fresh_branch hf))
    hright.references hsecond
  refine ⟨_, _, .stackPair hex hey, ResourceInterpretation.pair hsup.2.1 (Or.inl hq)
    hx' hy' hcx hcy hxy, ?_⟩
  refine Set.union_subset (Set.union_subset ?_
    (hfirst.trans (Set.union_subset_union hl
      (fun _ h => Supplies.fresh_afterStack (Supplies.fresh_branch h)))))
    (hsecond.trans (Set.union_subset_union hr
      (fun _ h => Supplies.fresh_afterStack (Supplies.fresh_branch h))))
  intro l hl
  obtain rfl := Set.mem_singleton_iff.mp (cellResources_subset q _ hl)
  exact Or.inr supplies.stack_fresh

end ModalityInference
