import ModalityInference.Proofs.ResourceReuse

/-! Region entry extends the live world with a fresh frame. A globally typed
result can return to the original world, including all aliased references. -/
namespace ModalityInference

theorem ResourceEnvironmentInterpretation.world_mono {ρ w w' Γ γ reserved}
    (h : ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (hlive : ∀ l, w.Live l → w'.Live l) :
    ResourceEnvironmentInterpretation ρ w' Γ γ reserved := by
  refine ⟨?_, h.2⟩
  intro i s hi
  obtain ⟨v, hv, hs⟩ := h.1 i s hi
  refine ⟨v, hv, hs.1, ?_⟩
  intro η ground hη hg
  obtain ⟨owned, ho, hr⟩ := hs.2 η ground hη hg
  exact ⟨owned, ho, hr.reworld (fun l hl => hlive l (hr.valid l hl))⟩

theorem World.Compatible.enter {w : World} {s γ} (hs : w.Compatible s γ) :
    (World.mk (insert s.frames.start w.liveFrames)).Compatible s.enter γ := by
  have hf : ∀ n, s.frames.tail.at n ≠ s.frames.start :=
    fun n => Ne.symm (s.frames.start_not_tail hs.1.2.2.1 n)
  refine ⟨⟨hs.1.1, by change 0 < 1; decide, hs.1.2.2.1, hf⟩, Finset.mem_insert_self _ _, ?_,
    fun l hl h => hs.2.2.2 l hl (Supplies.fresh_enter h)⟩
  intro n hn
  rcases Finset.mem_insert.mp hn with he | hn
  · exact hf n he
  · exact hs.2.2.1 (n + 1) (by simpa only [Supplies.enter, Supply.tail_at] using hn)

theorem Typing.resource_region {t : AnnotatedTerm} {a : Ty} {Γ : Context} {ρ}
    (ih : ∀ {w γ reserved ground},
      ResourceEnvironmentInterpretation ρ w (Γ.restrict t.freeVars) γ reserved →
      (TypeExpr.modal a (.const Mode.global)).realize ρ = some ground →
      ResourceSemanticEvaluation w γ t ground (ContextResources (Γ.restrict t.freeVars) reserved))
    {w γ reserved ground}
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (Term.region t).freeVars) γ reserved)
    (ha : a.realize ρ = some ground) :
    ResourceSemanticEvaluation w γ (.region t) ground
      (ContextResources (Γ.restrict (Term.region t).freeVars) reserved) := by
  intro supplies hsup
  have henv := hγ.world_mono (w' := ⟨insert supplies.frames.start w.liveFrames⟩)
    (fun l hl => by cases l <;> first | trivial | exact Finset.mem_insert_of_mem hl)
  obtain ⟨v, owned, he, hv, ho⟩ := ih (ground := ground.modal Mode.global) henv
    (by simp [TypeExpr.realize, ModExpr.eval, ha]) supplies.enter hsup.enter
  have hglobal : ResourceInterpretation ⟨insert supplies.frames.start w.liveFrames⟩
      ground Mode.global v owned := by
    simpa using ResourceInterpretation.modal_iff.mp hv
  have hv' : w.ValidValue v := by
    intro l hl
    have hh := hglobal.global_references (by simp [Mode.compose, Mode.global]) l hl
    cases l with
    | heap => trivial
    | stack => exact hh.elim
  obtain ⟨owned', hsub, hri⟩ := ResourceInterpretation.mode_mono
    (show Mode.global.le Mode.identity = true by decide) (hglobal.reworld hv')
  exact ⟨v, owned', .region he, hri,
    hsub.trans (ho.trans (Set.union_subset_union Set.Subset.rfl
      (fun _ h => Supplies.fresh_enter h)))⟩

end ModalityInference
