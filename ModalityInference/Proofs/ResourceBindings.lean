import ModalityInference.Proofs.ResourceCaptures

/-! Extend interpreted environments with a separated binding and account for the
resources of the bindings actually read by a body. -/
namespace ModalityInference

theorem ResourceSchemeInterpretation.mono {ρ w a ground v owned}
    (ha : a.realize ρ = some ground) (hv : ResourceInterpretation w ground Mode.identity v owned) :
    ResourceSchemeInterpretation ρ w (Scheme.mono a) v owned := by
  refine ⟨hv.references, ?_⟩
  intro η t hη ht
  have he : η = ρ := GroundInstantiates.mono_iff.mp hη
  exact ⟨owned, Set.Subset.rfl, (Option.some.inj (ha.symm.trans (he ▸ ht))) ▸ hv⟩

theorem ResourceEnvironmentInterpretation.of_lookup {ρ w Γ Γ' γ reserved}
    (h : ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (hc : ∀ (i : Nat) (s : Scheme), Γ'[i]? = some (some s) → Γ[i]? = some (some s)) :
    ResourceEnvironmentInterpretation ρ w Γ' γ reserved :=
  ⟨fun i s hi => h.1 i s (hc i s hi),
   fun i j s t hij hi hj => h.2 i j s t hij (hc i s hi) (hc j t hj)⟩

theorem ContextResources.of_lookup {Γ Γ' : Context} (reserved : Nat → Resources)
    (hc : ∀ (i : Nat) (s : Scheme), Γ'[i]? = some (some s) → Γ[i]? = some (some s)) :
    ContextResources Γ' reserved ⊆ ContextResources Γ reserved :=
  fun _ ⟨i, s, hi, hl⟩ => ⟨i, s, hc i s hi, hl⟩

theorem ResourceEnvironmentInterpretation.cons {ρ w Γ γ s v head tail}
    (hs : ResourceSchemeInterpretation ρ w s v head)
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ tail)
    (hd : Disjoint head (ContextResources Γ tail)) :
    ResourceEnvironmentInterpretation ρ w (some s :: Γ) (v :: γ)
      (fun | 0 => head | i + 1 => tail i) := by
  refine ⟨?_, ?_⟩
  case refine_2 =>
    rintro (_ | i) (_ | j) a b hij hi hj <;> simp_all
    case zero.succ => exact Disjoint.mono_right (show tail j ⊆ ContextResources Γ tail from fun _ hl => ⟨j, b, hj, hl⟩) hd
    case succ.zero => exact (Disjoint.mono_right (show tail i ⊆ ContextResources Γ tail from fun _ hl => ⟨i, a, hi, hl⟩) hd).symm
    case succ.succ => exact hγ.2 _ _ _ _ hij hi hj
  case refine_1 =>
    rintro (_ | i) a hi <;> simp_all
    exact hγ.1 i a hi

theorem ContextResources.cons (Γ : Context) (s : Scheme) (head : Resources)
    (tail : Nat → Resources) :
    ContextResources (some s :: Γ) (fun | 0 => head | i + 1 => tail i) =
      head ∪ ContextResources Γ tail := by
  ext l
  constructor
  · rintro ⟨(_ | i), t, hi, hl⟩
    · exact Or.inl hl
    · exact Or.inr ⟨i, t, hi, hl⟩
  · rintro (h | ⟨i, t, hi, hl⟩)
    · exact ⟨0, s, rfl, h⟩
    · exact ⟨i + 1, t, hi, hl⟩

theorem Context.body_restrict_lookup (body : Term A) (Γ : Context) (s : Option Scheme)
    (i : Nat) (t : Scheme) (h : (Context.restrict (s :: Γ) body.freeVars)[i]? = some (some t)) :
    (s :: Γ.restrict (body.freeVars 1))[i]? = some (some t) := by
  cases i
  case zero => exact (Context.restrict_present.mp h).2
  case succ i =>
    exact Context.restrict_present.mpr
      ⟨(body.mem_freeVars_add 0 1 i).mpr (Context.restrict_present.mp h).1,
        (Context.restrict_present.mp h).2⟩

theorem ResourceEnvironmentInterpretation.cons_used {ρ w γ s v head tail} {Γ : Context}
    (body : AnnotatedTerm)
    (hs : ResourceSchemeInterpretation ρ w s v head)
    (hγ : ResourceEnvironmentInterpretation ρ w (Γ.restrict (body.freeVars 1)) γ tail)
    (hd : Disjoint head (ContextResources (Γ.restrict (body.freeVars 1)) tail)) :
    ResourceEnvironmentInterpretation ρ w (Context.restrict (some s :: Γ) body.freeVars) (v :: γ)
      (fun | 0 => head | i + 1 => tail i) :=
  (ResourceEnvironmentInterpretation.cons hs hγ hd).of_lookup (Context.body_restrict_lookup body Γ (some s))

theorem ContextResources.cons_used_subset (body : AnnotatedTerm) (Γ : Context)
    (s : Scheme) (head : Resources) (tail : Nat → Resources) :
    ContextResources (Context.restrict (some s :: Γ) body.freeVars)
      (fun | 0 => head | i + 1 => tail i) ⊆
      head ∪ ContextResources (Γ.restrict (body.freeVars 1)) tail := by
  rw [← ContextResources.cons]
  exact ContextResources.of_lookup _ (Context.body_restrict_lookup body Γ (some s))

theorem ResourceEnvironmentInterpretation.references {ρ w Γ γ reserved}
    (h : ResourceEnvironmentInterpretation ρ w Γ γ reserved) :
    ∀ l ∈ ContextResources Γ reserved, EnvironmentReferences γ l :=
  fun l ⟨i, s, hi, hl⟩ =>
    let ⟨v, hv, hs⟩ := h.1 i s hi
    ⟨v, List.mem_of_getElem? hv, hs.1 l hl⟩

end ModalityInference
