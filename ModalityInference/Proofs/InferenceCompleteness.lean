import ModalityInference.Proofs.GenerationCompleteness
import ModalityInference.Proofs.SolverCompleteness
import ModalityInference.Proofs.GeneralizedCoverage

/-! Executable inference completeness follows from a single ground generation
witness; increasing the budget preserves its exact generated result. -/
namespace ModalityInference

theorem GenerationReady.initial_empty : GenerationReady [] (initialInferenceState []) :=
  ⟨AlgorithmicContext.bounded_nil _ _, AlgorithmicContext.flexible_nil,
    AlgorithmicContext.modParamsBounded_nil _, Bounds.bounded_nil _ _, Bounds.flexible_nil⟩

theorem GroundGenerates.infer_complete {t ρ a}
    (h : GroundGenerates [] t (initialInferenceState []) ρ a) :
    ∃ n, ∀ fuel ≥ n, ∃ result, infer fuel [] t = .success result := by
  obtain ⟨n, r, η, ground, hg, hm, _, _, _⟩ := h
  have hb := generate_bounded hg GenerationReady.initial_empty.contextBounded
    GenerationReady.initial_empty.constraintsBounded
  have hf := generate_flexible hg AlgorithmicContext.flexible_nil Bounds.flexible_nil
  obtain ⟨k, hk⟩ := solveFrom_complete hb.2 hf.2 ⟨η, hm⟩
  refine ⟨max n k, fun fuel hbudget => ?_⟩
  obtain ⟨solved, hsolved⟩ := hk fuel (by omega)
  have hgenerated := generate_monotone hg fuel (by omega)
  refine ⟨⟨generalizeOver [] solved.bounds (solved.substitution.ty r.type),
    r.term, solved.substitution, solved.bounds, solved.trace⟩, ?_⟩
  simp [infer, hgenerated, hsolved, bind, pure, RunResult.bind]

theorem GroundTypingComplete.infer_complete {t a} (ht : Typing [] [] t a)
    (hc : GroundTypingComplete [] [] t a) :
    ∃ n, ∀ fuel ≥ n, ∃ result, infer fuel [] t.erase = .success result := by
  let ρ : GroundAssignment := ⟨fun _ => .unit Mode.identity, fun _ => Mode.identity⟩
  have hm : GroundModels ρ [] := by simp [GroundModels]
  obtain ⟨target, htarget⟩ := Option.isSome_iff_exists.mp (ht.realize_defined hm)
  exact (hc [] (initialInferenceState []) ρ ρ target GenerationReady.initial_empty hm
    (AlgorithmicContextCovers.nil _ _ _) hm htarget).infer_complete

@[simp] theorem generalizeOver_nil (cs : Bounds) (a : Ty) :
    generalizeOver [] cs a = Scheme.generalize cs a := by
  simp [generalizeOver]

theorem GroundTypingComplete.infer_covers {t a fuel result}
    (hc : GroundTypingComplete [] [] t a) (hi : infer fuel [] t.erase = .success result)
    (ρ τ : GroundAssignment) :
    SchemeCovers ρ τ result.scheme (Scheme.generalize [] a) := by
  simp only [infer, bind, pure, RunResult.bind] at hi
  repeat' (split at hi <;> try contradiction)
  cases hi
  rename_i _ r hg _ solved hs
  simp only [List.map_nil, generalizeOver_nil]
  apply generate_generalize_covers (nt := 0) (nm := 0)
    (by simpa only [List.map_nil, initialInferenceState, List.foldl_nil] using hg) hs
  intro η b hη hb
  obtain ⟨k, q, ξ, ground, hq, hm, _, ht, hsub⟩ :=
    hc [] (initialInferenceState []) ρ η b GenerationReady.initial_empty hη
      (AlgorithmicContextCovers.nil _ _ _) (by simp [initialInferenceState, GroundModels]) hb
  exact ⟨k, q, ξ, ground, hq, hm, ht, hsub⟩

theorem inference_complete {t a} (h : RawTyping [] [] t a) :
    ∃ n, ∀ fuel ≥ n, ∃ result, infer fuel [] t = .success result := by
  obtain ⟨elaborated, rfl, ht⟩ := h
  exact GroundTypingComplete.infer_complete ht ht.ground_complete

/-- Every ground instance of any closed declarative type is represented below
that instance by every successful inferred scheme. -/
theorem inference_ground_principal {t a fuel result} (ht : RawTyping [] [] t a)
    (hi : infer fuel [] t = .success result) (ρ τ : GroundAssignment) :
    SchemeCovers ρ τ result.scheme (Scheme.generalize [] a) := by
  obtain ⟨elaborated, rfl, htyped⟩ := ht
  exact htyped.ground_complete.infer_covers hi ρ τ

end ModalityInference
