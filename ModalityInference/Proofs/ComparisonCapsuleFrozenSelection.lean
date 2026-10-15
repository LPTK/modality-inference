import ModalityInference.Proofs.ComparisonCapsuleExtraction
import ModalityInference.Proofs.ComparisonPartialStructuredImages

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonCapsuleIntervals ComparisonPartialStructuredCapsule

/-- Exact literal images forced by partial occurrence actions are drawn from
the endpoint grammars of this name's input requests. -/
def frozenNameCandidates (p : Prepared) (total : ModExpr → Bool) (name : Nat) : List CompareTy :=
  ((collect p total).filter (fun r => r.name == name)).flatMap fun r =>
    operandGrammar (pairDepth r.endpoint) r.endpoint

theorem frozenNameCandidates_public (p : Prepared) (total : ModExpr → Bool) (name : Nat)
    {a : CompareTy} (ha : a ∈ frozenNameCandidates p total name) : Public a := by
  obtain ⟨r, _, ha⟩ := List.mem_flatMap.mp ha
  exact operandGrammar_public _ _ ha

/-- A partial instantiated occurrence action freezes its original shared type
image literally. This uses the actual body comparison and allows arbitrary
partial modality and internal type images. -/
theorem collected_partial_action_image {p : Prepared}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (total : ModExpr → Bool) (original : CompareSubstitution)
    (hbody : AlgebraSubtype p.assumptions (original.ty p.sourceType) (.ofTy p.targetType))
    {r : Request} (hr : r ∈ collect p total)
    (hm : ¬Entails p.assumptions (.defined (r.action.subst original.mode))) :
    original.type (.flex r.name) ∈ operandGrammar (pairDepth r.endpoint) r.endpoint := by
  exact internal_operandGrammar_complete hΔ hR hm (collect_algebra hR total hbody r hr)

/-- Every collected name has a complete, witness-preserving split: all its
actions are total after the original modality substitution, or its exact type
image belongs to an input-only finite literal grammar. -/
theorem collected_name_action_dichotomy {p : Prepared}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (total : ModExpr → Bool) (original : CompareSubstitution)
    (hbody : AlgebraSubtype p.assumptions (original.ty p.sourceType) (.ofTy p.targetType))
    (name : Nat) :
    (∀ r ∈ (collect p total).filter (fun r => r.name == name),
      Entails p.assumptions (.defined (r.action.subst original.mode))) ∨
      original.type (.flex name) ∈ frozenNameCandidates p total name := by
  classical
  by_cases ht : ∀ r ∈ (collect p total).filter (fun r => r.name == name),
      Entails p.assumptions (.defined (r.action.subst original.mode))
  · exact Or.inl ht
  · right
    push_neg at ht
    obtain ⟨r, hr, hm⟩ := ht
    have hn : r.name = name := beq_iff_eq.mp (List.mem_filter.mp hr).2
    apply List.mem_flatMap.mpr
    refine ⟨r, hr, ?_⟩
    simpa only [hn] using collected_partial_action_image hΔ hR total original hbody
      (List.mem_filter.mp hr).1 hm

/-- The split shares the original substitution across every collected name;
it makes no independent choices for repeated occurrences or source modalities. -/
theorem collected_actions_or_literal_images {p : Prepared}
    (hΔ : p.assumptions.TypeBoundsDefined) (hR : Residual p.assumptions)
    (total : ModExpr → Bool) (original : CompareSubstitution)
    (hbody : AlgebraSubtype p.assumptions (original.ty p.sourceType) (.ofTy p.targetType)) :
    ∀ name ∈ ((collect p total).map Request.name).dedup,
      (∀ r ∈ (collect p total).filter (fun r => r.name == name),
        Entails p.assumptions (.defined (r.action.subst original.mode))) ∨
        original.type (.flex name) ∈ frozenNameCandidates p total name := by
  intro name _
  exact collected_name_action_dichotomy hΔ hR total original hbody name

end ModalityInference.ComparisonCapsuleContext
