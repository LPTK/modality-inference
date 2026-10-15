import ModalityInference.Proofs.ComparisonPartialCapsule

/-! A partial carrier at an atomic shape is a frozen input capsule followed by
one total action. The candidate capsules are finite root-spine fragments of
the comparison boundary; their frozen operands are retained literally. -/

namespace ModalityInference.ComparisonPartialCapsule

open ComparisonPartialCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

/-- All possible frozen boundaries exposed by root composition steps. -/
def candidates : CompareTy → List (CompareTy × ModExpr)
  | .modal a (.compose m n) => candidates (.modal (.modal a m) n)
  | .modal a m => (a, m) :: candidates a
  | .prod a b | .sum a b | .fn a b | .join a b | .meet a b => candidates a ++ candidates b
  | _ => []
termination_by a => size a
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [size, ComparisonPartialModes.expressionSize]
  all_goals first | omega | have := mode_size_pos m; omega

theorem observe_mem_candidates {Δ : Bounds} (a : CompareTy) {token : CompareTy × ModExpr}
    (h : token ∈ observe Δ a) : token ∈ candidates a := by
  match a with
  | .modal a m =>
    cases m
    case compose m n =>
      rw [observe_compose] at h
      rw [candidates]
      exact observe_mem_candidates _ h
    all_goals
      rw [observe] at h
      · rw [candidates]
        · split at h
          · exact List.mem_cons_of_mem _ (observe_mem_candidates a h)
          · exact List.mem_cons.mpr (Or.inl (Set.mem_singleton_iff.mp h))
        · simp
      · simp
  | .join a b =>
    rw [observe] at h
    rw [candidates, List.mem_append]
    exact h.elim (fun h => Or.inl (observe_mem_candidates a h))
      (fun h => Or.inr (observe_mem_candidates b h))
  | .meet a b =>
    rw [observe] at h
    rw [candidates]
    exact List.mem_append_left _ (observe_mem_candidates a h.1)
  | .var _ | .unit | .credit | .prod _ _ | .sum _ _ | .fn _ _ =>
    rw [observe] at h <;> simp_all
termination_by size a
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [size, ComparisonPartialModes.expressionSize]
  all_goals omega

structure Normal (Δ : Bounds) (a : CompareTy) where
  token : CompareTy × ModExpr
  suffix : ModExpr
  observation : observe Δ a = {token}
  total : Entails Δ (.defined suffix)
  forward : ShapedSubtype Δ a (.modal (.modal token.1 token.2) suffix)
  backward : ShapedSubtype Δ (.modal (.modal token.1 token.2) suffix) a

def Normal.modal {Δ : Bounds} {a : CompareTy} (s : Normal Δ a)
    {m : ModExpr} (hm : Entails Δ (.defined m)) : Normal Δ (.modal a m) where
  token := s.token
  suffix := .compose s.suffix m
  observation := by rw [observe_modal_total hm]; exact s.observation
  total := Entails.defined_compose_iff.mpr ⟨s.total, hm⟩
  forward := (ShapedSubtype.congr s.forward (.refl hm)).trans
    (.compose (a := .modal s.token.1 s.token.2) s.forward.wellShaped_right)
  backward := (ShapedSubtype.composeRev (a := .modal s.token.1 s.token.2) s.forward.wellShaped_right).trans
    (.congr s.backward (.refl hm))

def Normal.compose {Δ : Bounds} {a : CompareTy} {m n : ModExpr}
    (s : Normal Δ (.modal (.modal a m) n)) : Normal Δ (.modal a (.compose m n)) where
  token := s.token
  suffix := s.suffix
  observation := by rw [observe_compose]; exact s.observation
  total := s.total
  forward := (ShapedSubtype.composeRev (a := a) s.forward.wellShaped_left).trans s.forward
  backward := s.backward.trans (.compose (a := a) s.forward.wellShaped_left)

theorem modal_partial_normal {Δ : Bounds} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) {a : CompareTy} (hs : a.WellShaped Δ) :
    Nonempty (Normal Δ (.modal a m)) := by
  have he := not_epsilon_of_partial hm
  induction m generalizing a with
  | compose m n ihm ihn =>
    by_cases hn : Entails Δ (.defined n)
    · have hm' : ¬Entails Δ (.defined m) :=
        fun h => hm (Entails.defined_compose_iff.mpr ⟨h, hn⟩)
      obtain ⟨s⟩ := ihm hm' hs (not_epsilon_of_partial hm')
      exact ⟨(s.modal hn).compose⟩
    · obtain ⟨s⟩ := ihn hn (a := .modal a m) hs (not_epsilon_of_partial hn)
      exact ⟨s.compose⟩
  | _ =>
    refine ⟨⟨(a, _), .epsilon, ?_, (fun _ _ => rfl), .identityRev hs, .identity hs⟩⟩
    rw [observe] <;> simp_all


theorem carrier_partial_normal {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    {a : CompareTy} (hc : Carrier Δ a) (hs : a.WellShaped Δ)
    (ha : Atomic (a.shape.subst ρ)) (hn : ¬a.DefinedUnder Δ) : Nonempty (Normal Δ a) := by
  induction a with
  | var | unit | credit =>
    exact False.elim (hn (by simp [CompareTy.DefinedUnder, CompareTy.wellFormedBounds, ModeModels]))
  | prod | sum | fn => exact False.elim ha
  | join a b _ _ => exact False.elim (hn (CompareTy.definedUnder_join_iff.mpr hc))
  | meet a b _ _ => exact False.elim (hn (CompareTy.definedUnder_meet_iff.mpr hc))
  | modal a m ih =>
    by_cases hm : Entails Δ (.defined m)
    · obtain ⟨s⟩ := ih hc hs ha (fun hd => hn (CompareTy.definedUnder_modal_iff.mpr ⟨hd, hm⟩))
      exact ⟨s.modal hm⟩
    · exact modal_partial_normal hm hs

/-- A partial carrier below an input boundary uses one of that boundary's
finitely many literal root-spine fragments, followed by a total action. -/
theorem carrier_input_normal {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (ha : Carrier Δ a)
    (hatom : Atomic (a.shape.subst ρ)) (hn : ¬a.DefinedUnder Δ)
    (hab : AlgebraSubtype Δ a b) :
    ∃ s : Normal Δ a, s.token ∈ candidates b := by
  obtain ⟨s⟩ := carrier_partial_normal ha hab.wellShaped_left hatom hn
  refine ⟨s, observe_mem_candidates (Δ := Δ) b ?_⟩
  apply algebra_sound hΔ hρ hab hatom
  rw [s.observation]
  exact Set.mem_singleton _

/-- The dual orientation uses a partial carrier boundary, so its observation
contains the same literal token as the image. -/
theorem carrier_input_normal_dual {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a b : CompareTy} (ha : Carrier Δ a) (hb : Carrier Δ b)
    (hatom : Atomic (a.shape.subst ρ)) (hn : ¬a.DefinedUnder Δ)
    (hba : AlgebraSubtype Δ b a) :
    ∃ s : Normal Δ a, s.token ∈ candidates b := by
  obtain ⟨s⟩ := carrier_partial_normal ha hba.wellShaped_right hatom hn
  have hnb : ¬b.DefinedUnder Δ := fun hd => hn ((hb.defined_iff hΔ ha hba).mp hd)
  obtain ⟨token, hbtoken, hatoken⟩ := carrier_capsule_eq hΔ hρ hb ha
    (by rw [hba.shape_equivalent ρ hρ]; exact hatom) hnb hba
  have he : s.token = token := by
    have hmem : s.token ∈ observe Δ a := s.observation ▸ Set.mem_singleton _
    simpa only [hatoken, Set.mem_singleton_iff] using hmem
  refine ⟨s, observe_mem_candidates (Δ := Δ) b ?_⟩
  rw [he, hbtoken]
  exact Set.mem_singleton _


/-- Root-spine fragments of a public input remain public, including the
literal annotations retained below the frozen boundary. -/
theorem candidates_ofTy_public (t : Ty) {token : CompareTy × ModExpr}
    (h : token ∈ candidates (.ofTy t)) : ∃ a : Ty, CompareTy.ofTy a = token.1 := by
  match t with
  | .var _ | .unit | .credit => simp [CompareTy.ofTy, candidates] at h
  | .prod a b | .sum a b | .fn a b =>
    simp only [CompareTy.ofTy, candidates, List.mem_append] at h
    exact h.elim (candidates_ofTy_public a) (candidates_ofTy_public b)
  | .modal a m =>
    cases m
    case compose m n =>
      change token ∈ candidates (.modal (.ofTy a) (.compose m n)) at h
      rw [candidates] at h
      exact candidates_ofTy_public (.modal (.modal a m) n) h
    all_goals
      change token ∈ candidates (.modal (.ofTy a) _) at h
      rw [candidates] at h
      · rcases List.mem_cons.mp h with he | h
        · cases he
          exact ⟨a, rfl⟩
        · exact candidates_ofTy_public a h
      · simp
termination_by size (.ofTy t)
decreasing_by
  all_goals simp_wf
  all_goals simp_all only [CompareTy.ofTy, size, ComparisonPartialModes.expressionSize]
  all_goals omega

/-- Every partial atomic carrier compared with a public upper endpoint is a
public frozen fragment of that endpoint acted on by one total symbolic suffix. -/
theorem carrier_public_input_normal {Δ : Bounds} {ρ : TypeVar → ComparisonShape}
    (hΔ : Δ.TypeBoundsDefined) (hρ : ComparisonShape.Models Δ ρ)
    {a : CompareTy} {b : Ty} (ha : Carrier Δ a)
    (hatom : Atomic (a.shape.subst ρ)) (hn : ¬a.DefinedUnder Δ)
    (hab : AlgebraSubtype Δ a (.ofTy b)) :
    ∃ s : Normal Δ a, s.token ∈ candidates (.ofTy b) ∧
      ∃ t : Ty, CompareTy.ofTy t = s.token.1 := by
  obtain ⟨s, hs⟩ := carrier_input_normal hΔ hρ ha hatom hn hab
  exact ⟨s, hs, candidates_ofTy_public b hs⟩

end
end ModalityInference.ComparisonPartialCapsule
