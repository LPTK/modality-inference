import ModalityInference.Proofs.Evaluation
import Mathlib.Data.List.Forall2

/-! Runtime behavior is independent of capture annotations. -/
namespace ModalityInference

@[simp] theorem Term.freeVars_mapAnnotation (t : Term A) (f : A → B) (depth : Nat) :
    (t.mapAnnotation f).freeVars depth = t.freeVars depth := by
  induction t generalizing depth <;> simp_all [Term.mapAnnotation, Term.freeVars]

theorem Eval.annotation_erasure {s γ δ t u v}
    (hγ : List.Forall₂ ValueErasure γ δ) (ht : t.erase = u.erase)
    (h : Eval s γ t v) : ∃ w, Eval s δ u w ∧ ValueErasure v w := by
  induction h generalizing δ u
  all_goals cases u <;> simp only [Term.erase, Term.mapAnnotation, Term.var.injEq,
    Term.lam.injEq, Term.app.injEq, Term.pair.injEq, Term.stackPair.injEq,
    Term.inl.injEq, Term.inr.injEq, Term.defn.injEq, Term.split.injEq,
    Term.case.injEq, Term.reuse.injEq, Term.region.injEq, reduceCtorEq, true_and] at ht
  case app.app _ _ _ _ _ _ _ _ _ hf hx hb ihf ihx ihb f' x' =>
    obtain ⟨_, hf', hvf⟩ := ihf hγ ht.1
    cases hvf with | closure henv hbody =>
    obtain ⟨_, hx', hvx⟩ := ihx hγ ht.2
    obtain ⟨_, hb', hvb⟩ := ihb (.cons hvx henv) hbody
    exact ⟨_, .app hf' hx' hb', hvb⟩
  case pair.pair _ _ _ _ _ _ _ _ iha ihb _ _ |
       stackPair.stackPair _ _ _ _ _ _ _ _ iha ihb _ _ =>
    rcases And.intro (iha hγ ht.1) (ihb hγ ht.2) with ⟨⟨_, ha, hva⟩, ⟨_, hb, hvb⟩⟩
    first | exact ⟨_, .pair ha hb, .pair hva hvb⟩ | exact ⟨_, .stackPair ha hb, .pair hva hvb⟩
  case inl.inl _ _ _ _ _ ih _ | inr.inr _ _ _ _ _ ih _ | region.region _ _ _ _ _ ih _ =>
    obtain ⟨_, he, hv⟩ := ih hγ ht
    first | exact ⟨_, .inl he, .inl hv⟩ | exact ⟨_, .inr he, .inr hv⟩ | exact ⟨_, .region he, hv⟩
  case defn.defn _ _ _ _ _ _ _ _ ihr ihb _ _ =>
    obtain ⟨_, hr, hvr⟩ := ihr .nil ht.1
    obtain ⟨_, hb, hvb⟩ := ihb (.cons hvr hγ) ht.2
    exact ⟨_, .defn hr hb, hvb⟩
  case split.split _ _ _ _ _ _ _ _ _ _ iha ihb _ _ =>
    obtain ⟨_, ha, hva⟩ := iha hγ ht.1
    cases hva with | pair hx hy =>
    obtain ⟨_, hb, hvb⟩ := ihb (.cons .credit (.cons hx (.cons hy hγ))) ht.2
    exact ⟨_, .split ha hb, hvb⟩
  case caseLeft.case _ _ _ _ _ _ _ _ _ iha ihb _ _ _ |
       caseRight.case _ _ _ _ _ _ _ _ _ iha ihb _ _ _ =>
    obtain ⟨_, ha, hva⟩ := iha hγ ht.1
    cases hva; rename_i x' hx
    obtain ⟨_, hb, hvb⟩ := ihb (.cons hx hγ) (by first | exact ht.2.1 | exact ht.2.2)
    first | exact ⟨_, .caseLeft ha hb, hvb⟩ | exact ⟨_, .caseRight ha hb, hvb⟩
  case reuse.reuse _ _ _ _ _ _ _ _ _ _ _ ihk iha ihb _ _ _ =>
    rcases And.intro (ihk hγ ht.1) (And.intro (iha hγ ht.2.1) (ihb hγ ht.2.2)) with
      ⟨⟨_, hk, hvk⟩, ⟨_, ha, hva⟩, ⟨_, hb, hvb⟩⟩
    cases hvk; exact ⟨_, .reuse hk ha hb, .pair hva hvb⟩
  case var.var _ _ _ _ hv j =>
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hv
    subst j
    exact ⟨_, .var (List.getElem?_eq_some_iff.mpr ⟨hγ.length_eq ▸ hi, rfl⟩),
      hγ.get hi (hγ.length_eq ▸ hi)⟩
  case unit.unit => exact ⟨_, .unit, .unit⟩
  case lam.lam _ _ _ body _ body' =>
    refine ⟨_, .lam, .closure ?_ ht⟩
    have hfv : body.freeVars 1 = body'.freeVars 1 := by
      simpa only [Term.freeVars_mapAnnotation] using congrArg (Term.freeVars 1) ht
    apply List.forall₂_of_length_eq_of_get (by simpa [trimEnvironment] using hγ.length_eq)
    simp only [trimEnvironment, List.length_mapIdx, List.get_eq_getElem, List.getElem_mapIdx, hfv]
    intro i hi hj
    split <;> first | exact hγ.get hi hj | exact .unit

end ModalityInference
