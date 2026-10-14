import ModalityInference.Proofs.SharingLockCapture
import ModalityInference.Proofs.SchemeBounds

/-! Modal refinement can retain both shared and unshared instances of a capture. -/
namespace ModalityInference

namespace SharingLockCapture

def refinedSource : Scheme :=
  {modParams := [2]
   bounds := [.sub (α 0) (.modal (α 0) (μ 2)),
     .sub (.modal (α 0) (μ 2)) (.modal (.modal (α 0) (μ 2)) (.future (μ 0)))]
   body := .modal (α 0) (μ 2)}

def refinedCapture : Scheme := refinedSource.modal (.capture (μ 0))

def sharedType : Ty := .modal (.modal (α 0) (.const Mode.aliased)) (.capture (μ 0))

theorem original_subsumes_refined : Subsumes residual (.mono (α 0)) refinedSource := by
  refine ⟨{}, by simp [Instantiates, Scheme.mono], by simp [EntailsAll, Scheme.mono,
    Substitution.bounds], ?_⟩
  exact .bound (by decide)

theorem refined_lock : Lock residual (μ 0) [some refinedSource] [some refinedCapture] := by
  refine .keep .nil ?_ ?_ (.bound (by decide))
  all_goals simp [Scheme.FreshForBounds, Scheme.FreshForMode, refinedSource, μ,
    residual, Bounds.typeVars, Bounds.modVars, Constraint.typeVars, Constraint.modVars,
    TypeExpr.typeVars, TypeExpr.modVars, ModExpr.vars, aliasCapture, aliasFuture, α,
    ModExpr.epsilon]

def sharedInstance : Substitution := {modes := [(2, .const Mode.aliased)]}

theorem shared_instance_bounds : EntailsAll residual (sharedInstance.bounds refinedCapture.bounds) := by
  simp [sharedInstance, refinedCapture, refinedSource, Scheme.modal, Substitution.bounds,
    Substitution.constraint, Constraint.subst, Substitution.type, Substitution.mode,
    TypeExpr.subst, ModExpr.subst, α, μ, EntailsAll, Entails, TypeExpr.DefinedUnder,
    TypeExpr.wellFormedBounds, ModeModels, ModeSatisfies, ModExpr.WellFormed, ModExpr.eval,
    List.lookup_cons]
  exact ⟨Subtype.identityRev.trans (.congr .refl (.valid fun _ _ =>
    ⟨_, _, rfl, rfl, by decide⟩)), (Subtype.bound (by decide)).trans .composeRev⟩

theorem shared_many : Subtype residual sharedType (.modal sharedType (.const Mode.many)) := by
  have h : Subtype residual (α 0) (.modal (α 0) (.const Mode.many)) :=
    Subtype.identityRev.trans (.bound (by decide))
  refine (Subtype.congr (Subtype.congr h (.refl ?_)) (.refl ?_)).trans
    ((Subtype.congr (Subtype.modal_comm ?_ ?_) (.refl ?_)).trans (Subtype.modal_comm ?_ ?_))
  all_goals simp [Entails, ModExpr.WellFormed, ModExpr.eval, μ]

theorem refined_subsumes_shared :
    Subsumes residual refinedCapture (.mono (.modal sharedType (.const Mode.many))) :=
  ⟨sharedInstance, by simp [Instantiates, refinedCapture, refinedSource, Scheme.modal,
    sharedInstance], shared_instance_bounds, shared_many⟩

theorem shared_join : ContextJoin residual [none, some (.mono sharedType)]
    [none, some (.mono sharedType)] [none, some (.mono (.modal sharedType (.const Mode.many)))] := by
  refine .unused (.shared .nil (by simp [Scheme.FreshForBounds, Scheme.mono]) ?_)
  refine (Subtype.modal_comm ?_ ?_).trans (.congr (Subtype.aliased_idempotent _ _) (.refl ?_))
  all_goals simp [Entails, ModExpr.WellFormed, ModExpr.eval, μ]

theorem shared_variable : Typing residual [none, some (.mono sharedType)] (.var 1) sharedType := by
  refine .var (Γ := [none, some (.mono sharedType)]) (i := 1) (s := .mono sharedType)
    (σ := {}) rfl ?_ ?_ ?_
  all_goals simp [Instantiates, Scheme.mono, EntailsAll, Substitution.bounds, sharedType,
    Entails, TypeExpr.wellFormedBounds, ModExpr.WellFormed, ModExpr.eval, α, μ,
    Substitution.ty, Substitution.type, Substitution.mode, TypeExpr.subst, ModExpr.subst]

theorem refined_body : Typing residual [some (.mono (α 1)), some refinedCapture]
    (.pair (.var 1) (.var 1)) (.modal (.prod (α 2) (α 3)) (μ 1)) := by
  refine .subs (.pair shared_join
    (.subs shared_variable (ContextLe.refl _ _) (.trans .compose (.bound (by decide))))
    (.subs shared_variable (ContextLe.refl _ _) (.trans .compose (.bound (by decide)))))
    (.drop (.keep .nil refined_subsumes_shared)) .refl

theorem refined_typable : Typing residual context
    (.lam [some refinedCapture] (.pair (.var 1) (.var 1)))
    (.modal (.fn (α 1) (.modal (.prod (α 2) (α 3)) (μ 1))) (μ 0)) := by
  refine .subs (.lam ?_ ?_ refined_lock refined_body) (.keep .nil original_subsumes_refined) .refl
  all_goals simp [EntailsAll, Entails, TypeExpr.wellFormedBounds, α, μ,
    ModExpr.WellFormed, ModExpr.eval]

theorem inferred_type_with_refined_annotation : ∃ result, infer 100 context term = .success result ∧
    (.lam [some refinedCapture] (.pair (.var 1) (.var 1)) : AnnotatedTerm).erase = term ∧
    Typing result.residual (context.subst result.substitution)
      (.lam [some refinedCapture] (.pair (.var 1) (.var 1))) result.scheme.body :=
  ⟨_, rfl, rfl, refined_typable⟩

end SharingLockCapture
end ModalityInference
