import ModalityInference.Proofs.ComparisonStructuralNormalization
import ModalityInference.Proofs.ComparisonCoordinateTransition
import ModalityInference.Proofs.ComparisonStructuralControlClosure

/-! Whole endpoint normalization preserves the candidate sorted interpretation
before the root's declared-bound obligations are established. Constructor cases
use genuine child observers; signed-control cases use the same coordinate action
and scalar environment throughout. -/

namespace ModalityInference.ComparisonStructuralNormalization
open ComparisonAlgebra ComparisonControls ComparisonStructuralBasis ComparisonStructuralLattice
  ComparisonPropagation ComparisonShapedObserverGluing

private def interleave (basis heads modes : Nat → Bool) (i : Nat) : Bool :=
  if i % 3 = 0 then basis (i / 3)
  else if i % 3 = 1 then heads (i / 3)
  else modes (i / 3)

@[simp] private theorem interleave_basis (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3*i)=basis i := by simp [interleave,Nat.mul_comm]

@[simp] private theorem interleave_heads (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3*i+1)=heads i := by
  have hd : (3*i+1)/3=i := by omega
  have hm : (3*i+1)%3=1 := by omega
  simp [interleave,hd,hm]

@[simp] private theorem interleave_modes (basis heads modes : Nat → Bool) (i : Nat) :
    interleave basis heads modes (3*i+2)=modes i := by
  have hd : (3*i+2)/3=i := by omega
  have hm : (3*i+2)%3=2 := by omega
  simp [interleave,hd,hm]

private theorem modal_value {Δ s} (d : Data Δ s) {c : Coordinate} {η : ModVar → Mode}
    (hη : c=.unaffected ∨ ModeModels Δ η)
    (hc : ∀m x, d.transition.apply m x=coordinateValue c x (m.complete η))
    {world : Nat → Bool} {modeAtom : Nat → Nat}
    (hw : ∀i, world (modeAtom i)=encodeModes η i) {a : CompareTy} {m : ModExpr}
    (hm : Entails Δ (.defined m)) :
    d.value (.modal a m)=(c.modalWith modeAtom (.const (d.value a)) m).eval world := by
  rw [Data.value,hc]
  symm
  apply Coordinate.modalWith_eval hw
  rcases hη with hη|hη
  · exact Or.inl hη
  · obtain ⟨n,hn⟩ := Option.isSome_iff_exists.mp (hm η hη)
    exact Or.inr ((ModExpr.complete_of_eval hn).symm ▸ hn)

private noncomputable def observationWorld {Δ s} (b : Basis) (d : Data Δ s) (η : ModVar → Mode) : Nat → Bool :=
  interleave (basisValue b.types d.value) (basisValue b.heads d.value) (encodeModes η)

private theorem generated_value {Δ s} (d : Data Δ s) {b : Basis} {c : Coordinate}
    {η : ModVar → Mode} (hη : c=.unaffected ∨ ModeModels Δ η)
    (hc : ∀m x, d.transition.apply m x=coordinateValue c x (m.complete η))
    (g : ComparisonControls.Generated b) (hd : g.term.DefinedUnder Δ) :
    (g.formula (fun i=>3*i+1) (fun i=>3*i+2) c).eval (observationWorld b d η)=
      d.value g.term := by
  induction g with
  | head a ha =>
    simpa [ComparisonControls.Generated.formula,ComparisonControls.Generated.term,Basis.formula,BoolExpr.eval,observationWorld] using
      ComparisonLatticeCompiler.basisValue_index ha d.value
  | join a b iha ihb =>
    simp only [ComparisonControls.Generated.formula,BoolExpr.eval]
    exact congrArg₂ (· || ·) (iha (CompareTy.definedUnder_join_iff.mp hd).1)
      (ihb (CompareTy.definedUnder_join_iff.mp hd).2)
  | meet a b iha ihb =>
    simp only [ComparisonControls.Generated.formula,BoolExpr.eval]
    exact congrArg₂ (· && ·) (iha (CompareTy.definedUnder_meet_iff.mp hd).1)
      (ihb (CompareTy.definedUnder_meet_iff.mp hd).2)
  | modal a m hm ih =>
    have hh := CompareTy.definedUnder_modal_iff.mp hd
    exact (c.modalWith_congr_value _ m (ih hh.1)).trans
      (modal_value d hη hc (fun i=>by simp [observationWorld]) hh.2).symm

private theorem basis_theory {Δ s} (d : Data Δ s) (b : Basis) {c : Coordinate}
    {η : ModVar → Mode} (hη : c=.unaffected ∨ ModeModels Δ η)
    (hc : ∀m x, d.transition.apply m x=coordinateValue c x (m.complete η))
    :
    (b.theoryAt (fun i=>3*i) (fun i=>3*i+1) (fun i=>3*i+2) c).eval
      (observationWorld b d η)=true := by
  apply b.theoryAt_of_modal _ _ _ c _ d.value (fun _ _=>rfl) (fun _ _=>rfl)
  · intro i hi
    simp [observationWorld,basisValue,List.getElem?_eq_getElem hi]
  · intro i hi
    simp [observationWorld,basisValue,List.getElem?_eq_getElem hi]
  · intro a m hp
    apply modal_value d hη hc (fun i=>by simp [observationWorld])
    rcases List.mem_append.mp hp with hp|hp
    · simp only [List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq] at hp
      rcases hp with ⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩|⟨_,rfl⟩ <;>
        exact fun _ _=>rfl
    · obtain ⟨q,_,he⟩ := List.mem_map.mp hp
      cases he
      exact fun η _=>control_total q η

private theorem action_value {Δ s} (d : Data Δ s) {b : Basis} {c : Coordinate}
    {η : ModVar → Mode} (hη : c=.unaffected ∨ ModeModels Δ η)
    (hc : ∀m x, d.transition.apply m x=coordinateValue c x (m.complete η))
    {fuel : Nat} {m : ModExpr} {action : ComparisonStructuralActions.Action}
    (haction : ComparisonStructuralActions.prepareAction fuel b m=.success action)
    {a t : CompareTy} {input : CNF}
    (hin : ComparisonLatticeCompiler.compile b a=some input)
    (hout : reify b.types (action.apply input)=some t)
    (ha : a.DefinedUnder Δ) (hm : Entails Δ (.defined m)) :
    d.value t=d.value (.modal a m) := by
  obtain ⟨hlo,hhi⟩ := ComparisonStructuralActions.prepareAction_spec haction
  obtain ⟨g,hg⟩ := (ComparisonLatticeCompiler.compile_polynomial hin).1.generated
    (fun a ha=>b.types_generated ha)
  have hv := generated_value d hη hc g (hg.symm ▸ ha)
  rw [hg] at hv
  obtain ⟨hl,hu⟩ := g.formula_bounds (fun i=>3*i+1) (fun i=>3*i+2) c (observationWorld b d η)
  rw [hv] at hl hu
  have hworld : observationWorld b d η ∘ (fun i=>3*i)=basisValue b.types d.value := by
    funext i
    simp [observationWorld]
  have hi : CNFHolds (observationWorld b d η ∘ (fun i=>3*i)) input ↔
      (BoolExpr.const (d.value a)).eval (observationWorld b d η)=true := by
    rw [hworld]
    exact ComparisonLatticeCompiler.compile_value hin d.value (fun _ _=>rfl) (fun _ _=>rfl)
  have hsem := action.theory hlo hhi (basis_theory d b hη hc) hi hl hu
  rw [hworld] at hsem
  have houtvalue := reify_correct hout d.value (fun _ _=>rfl) (fun _ _=>rfl)
  apply Bool.eq_iff_iff.mpr
  exact houtvalue.trans (hsem.trans (by rw [←modal_value d hη hc
    (fun i=>by simp [observationWorld]) hm]))

private theorem op_value {Δ s} (d : Data Δ s) (k : Kind) (a b : CompareTy) :
    d.value (k.op a b)=branchValue (d.branch k) k a b := by cases k <;> rfl

private theorem right_distrib_value {Δ s} (d : Data Δ s) (k : Kind)
    (p : Bool) (a b e : CompareTy) :
    d.value (k.op a (typeOp p b e))=
      d.value (typeOp p (k.op a b) (k.op a e)) := by
  cases hb : d.branch k <;> cases k <;> cases p <;>
    simp [typeOp,op_value,Data.value,branchValue,hb,ComparisonStructuralObservers.leftSign]

private theorem left_distrib_value {Δ s} (d : Data Δ s) (k : Kind)
    (p : Bool) (a b e : CompareTy) :
    d.value (k.op (typeOp p a b) e)=
      d.value (typeOp (k.leftSign p) (k.op a e) (k.op b e)) := by
  cases hb : d.branch k <;> cases k <;> cases p <;>
    simp [typeOp,Kind.leftSign,op_value,Data.value,branchValue,hb,ComparisonStructuralObservers.leftSign]

private theorem right_value {Δ s} (d : Data Δ s) (k : Kind)
    {basis : List CompareTy} {a b t : CompareTy}
    (h : ComparisonConstructorNormalization.right k.op basis a b=some t) :
    d.value t=d.value (k.op a b) := by
  induction b generalizing t
  all_goals
    simp only [ComparisonConstructorNormalization.right] at h
    split at h
    next hatom => cases Option.some.inj h; rfl
    next hnot =>
      first
      | contradiction
      | rename_i b e ihb ihe
        cases hx : ComparisonConstructorNormalization.right k.op basis a b <;> simp [hx] at h
        rename_i x
        cases hy : ComparisonConstructorNormalization.right k.op basis a e <;> simp [hy] at h
        rename_i y
        subst t
        first
        | simpa only [typeOp,Data.value,ihb hx,ihe hy] using (right_distrib_value d k true a b e).symm
        | simpa only [typeOp,Data.value,ihb hx,ihe hy] using (right_distrib_value d k false a b e).symm

private theorem lift_value {Δ s} (d : Data Δ s) (k : Kind)
    {left right : List CompareTy} {a b t : CompareTy}
    (h : ComparisonConstructorNormalization.lift k.op k.leftSign left right a b=some t) :
    d.value t=d.value (k.op a b) := by
  induction a generalizing t
  all_goals
    simp only [ComparisonConstructorNormalization.lift] at h
    split at h
    next hatom => exact right_value d k h
    next hnot =>
      first
      | contradiction
      | rename_i a e iha ihe
        cases hx : ComparisonConstructorNormalization.lift k.op k.leftSign left right a b <;> simp [hx] at h
        rename_i x
        cases hy : ComparisonConstructorNormalization.lift k.op k.leftSign left right e b <;> simp [hy] at h
        rename_i y
        subst t
        first
        | have hh := (left_distrib_value d k true a e b).symm
          cases he : k.leftSign true <;> simpa [he,typeOp,Data.value,iha hx,ihe hy] using hh
        | have hh := (left_distrib_value d k false a e b).symm
          cases he : k.leftSign false <;> simpa [he,typeOp,Data.value,iha hx,ihe hy] using hh

private theorem constructor_value {Δ s} (d : Data Δ s) (k : Kind)
    {names : List TypeVar} {modes : List ModVar} {shapes : TypeVar → ComparisonShape}
    {left right : ComparisonShape} {a b t : CompareTy}
    (h : constructor names modes shapes left right k.op k.leftSign a b=.success t) :
    d.value t=d.value (k.op a b) := by
  cases hl : basis names modes shapes left <;> simp [constructor,hl] at h
  rename_i leftBasis
  cases hr : basis names modes shapes right <;> simp [hr] at h
  rename_i rightBasis
  cases hx : ComparisonConstructorNormalization.lift k.op k.leftSign leftBasis.types rightBasis.types a b <;>
    simp [hx] at h
  subst t
  exact lift_value d k hx

private theorem normalized_modal_value {Δ s} (d : Data Δ s) {c : Coordinate}
    {η : ModVar → Mode} (hη : c=.unaffected ∨ ModeModels Δ η)
    (hc : ∀m x, d.transition.apply m x=coordinateValue c x (m.complete η))
    {names : List TypeVar} {modes : List ModVar} {shapes : TypeVar → ComparisonShape}
    {shape : ComparisonShape} {fuel : Nat} {a t : CompareTy} {m : ModExpr}
    (ha : a.DefinedUnder Δ) (hm : Entails Δ (.defined m))
    (h : modal fuel names modes shapes shape a m=.success t) :
    d.value t=d.value (.modal a m) := by
  cases hb : basis names modes shapes shape <;> simp [modal,hb] at h
  rename_i b
  cases hi : ComparisonLatticeCompiler.compile b a <;> simp [hi] at h
  rename_i input
  cases hx : ComparisonStructuralActions.prepareAction fuel b m <;> simp [hx,bind,RunResult.bind] at h
  rename_i action
  cases ho : reify b.types (action.apply input) <;> simp [ho] at h
  subst t
  exact action_value d hη hc hx hi ho ha hm

private theorem op_congr_value {Δ s s₁ s₂} (d : Data Δ s) (hr : Resolved Δ s) (k : Kind)
    {a b x y : CompareTy} (ha : Representable Δ s (k.op a b))
    (hx : Representable Δ s₁ x) (hy : Representable Δ s₂ y)
    (hax : Equiv Δ a x) (hby : Equiv Δ b y) :
    d.value (k.op x y)=d.value (k.op a b) := by
  obtain ⟨_,hal,har⟩ := hr.children k ha
  have hxl : Representable Δ (leftShape s) x :=
    ⟨hx.1,hx.2.1,hax.1.shape_equivalent.symm.trans hal.2.2⟩
  have hyr : Representable Δ (rightShape s) y :=
    ⟨hy.1,hy.2.1,hby.1.shape_equivalent.symm.trans har.2.2⟩
  simp only [op_value]
  cases he : d.branch k with
  | inl g =>
    have hh : booleanValue g.observer x=booleanValue g.observer a :=
      le_antisymm (g.value_mono hxl hal hax.2) (g.value_mono hal hxl hax.1)
    simp only [branchValue,hh]
  | inr g =>
    exact le_antisymm (g.value_mono hyr har hby.2) (g.value_mono har hyr hby.1)

private theorem constructor_result_value {Δ s} (d : Data Δ s) (hr : Resolved Δ s)
    {names : List TypeVar} {modes : List ModVar} {shapes : TypeVar → ComparisonShape}
    (hmodels : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (k : Kind) {a b x y t : CompareTy} {fuel : Nat}
    (ha : Representable Δ s (k.op a b))
    (hsa : ComparisonInterpolation.Supports (·∈names) (·∈modes) a)
    (hsb : ComparisonInterpolation.Supports (·∈names) (·∈modes) b)
    (hx : run fuel names modes shapes a=.success x)
    (hy : run fuel names modes shapes b=.success y)
    (ht : constructor names modes shapes (a.shape.subst shapes) (b.shape.subst shapes)
      k.op k.leftSign x y=.success t) :
    d.value t=d.value (k.op a b) := by
  obtain ⟨_,hal,har⟩ := hr.children k ha
  obtain ⟨_,_,_,hxr,hxe⟩ := run_correct hmodels hshapes hal.1 hal.2.1 hsa hx
  obtain ⟨_,_,_,hyr,hye⟩ := run_correct hmodels hshapes har.1 har.2.1 hsb hy
  exact (constructor_value d k ht).trans (op_congr_value d hr k ha hxr hyr hxe hye)

/-- Normalization is valid in the candidate sorted interpretation before its
whole declared-bound obligations have been established. -/
theorem run_value {Δ s} (d : Data Δ s) (hr : Resolved Δ s) {c : Coordinate}
    {η : ModVar → Mode} (hη : c=.unaffected ∨ ModeModels Δ η)
    (hc : ∀m x, d.transition.apply m x=coordinateValue c x (m.complete η))
    {names : List TypeVar} {modes : List ModVar} {shapes : TypeVar → ComparisonShape}
    (hmodels : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    {a t : CompareTy} {fuel : Nat} (ha : Representable Δ s a)
    (hs : ComparisonInterpolation.Supports (·∈names) (·∈modes) a)
    (h : run fuel names modes shapes a=.success t) : d.value t=d.value a := by
  induction a generalizing t with
  | var v => cases RunResult.success.inj h; rfl
  | unit => cases RunResult.success.inj h; rfl
  | credit => cases RunResult.success.inj h; rfl
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    cases hx : run fuel names modes shapes a <;> simp [run,hx,bind,RunResult.bind] at h
    rename_i x
    cases hy : run fuel names modes shapes b <;> simp [hy] at h
    rename_i y
    first
    | exact constructor_result_value d hr hmodels hshapes .prod ha hs.1 hs.2 hx hy h
    | exact constructor_result_value d hr hmodels hshapes .sum ha hs.1 hs.2 hx hy h
    | exact constructor_result_value d hr hmodels hshapes .fn ha hs.1 hs.2 hx hy h
  | join a b iha ihb =>
    cases hx : run fuel names modes shapes a <;> simp [run,hx,bind,RunResult.bind] at h
    rename_i x
    cases hy : run fuel names modes shapes b <;> simp [hy,pure] at h
    rename_i y
    subst t
    have hd := CompareTy.definedUnder_join_iff.mp ha.2.1
    exact congrArg₂ (· || ·) (iha ⟨ha.1.1,hd.1,ha.2.2⟩ hs.1 hx)
      (ihb ⟨ha.1.2.1,hd.2,ha.1.2.2.symm.trans ha.2.2⟩ hs.2 hy)
  | meet a b iha ihb =>
    cases hx : run fuel names modes shapes a <;> simp [run,hx,bind,RunResult.bind] at h
    rename_i x
    cases hy : run fuel names modes shapes b <;> simp [hy,pure] at h
    rename_i y
    subst t
    have hd := CompareTy.definedUnder_meet_iff.mp ha.2.1
    exact congrArg₂ (· && ·) (iha ⟨ha.1.1,hd.1,ha.2.2⟩ hs.1 hx)
      (ihb ⟨ha.1.2.1,hd.2,ha.1.2.2.symm.trans ha.2.2⟩ hs.2 hy)
  | modal a m ih =>
    cases hx : run fuel names modes shapes a <;> simp [run,hx,bind,RunResult.bind] at h
    rename_i x
    have hd := CompareTy.definedUnder_modal_iff.mp ha.2.1
    obtain ⟨_,_,_,hxr,_⟩ := run_correct (a := a) hmodels hshapes ha.1 hd.1 hs.1 hx
    exact (normalized_modal_value d hη hc hxr.2.1 hd.2 h).trans
      (congrArg (d.transition.apply m) (ih ⟨ha.1,hd.1,ha.2.2⟩ hs.1 hx))

end ModalityInference.ComparisonStructuralNormalization
