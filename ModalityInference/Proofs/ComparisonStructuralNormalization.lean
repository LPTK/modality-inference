import ModalityInference.ComparisonStructuralNormalization
import ModalityInference.Proofs.ComparisonConstructorNormalization
import ModalityInference.Proofs.ComparisonStructuralWitness
import ModalityInference.Proofs.ComparisonStructuralActions
import ModalityInference.Proofs.ComparisonLatticeCompiler

/-! Deterministic normalization preserves every whole endpoint in the guarded
comparison algebra. Finite shape models justify the common bases; source
annotations remain symbolic and their definedness is proved under the same
declared assumptions. -/
namespace ModalityInference.ComparisonStructuralNormalization
open ComparisonAlgebra ComparisonControls ComparisonStructuralBasis
open ComparisonStructuralLattice ComparisonPropagation

/-- The output uses the exact finite basis at the indicated solved shape. -/
def Output (Δ : Bounds) (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (s : ComparisonShape) (a t : CompareTy) : Prop :=
  ∃b, basis names modes shapes s = some b ∧ LatticeForm b.types t ∧
    Representable Δ s t ∧ Equiv Δ a t

theorem basis_representable {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {b : Basis}
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (hb : basis names modes shapes s = some b) :
    ∀a∈b.types, Representable Δ s a := by
  rw [(basis_spec hb).2.2]
  exact extend_representable modes (heads_representable names modes shapes hs s)

theorem Output.constructor_complete {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s t : ComparisonShape} {a c x y : CompareTy}
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (k : Kind) (hx : Output Δ names modes shapes s a x)
    (hy : Output Δ names modes shapes t c y) :
    ∃z, constructor names modes shapes s t k.op k.leftSign x y = .success z ∧
      Output Δ names modes shapes (k.shape s t) (k.op a c) z := by
  obtain ⟨left, hl, hxf, hxr, hxe⟩ := hx
  obtain ⟨right, hr, hyf, hyr, hye⟩ := hy
  obtain ⟨z,hz,hzf,hzr,hze⟩ := ComparisonConstructorNormalization.lift_complete k hxf hyf
    (basis_representable hs hl) (basis_representable hs hr)
  have hheads : LatticeForm (heads names modes shapes (k.shape s t)) z := by
    apply hzf.mono
    intro u hu
    rw [(basis_spec hl).2.2, (basis_spec hr).2.2] at hu
    exact constructor_heads k names modes shapes s t u hu
  obtain ⟨parent,hparent⟩ := basis_exists hheads.nonempty
  refine ⟨z, ?_, parent, hparent, ?_, hzr, (k.congr hxe hye).trans hze⟩
  · simp [constructor, hl, hr, hz]
  · exact hheads.mono (fun u hu => head_mem_types ((basis_spec hparent).1.symm ▸ hu))

theorem Output.modal_complete {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {a x : CompareTy} {m : ModExpr}
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (hx : Output Δ names modes shapes s a x) (hm : DefinedMode Δ m)
    (hms : ∀v∈m.freeVariables, v∈modes) :
    ∃threshold z, (∀fuel≥threshold, modal fuel names modes shapes s x m = .success z) ∧
      Output Δ names modes shapes s (.modal a m) z := by
  obtain ⟨b,hb,hxf,hxr,hxe⟩ := hx
  obtain ⟨clauses,hclauses⟩ := ComparisonLatticeCompiler.compile_complete hxf
  obtain ⟨t,ht,htr,hte⟩ := ComparisonLatticeCompiler.compile_correct
    (basis_representable hs hb) hclauses
  obtain ⟨threshold,action,hact⟩ := ComparisonStructuralActions.prepareAction_complete
    (b := b) (fun v hv => (basis_spec hb).2.1 ▸ hms v hv)
  obtain ⟨hlo,hhi⟩ := ComparisonStructuralActions.prepareAction_spec (hact threshold le_rfl)
  obtain ⟨z,hz,hzr,hze⟩ := action.correct hlo hhi
    (by rw [(basis_spec hb).1]; exact heads_representable names modes shapes hs s)
    hm (ComparisonLatticeCompiler.compile_polynomial hclauses).2 ht
  refine ⟨threshold,z,?_,b,hb,?_,hzr,?_⟩
  · intro fuel hf
    simp [modal, hb, hclauses, hact fuel hf, hz, bind, RunResult.bind]
  · exact reify_property hz (LatticeForm b.types) (fun _ => LatticeForm.atom)
      (fun _ _ => LatticeForm.join) (fun _ _ => LatticeForm.meet)
  · have he := hxe.trans hte.symm
    exact ⟨(AlgebraSubtype.congr he.1 (.refl hm)).trans hze.2,
      hze.1.trans (.congr he.2 (.refl hm))⟩

theorem Output.of_head {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {a : CompareTy}
    (hs : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    (ha : a∈heads names modes shapes s) : Output Δ names modes shapes s a a := by
  obtain ⟨b,hb⟩ := basis_exists (List.ne_nil_of_mem ha)
  have hr := heads_representable names modes shapes hs s a ha
  exact ⟨b,hb,.atom (head_mem_types ((basis_spec hb).1.symm ▸ ha)),hr,.refl hr.1⟩

theorem Output.typeOp {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {a c x y : CompareTy}
    (p : Bool) (hx : Output Δ names modes shapes s a x)
    (hy : Output Δ names modes shapes s c y) :
    Output Δ names modes shapes s (typeOp p a c) (typeOp p x y) := by
  obtain ⟨b,hb,hxf,hxr,hxe⟩ := hx
  obtain ⟨b',hb',hyf,hyr,hye⟩ := hy
  have he : b'=b := Option.some.inj (hb'.symm.trans hb)
  subst b'
  exact ⟨b,hb,lattice_typeOp p hxf hyf,representable_typeOp p hxr hyr,
    Equiv.typeOp p hxe hye (hxe.1.shape_equivalent.trans (hxr.2.2.trans
      (hyr.2.2.symm.trans hye.1.shape_equivalent.symm)))⟩

theorem run_complete {Δ : Bounds} (names : List TypeVar) (modes : List ModVar)
    (shapes : TypeVar → ComparisonShape) (hmodels : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    {a : CompareTy} (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (hsupport : ComparisonInterpolation.Supports (·∈names) (·∈modes) a) :
    ∃threshold t, (∀fuel≥threshold, run fuel names modes shapes a = .success t) ∧
      Output Δ names modes shapes (a.shape.subst shapes) a t := by
  induction a with
  | var v =>
    exact ⟨0, .var v, (by intro fuel _; rfl),
      Output.of_head hshapes (fixed_head_mem names modes shapes hsupport)⟩
  | unit =>
    exact ⟨0, .unit, (by intro fuel _; rfl),
      Output.of_head hshapes (List.mem_append_right _ (by simp))⟩
  | credit =>
    exact ⟨0, .credit, (by intro fuel _; rfl),
      Output.of_head hshapes (List.mem_append_right _ (by simp))⟩
  | prod a c iha ihc =>
    obtain ⟨n,x,hx,hxo⟩ := iha hs.1 (CompareTy.definedUnder_prod_iff.mp hd).1 hsupport.1
    obtain ⟨k,y,hy,hyo⟩ := ihc hs.2 (CompareTy.definedUnder_prod_iff.mp hd).2 hsupport.2
    obtain ⟨z,hz,hzo⟩ := hxo.constructor_complete hshapes .prod hyo
    refine ⟨max n k,z,?_,hzo⟩
    intro fuel hf
    simpa [run, hx fuel ((le_max_left _ _).trans hf), hy fuel ((le_max_right _ _).trans hf),
      Kind.op, Kind.leftSign, bind, RunResult.bind] using hz
  | sum a c iha ihc =>
    obtain ⟨n,x,hx,hxo⟩ := iha hs.1 (CompareTy.definedUnder_sum_iff.mp hd).1 hsupport.1
    obtain ⟨k,y,hy,hyo⟩ := ihc hs.2 (CompareTy.definedUnder_sum_iff.mp hd).2 hsupport.2
    obtain ⟨z,hz,hzo⟩ := hxo.constructor_complete hshapes .sum hyo
    refine ⟨max n k,z,?_,hzo⟩
    intro fuel hf
    simpa [run, hx fuel ((le_max_left _ _).trans hf), hy fuel ((le_max_right _ _).trans hf),
      Kind.op, Kind.leftSign, bind, RunResult.bind] using hz
  | fn a c iha ihc =>
    obtain ⟨n,x,hx,hxo⟩ := iha hs.1 (CompareTy.definedUnder_fn_iff.mp hd).1 hsupport.1
    obtain ⟨k,y,hy,hyo⟩ := ihc hs.2 (CompareTy.definedUnder_fn_iff.mp hd).2 hsupport.2
    obtain ⟨z,hz,hzo⟩ := hxo.constructor_complete hshapes .fn hyo
    refine ⟨max n k,z,?_,hzo⟩
    intro fuel hf
    simpa [run, hx fuel ((le_max_left _ _).trans hf), hy fuel ((le_max_right _ _).trans hf),
      Kind.op, Kind.leftSign, bind, RunResult.bind] using hz
  | join a c iha ihc =>
    obtain ⟨n,x,hx,hxo⟩ := iha hs.1 (CompareTy.definedUnder_join_iff.mp hd).1 hsupport.1
    obtain ⟨k,y,hy,hyo⟩ := ihc hs.2.1 (CompareTy.definedUnder_join_iff.mp hd).2 hsupport.2
    have he : a.shape.subst shapes = c.shape.subst shapes := hs.2.2 shapes hmodels
    rw [←he] at hyo
    refine ⟨max n k,.join x y,?_,hxo.typeOp true hyo⟩
    intro fuel hf
    simp [run, hx fuel ((le_max_left _ _).trans hf), hy fuel ((le_max_right _ _).trans hf),
      bind, pure, RunResult.bind]
  | meet a c iha ihc =>
    obtain ⟨n,x,hx,hxo⟩ := iha hs.1 (CompareTy.definedUnder_meet_iff.mp hd).1 hsupport.1
    obtain ⟨k,y,hy,hyo⟩ := ihc hs.2.1 (CompareTy.definedUnder_meet_iff.mp hd).2 hsupport.2
    have he : a.shape.subst shapes = c.shape.subst shapes := hs.2.2 shapes hmodels
    rw [←he] at hyo
    refine ⟨max n k,.meet x y,?_,hxo.typeOp false hyo⟩
    intro fuel hf
    simp [run, hx fuel ((le_max_left _ _).trans hf), hy fuel ((le_max_right _ _).trans hf),
      bind, pure, RunResult.bind]
  | modal a m ih =>
    obtain ⟨n,x,hx,hxo⟩ := ih hs (CompareTy.definedUnder_modal_iff.mp hd).1 hsupport.1
    obtain ⟨k,z,hz,hzo⟩ := hxo.modal_complete hshapes
      (CompareTy.definedUnder_modal_iff.mp hd).2
      (fun v hv => hsupport.2 v ((m.mem_freeVariables v).mp hv))
    refine ⟨max n k,z,?_,hzo⟩
    intro fuel hf
    simpa [run, hx fuel ((le_max_left _ _).trans hf), bind, RunResult.bind] using
      hz fuel ((le_max_right _ _).trans hf)

theorem modal_monotone {small large : Nat} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {s : ComparisonShape} {a t : CompareTy} {m : ModExpr}
    (hle : small≤large) (h : modal small names modes shapes s a m = .success t) :
    modal large names modes shapes s a m = .success t := by
  cases hb : basis names modes shapes s <;> simp [modal, hb] at h
  rename_i b
  cases hc : ComparisonLatticeCompiler.compile b a <;> simp [hc] at h
  rename_i clauses
  cases hm : ComparisonStructuralActions.prepareAction small b m <;>
    simp [hm,bind,RunResult.bind] at h
  rename_i action
  simpa [modal, hb, hc, ComparisonStructuralActions.prepareAction_monotone hle hm,
    bind,RunResult.bind] using h

theorem run_monotone {small large : Nat} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} {a t : CompareTy}
    (hle : small≤large) (h : run small names modes shapes a = .success t) :
    run large names modes shapes a = .success t := by
  induction a generalizing t with
  | var v => exact h
  | unit => exact h
  | credit => exact h
  | prod a c iha ihc | sum a c iha ihc | fn a c iha ihc
  | join a c iha ihc | meet a c iha ihc =>
    cases hx : run small names modes shapes a <;> simp [run,hx,bind,RunResult.bind] at h
    rename_i x
    cases hy : run small names modes shapes c <;> simp [hy] at h
    rename_i y
    simpa [run,iha hx,ihc hy,bind,pure,RunResult.bind] using h
  | modal a m ih =>
    cases hx : run small names modes shapes a <;> simp [run,hx,bind,RunResult.bind] at h
    rename_i x
    have hx' := ih hx
    simpa [run,hx',bind,RunResult.bind] using modal_monotone hle h

theorem run_correct {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {shapes : TypeVar → ComparisonShape} (hmodels : ComparisonShape.Models Δ shapes)
    (hshapes : ∀v, ComparisonShape.Equivalent Δ (.var v) (shapes v))
    {a : CompareTy} (hs : a.WellShaped Δ) (hd : a.DefinedUnder Δ)
    (hsupport : ComparisonInterpolation.Supports (·∈names) (·∈modes) a)
    {fuel : Nat} {t : CompareTy} (h : run fuel names modes shapes a = .success t) :
    Output Δ names modes shapes (a.shape.subst shapes) a t := by
  obtain ⟨n,u,hu,ho⟩ := run_complete names modes shapes hmodels hshapes hs hd hsupport
  have hl := run_monotone (Nat.le_max_left fuel n) h
  have hr := hu (max fuel n) (Nat.le_max_right fuel n)
  have he : t=u := RunResult.success.inj (hl.symm.trans hr)
  exact he.symm ▸ ho

end ModalityInference.ComparisonStructuralNormalization
