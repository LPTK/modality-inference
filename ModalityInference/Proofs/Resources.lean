import ModalityInference.ResourceSemantics
import ModalityInference.Proofs.Subtyping
import ModalityInference.Proofs.Annotations
import ModalityInference.Proofs.Grounding

/-! Properties of ownership evidence that is independent of capture annotations. -/
namespace ModalityInference

theorem cellResources_subset (m : Mode) (l : Location) : cellResources m l ⊆ {l} := by
  cases h : m.unique <;> simp [cellResources, h]

theorem ResourceInterpretation.credit {w : World} {l : Location} {m : Mode}
    (hlive : w.Live l) (hlocal : m.isLocal = true ∨ HeapLocation l) :
    ResourceInterpretation w (.credit m) Mode.identity (.credit l) (cellResources m l) := by
  simp only [ResourceInterpretation, GroundTy.mode, Mode.compose_identity]
  refine ⟨?_, fun k hk =>
    (Set.mem_singleton_iff.mp (cellResources_subset m l hk)).symm ▸ References.credit,
    hlocal, trivial⟩
  rintro k ⟨⟩
  exact hlive

theorem ValueErasure.refl (v : Value) : ValueErasure v v := by
  induction v using Value.rec
    (motive_2 := fun γ => List.Forall₂ ValueErasure γ γ)
  all_goals solve_by_elim [ValueErasure.unit, ValueErasure.credit, ValueErasure.pair,
    ValueErasure.inl, ValueErasure.inr, ValueErasure.closure, List.Forall₂.nil, List.Forall₂.cons]

theorem ValueErasure.valid {v u} (h : ValueErasure v u) {w : World}
    (hv : w.ValidValue v) : w.ValidValue u :=
  fun l hl => hv l ((h.references l).mpr hl)

theorem environmentReferences_erasure {γ δ} (h : List.Forall₂ ValueErasure γ δ) (l) :
    EnvironmentReferences γ l ↔ EnvironmentReferences δ l := by
  simpa only [References.closure_iff] using
    (ValueErasure.closure (Γ := []) (Δ := []) (t := .unit) (u := .unit) h rfl).references l

theorem World.compatible_erasure {w : World} {s γ δ}
    (h : List.Forall₂ ValueErasure γ δ) : w.Compatible s γ ↔ w.Compatible s δ := by
  simp only [World.Compatible, environmentReferences_erasure h]

theorem environmentValid_erasure {w : World} {γ δ}
    (h : List.Forall₂ ValueErasure γ δ) :
    (∀ v ∈ γ, w.ValidValue v) ↔ ∀ v ∈ δ, w.ValidValue v := by
  exact ⟨fun hv v hd l hl =>
    let ⟨u, hu, hr⟩ := (environmentReferences_erasure h l).mpr ⟨v, hd, hl⟩
    hv u hu l hr,
    fun hv v hg l hl =>
    let ⟨u, hu, hr⟩ := (environmentReferences_erasure h l).mp ⟨v, hg, hl⟩
    hv u hu l hr⟩

theorem ResourceInterpretation.valid {w t ambient v owned}
    (h : ResourceInterpretation w t ambient v owned) : w.ValidValue v := by
  cases t <;> cases v <;> exact h.1

theorem ResourceInterpretation.references {w t ambient v owned}
    (h : ResourceInterpretation w t ambient v owned) :
    ∀ l ∈ owned, References v l := by
  cases t <;> cases v <;> exact h.2.1

theorem ResourceInterpretation.modal_iff {w t m n v owned} :
    ResourceInterpretation w (t.modal m) n v owned ↔
      ResourceInterpretation w t (m.compose n) v owned := by
  cases t <;> cases v <;>
    simp only [GroundTy.modal, ResourceInterpretation, GroundTy.mode, Mode.compose_assoc]

theorem ResourceInterpretation.global_references {w t ambient v owned}
    (hv : ResourceInterpretation w t ambient v owned)
    (hg : (t.mode.compose ambient).isLocal = false) :
    ∀ l, References v l → HeapLocation l := by
  induction t generalizing ambient v owned
  case prod a b m iha ihb =>
    cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv
    obtain ⟨_, _, hx, hy, _⟩ := hv.2.2.2
    intro l hl
    exact match hl with
    | .pairCell => hv.2.2.1.resolve_left (fun h => Bool.noConfusion (hg.symm.trans h))
    | .pairLeft hr => iha hx
        (show (a.mode.isLocal && (m.compose ambient).isLocal) = false by
          simp [show (m.compose ambient).isLocal = false from hg]) _ hr
    | .pairRight hr => ihb hy
        (show (b.mode.isLocal && (m.compose ambient).isLocal) = false by
          simp [show (m.compose ambient).isLocal = false from hg]) _ hr
  case sum a b m iha ihb =>
    cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv
    case inl =>
      exact fun l hl => match hl with
      | .inl hr => iha hv.2.2
          (show (a.mode.isLocal && (m.compose ambient).isLocal) = false by
            simp [show (m.compose ambient).isLocal = false from hg]) l hr
    case inr =>
      exact fun l hl => match hl with
      | .inr hr => ihb hv.2.2
          (show (b.mode.isLocal && (m.compose ambient).isLocal) = false by
            simp [show (m.compose ambient).isLocal = false from hg]) l hr
  all_goals cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv
  case fn.closure => exact fun l hl => hv.2.2.1 hg l (References.closure_iff.mp hl)
  case credit.credit =>
    exact fun _ hl => match hl with
    | .credit => hv.2.2.1.resolve_left (fun h => Bool.noConfusion (hg.symm.trans h))
  case unit.unit => exact fun _ h => nomatch h

theorem ResourceInterpretation.shared_resources {w t ambient v owned}
    (hv : ResourceInterpretation w t ambient v owned)
    (hm : (t.mode.compose ambient).once = false)
    (ha : (t.mode.compose ambient).unique = false) : owned = ∅ := by
  induction t generalizing ambient v owned
  all_goals cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv
  case prod.pair a b m iha ihb l x y =>
    obtain ⟨first, second, hx, hy, _, _, _, heq⟩ := hv.2.2.2
    have hx0 := iha hx
      (show (a.mode.once && (m.compose ambient).once) = false by
        simp [show (m.compose ambient).once = false from hm])
      (show (a.mode.unique && (m.compose ambient).unique) = false by
        simp [show (m.compose ambient).unique = false from ha])
    have hy0 := ihb hy
      (show (b.mode.once && (m.compose ambient).once) = false by
        simp [show (m.compose ambient).once = false from hm])
      (show (b.mode.unique && (m.compose ambient).unique) = false by
        simp [show (m.compose ambient).unique = false from ha])
    simpa [cellResources, show (m.compose ambient).unique = false from ha, hx0, hy0] using heq
  case sum.inl a b m iha _ x =>
    exact iha hv.2.2
      (show (a.mode.once && (m.compose ambient).once) = false by
        simp [show (m.compose ambient).once = false from hm])
      (show (a.mode.unique && (m.compose ambient).unique) = false by
        simp [show (m.compose ambient).unique = false from ha])
  case sum.inr a b m _ ihb x =>
    exact ihb hv.2.2
      (show (b.mode.once && (m.compose ambient).once) = false by
        simp [show (m.compose ambient).once = false from hm])
      (show (b.mode.unique && (m.compose ambient).unique) = false by
        simp [show (m.compose ambient).unique = false from ha])
  case fn.closure => exact hv.2.2.2.1 hm
  case unit.unit => exact hv.2.2
  case credit.credit m l =>
    simpa [cellResources, show (m.compose ambient).unique = false from ha] using hv.2.2.2

/-- All capture metadata, including metadata in nested polymorphic closures, is
erasable even when reasoning about the exact same ownership evidence. -/
theorem ResourceInterpretation.erasure {w t ambient v u owned}
    (hv : ResourceInterpretation w t ambient v owned) (he : ValueErasure v u) :
    ResourceInterpretation w t ambient u owned := by
  induction t generalizing w ambient v u owned
  case fn a b m _ ihb =>
    cases he <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv ⊢
    rename_i γ δ Γ Δ t u henv hbody
    have hc : ValueErasure (.closure γ Γ t) (.closure δ Δ u) := .closure henv hbody
    refine ⟨hc.valid hv.1, fun l hl => (hc.references l).mp (hv.2.1 l hl),
      fun hm l hl => hv.2.2.1 hm l ((environmentReferences_erasure henv l).mpr hl),
      hv.2.2.2.1, ?_⟩
    intro w' x argument hδ hx hd supplies hsup
    obtain ⟨result, resources, heval, hr, hbound⟩ := hv.2.2.2.2 w' x argument
      ((environmentValid_erasure henv).mpr hδ) hx hd supplies
      ((World.compatible_erasure (.cons (.refl x) henv)).mpr hsup)
    obtain ⟨result', heval', he'⟩ := heval.annotation_erasure (.cons (.refl x) henv) hbody
    exact ⟨result', resources, heval', ihb hr he', hbound⟩
  case prod a b m iha ihb =>
    cases he <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv ⊢
    rename_i l x y x' y' hx hy
    obtain ⟨first, second, ha, hb, hd⟩ := hv.2.2.2
    exact ⟨(ValueErasure.pair hx hy).valid hv.1,
      fun k hk => ((ValueErasure.pair hx hy).references k).mp (hv.2.1 k hk),
      hv.2.2.1, first, second, iha ha hx, ihb hb hy, hd⟩
  case sum a b m iha ihb =>
    cases he <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv ⊢
    case inl x y he =>
      exact ⟨(ValueErasure.inl he).valid hv.1,
        fun l hl => ((ValueErasure.inl he).references l).mp (hv.2.1 l hl), iha hv.2.2 he⟩
    case inr x y he =>
      exact ⟨(ValueErasure.inr he).valid hv.1,
        fun l hl => ((ValueErasure.inr he).references l).mp (hv.2.1 l hl), ihb hv.2.2 he⟩
  all_goals cases he <;> simp_all [ResourceInterpretation]

/-- Lookup uses the evidence for its selected instance, without interpreting the
closure's old capture annotations using a different ambient assignment. -/
theorem ResourceEnvironmentInterpretation.lookup {ρ w Γ γ reserved i s η ground}
    (hγ : ResourceEnvironmentInterpretation ρ w Γ γ reserved)
    (hi : Γ[i]? = some (some s)) (hη : GroundInstantiates ρ s η)
    (ht : s.body.realize η = some ground) :
    ResourceSemanticEvaluation w γ (.var i) ground (ContextResources Γ reserved) := by
  obtain ⟨v, hv, _, hs⟩ := hγ.1 i s hi
  obtain ⟨owned, ho, hr⟩ := hs η ground hη ht
  exact fun _ _ => ⟨v, owned, .var hv, hr, fun _ hl => Or.inl ⟨i, s, hi, ho hl⟩⟩

theorem ResourceEnvironmentInterpretation.singleton {ρ w s v reserved}
    (h : ResourceSchemeInterpretation ρ w s v reserved) :
    ResourceEnvironmentInterpretation ρ w [some s] [v] (fun _ => reserved) := by
  have index : ∀ i t, [some s][i]? = some (some t) → i = 0 ∧ t = s := by
    rintro (_ | i) t <;> simp [eq_comm]
  exact ⟨fun i t hi =>
    let ⟨hi, ht⟩ := index i t hi
    hi ▸ ht ▸ ⟨v, rfl, h⟩,
    fun i j t u hij hi hj => (hij ((index i t hi).1.trans (index j u hj).1.symm)).elim⟩

@[simp] theorem ContextResources.singleton (s : Scheme) (reserved : Resources) :
    ContextResources [some s] (fun _ => reserved) = reserved :=
  Set.ext fun _ => ⟨fun ⟨_, _, _, hl⟩ => hl, fun hl => ⟨0, s, rfl, hl⟩⟩

end ModalityInference
