import ModalityInference.Proofs.ComparisonTupleReification
import ModalityInference.Proofs.ComparisonBasisReflection
import ModalityInference.Proofs.ComparisonBareShapes

/-! Boolean coordinate comparisons reflect into the guarded algebra for finite
generated types. Labels need only be defined under the original bounds. -/
namespace ModalityInference.ComparisonTupleReflection

open ComparisonAlgebra ComparisonControls ComparisonTupleReification ComparisonOpaqueObserver

def labels : ComparisonControls.Generated b → List ModExpr
  | .head _ _ => []
  | .join a c | .meet a c => labels a ++ labels c
  | .modal a m _ => m :: labels a

theorem labels_defined {Δ : Bounds} (g : ComparisonControls.Generated b) (hd : g.term.DefinedUnder Δ) :
    ∀ m ∈ labels g, DefinedMode Δ m := by
  induction g with
  | head a ha => simp [labels]
  | join a c iha ihc =>
    have hd := CompareTy.definedUnder_join_iff.mp hd
    simpa only [labels, List.forall_mem_append] using And.intro (iha hd.1) (ihc hd.2)
  | meet a c iha ihc =>
    have hd := CompareTy.definedUnder_meet_iff.mp hd
    simpa only [labels, List.forall_mem_append] using And.intro (iha hd.1) (ihc hd.2)
  | modal a m hm ih =>
    have hd := CompareTy.definedUnder_modal_iff.mp hd
    simpa only [labels, List.forall_mem_cons] using And.intro hd.2 (ih hd.1)

theorem interval {Δ : Bounds} {shape : ComparisonShape} (g : ComparisonControls.Generated b)
    (lower upper : Carrier Δ shape)
    (hh : ∀ a ∈ b.heads, InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) a)
    (hd : g.term.DefinedUnder Δ) :
    InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) g.term := by
  induction g with
  | head a ha => exact hh a ha
  | join a c iha ihc =>
    have hd := CompareTy.definedUnder_join_iff.mp hd
    exact InInterval.join (iha hd.1) (ihc hd.2)
  | meet a c iha ihc =>
    have hd := CompareTy.definedUnder_meet_iff.mp hd
    exact InInterval.meet (iha hd.1) (ihc hd.2)
  | modal a m hm ih =>
    have hd := CompareTy.definedUnder_modal_iff.mp hd
    exact InInterval.modal (ih hd.1) hd.2

theorem observer_value {Δ : Bounds} {shape : ComparisonShape} (g : ComparisonControls.Generated b)
    (f : LatticeHom (Order Δ shape) Bool) (lower upper : Carrier Δ shape)
    (hh : ∀ a ∈ b.heads, InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) a)
    (hd : g.term.DefinedUnder Δ) (coordinate : Coordinate) (η : ModVar → Mode)
    (hm : ∀ t, InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) t →
      ∀ m ∈ labels g, booleanValue f (.modal t m) =
        applyMode coordinate (booleanValue f t) (m.complete η)) :
    booleanValue f g.term = observe coordinate (booleanValue f) η g := by
  induction g with
  | head a ha => rfl
  | join a c iha ihc =>
    have hd := CompareTy.definedUnder_join_iff.mp hd
    rw [ComparisonControls.Generated.term, booleanValue_join, iha hd.1, ihc hd.2]
    · rfl
    · exact fun t ht m hmem => hm t ht m (List.mem_append_right _ hmem)
    · exact fun t ht m hmem => hm t ht m (List.mem_append_left _ hmem)
  | meet a c iha ihc =>
    have hd := CompareTy.definedUnder_meet_iff.mp hd
    rw [ComparisonControls.Generated.term, booleanValue_meet, iha hd.1, ihc hd.2]
    · rfl
    · exact fun t ht m hmem => hm t ht m (List.mem_append_right _ hmem)
    · exact fun t ht m hmem => hm t ht m (List.mem_append_left _ hmem)
  | modal a m hms ih =>
    have hd := CompareTy.definedUnder_modal_iff.mp hd
    rw [ComparisonControls.Generated.term, hm a.term (interval a lower upper hh hd.1) m (by simp [labels])]
    rw [ih hd.1 (fun t ht n hn => hm t ht n (List.mem_cons_of_mem _ hn))]
    rfl

theorem observer_family {Δ : Bounds} {shape : ComparisonShape}
    (family : List (ComparisonControls.Generated b))
    (f : LatticeHom (Order Δ shape) Bool) (lower upper : Carrier Δ shape)
    (hlu : lower ≤ upper)
    (hlo : observer f (lower.atMode Mode.bottom) = false)
    (hhi : observer f (upper.atMode Mode.top) = true)
    (hh : ∀ a ∈ b.heads, InInterval (lower.atMode Mode.bottom) (upper.atMode Mode.top) a)
    (hd : ∀ g ∈ family, g.term.DefinedUnder Δ) :
    ∃ coordinate η, (coordinate = Coordinate.unaffected ∨ ModeModels Δ η) ∧
      ∀ g ∈ family, booleanValue f g.term = observe coordinate (booleanValue f) η g := by
  let allLabels := family.flatMap labels
  have hlabels : ∀ m ∈ allLabels, DefinedMode Δ m := by
    intro m hm
    obtain ⟨g, hg, hm⟩ := List.mem_flatMap.mp hm
    exact labels_defined g (hd g hg) m hm
  obtain ⟨coordinate, η, hη, hmodal⟩ := observer_substituted_realizable
    f lower upper hlu hlo hhi ModExpr.var (fun η => η) (fun _ _ => rfl)
    allLabels (by simpa only [ModExpr.subst_id] using hlabels)
  refine ⟨coordinate, η, hη, ?_⟩
  intro g hg
  apply observer_value g f lower upper hh (hd g hg) coordinate η
  intro t ht m hm
  have hm' : m ∈ allLabels := List.mem_flatMap.mpr ⟨g, hg, hm⟩
  obtain ⟨ht, hlt, htu⟩ := ht
  simp only [CompareTy.subst_id] at hmodal
  have h := hmodal (encodeModes η) id (fun _ => rfl) t ht hlt htu m hm'
  apply h.trans
  rcases hη with rfl | hη
  · rfl
  · simpa only [Function.comp_id, projectedModes_encodeModes, BoolExpr.eval] using
      modalWith_value coordinate id (encodeModes η) (.const (booleanValue f t)) m
        (by simpa only [Function.comp_id, projectedModes_encodeModes] using hlabels m hm' η hη)

theorem booleanValue_mono (f : LatticeHom (Order Δ shape) Bool) {a c : CompareTy}
    (ha : Representable Δ shape a) (hc : Representable Δ shape c)
    (h : AlgebraSubtype Δ a c) : booleanValue f a = true → booleanValue f c = true := by
  simpa only [booleanValue_represented f a ha, booleanValue_represented f c hc] using
    observer_mono f (a := represented ha) (b := represented hc) h

/-- Four-coordinate validity under established scalar and type bounds implies
the guarded algebraic inequality for the generated types. -/
theorem subtype_of_coordinates {Δ : Bounds} {shape : ComparisonShape}
    (a c : ComparisonControls.Generated b)
    (premises : List (ComparisonControls.Generated b × ComparisonControls.Generated b))
    (hh : ∀ t ∈ b.heads, Representable Δ shape t)
    (ha : a.term.DefinedUnder Δ) (hc : c.term.DefinedUnder Δ)
    (hp : ∀ pair ∈ premises,
      pair.1.term.DefinedUnder Δ ∧ pair.2.term.DefinedUnder Δ ∧
        AlgebraSubtype Δ pair.1.term pair.2.term)
    (h : ∀ coordinate η heads,
      (coordinate = Coordinate.unaffected ∨ ModeModels Δ η) →
      (∀ pair ∈ premises, observe coordinate heads η pair.1 = true →
        observe coordinate heads η pair.2 = true) →
      observe coordinate heads η a = true → observe coordinate heads η c = true) :
    AlgebraSubtype Δ a.term c.term := by
  obtain ⟨lower, upper, _, _, hlu, hheads, _, _⟩ := b.carrier_interval
    CompareTy.var ModExpr.var (by simpa only [CompareTy.subst_id] using hh)
    (fun _ _ _ _ => rfl)
  simp only [CompareTy.subst_id] at hheads
  obtain ⟨haRep, hla, hau⟩ := interval a lower upper hheads ha
  obtain ⟨hcRep, hlc, hcu⟩ := interval c lower upper hheads hc
  apply (subtype_iff_boolean_observers (represented haRep) (represented hcRep)).mpr
  intro f
  cases hlo : observer f (lower.atMode Mode.bottom) with
  | true => exact Bool.le_iff_imp.mpr (fun _ => observer_mono f hlc hlo)
  | false =>
    cases hhi : observer f (upper.atMode Mode.top) with
    | false => exact Bool.le_iff_imp.mpr (fun hx =>
        False.elim (Bool.noConfusion (hhi.symm.trans (observer_mono f hau hx))))
    | true =>
      let family := a :: c :: premises.flatMap (fun pair => [pair.1, pair.2])
      have hfamily : ∀ g ∈ family, g.term.DefinedUnder Δ := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ha
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hc
        obtain ⟨pair, hp', hg⟩ := List.mem_flatMap.mp hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact (hp pair hp').1
        have he : g = pair.2 := List.mem_singleton.mp hg
        exact he ▸ (hp pair hp').2.1
      obtain ⟨coordinate, η, hη, he⟩ := observer_family family f lower upper hlu hlo hhi hheads hfamily
      have hea := he a (by simp [family])
      have hec := he c (by simp [family])
      apply Bool.le_iff_imp.mpr
      intro hx
      have hax : observe coordinate (booleanValue f) η a = true := by
        rw [← hea, booleanValue_represented f a.term haRep]
        exact hx
      have hcx := h coordinate η (booleanValue f) hη (by
        intro pair hp'
        have hmem : ∀ g ∈ [pair.1, pair.2], g ∈ family := fun g hg =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨pair, hp', hg⟩))
        rw [← he pair.1 (hmem _ (by simp)), ← he pair.2 (hmem _ (by simp))]
        exact booleanValue_mono f (interval pair.1 lower upper hheads (hp pair hp').1).1
          (interval pair.2 lower upper hheads (hp pair hp').2.1).1 (hp pair hp').2.2) hax
      rw [← hec, booleanValue_represented f c.term hcRep] at hcx
      exact hcx

end ModalityInference.ComparisonTupleReflection
