import ModalityInference.Proofs.Resources

/-! Subtyping transports ownership evidence to a subset of the source evidence. -/
namespace ModalityInference

def ResourceLe (a b : GroundTy) : Prop :=
  ∀ w ambient v owned, ResourceInterpretation w a ambient v owned →
    ∃ target, target ⊆ owned ∧ ResourceInterpretation w b ambient v target

theorem ResourceLe.refl (a : GroundTy) : ResourceLe a a :=
  fun _ _ _ owned hv => ⟨owned, Set.Subset.rfl, hv⟩

theorem cellResources_mono {m n : Mode}
    (h : n.unique = true → m.unique = true) (l : Location) :
    cellResources n l ⊆ cellResources m l := by
  cases hm : m.unique <;> cases hn : n.unique <;> simp_all [cellResources]

theorem ResourceLe.fn {a b c d m n}
    (hac : ResourceLe c a) (hbd : ResourceLe b d)
    (hl : m.isLocal = true → n.isLocal = true)
    (hf : m.once = true → n.once = true) :
    ResourceLe (.fn a b m) (.fn c d n) := by
  intro w ambient v owned hv
  cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv ⊢
  have hfuture :
      ((m.compose ambient).isLocal = true → (n.compose ambient).isLocal = true) ∧
      ((m.compose ambient).once = true → (n.compose ambient).once = true) :=
    ⟨fun h => Bool.and_eq_true_iff.mpr
      ⟨hl (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩,
     fun h => Bool.and_eq_true_iff.mpr
      ⟨hf (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩⟩
  refine ⟨owned, Set.Subset.rfl, hv.1, hv.2.1,
    fun hn => hv.2.2.1 (Bool.eq_false_iff.mpr (mt hfuture.1 (Bool.eq_false_iff.mp hn))),
    fun hn => hv.2.2.2.1 (Bool.eq_false_iff.mpr (mt hfuture.2 (Bool.eq_false_iff.mp hn))), ?_⟩
  intro w' x argument hγ hx hd supplies hs
  obtain ⟨argument', ha, hx'⟩ := hac w' Mode.identity x argument hx
  obtain ⟨result, resources, he, hr, hb⟩ :=
    hv.2.2.2.2 w' x argument' hγ hx' (hd.mono_right ha) supplies hs
  obtain ⟨target, hsub, ht⟩ := hbd w' Mode.identity result resources hr
  exact ⟨result, target, he, ht,
    hsub.trans (hb.trans (Set.union_subset_union (Set.union_subset_union_right _ ha) Set.Subset.rfl))⟩

theorem ResourceInterpretation.mode_mono {w t v owned} {m n : Mode}
    (h : m.le n = true) (hv : ResourceInterpretation w t m v owned) :
    ∃ target, target ⊆ owned ∧ ResourceInterpretation w t n v target := by
  induction t generalizing m n v owned
  all_goals cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv ⊢
  case prod.pair a b p iha ihb l x y =>
    obtain ⟨first, second, hx, hy, hcx, hcy, hxy, heq⟩ := hv.2.2.2
    obtain ⟨⟨first', hfirst, hx'⟩, ⟨second', hsecond, hy'⟩⟩ :=
      And.intro (iha (Mode.compose_le_left p h) hx) (ihb (Mode.compose_le_left p h) hy)
    have hcell := cellResources_mono ((Mode.le_iff _ _).mp (Mode.compose_le_left p h)).2.2 l
    have hsub : cellResources (p.compose n) l ∪ first' ∪ second' ⊆ owned :=
      heq ▸ Set.union_subset_union (Set.union_subset_union hcell hfirst) hsecond
    exact ⟨_, hsub, hv.1, fun k hk => hv.2.1 k (hsub hk),
      hv.2.2.1.imp ((Mode.le_iff _ _).mp (Mode.compose_le_left p h)).1 id,
      first', second', hx', hy', hcx.mono hcell hfirst,
      hcy.mono hcell hsecond, hxy.mono hfirst hsecond, rfl⟩
  case fn.closure a b p _ _ γ captured body =>
    exact let hp := (Mode.le_iff _ _).mp (Mode.compose_le_left p h)
      ⟨owned, Set.Subset.rfl, hv.1, hv.2.1,
        fun hn => hv.2.2.1 (Bool.eq_false_iff.mpr (mt hp.1 (Bool.eq_false_iff.mp hn))),
        fun hn => hv.2.2.2.1 (Bool.eq_false_iff.mpr (mt hp.2.1 (Bool.eq_false_iff.mp hn))),
        hv.2.2.2.2⟩
  case credit.credit p l =>
    exact let hp := (Mode.le_iff _ _).mp (Mode.compose_le_left p h)
      let hc := hv.2.2.2 ▸ cellResources_mono hp.2.2 l
      ⟨cellResources (p.compose n) l, hc, hv.1,
        fun k hk => hv.2.1 k (hc hk), hv.2.2.1.imp hp.1 id, rfl⟩
  case sum.inl a b p iha _ x =>
    exact let ⟨target, ht, hx⟩ := iha (Mode.compose_le_left p h) hv.2.2
      ⟨target, ht, hv.1, fun k hk => hv.2.1 k (ht hk), hx⟩
  case sum.inr a b p _ ihb x =>
    exact let ⟨target, ht, hx⟩ := ihb (Mode.compose_le_left p h) hv.2.2
      ⟨target, ht, hv.1, fun k hk => hv.2.1 k (ht hk), hx⟩
  case unit.unit => exact ⟨owned, Set.Subset.rfl, hv⟩

theorem ResourceLe.trans {a b c} (hab : ResourceLe a b) (hbc : ResourceLe b c) :
    ResourceLe a c :=
  fun w ambient v owned hv =>
    let ⟨middle, hm, hb⟩ := hab w ambient v owned hv
    let ⟨target, ht, hc⟩ := hbc w ambient v middle hb
    ⟨target, ht.trans hm, hc⟩

theorem ResourceLe.modal {a b} {m n : Mode} (hab : ResourceLe a b)
    (hmn : m.le n = true) : ResourceLe (a.modal m) (b.modal n) := by
  intro w ambient v owned hv
  obtain ⟨middle, hm, hb⟩ := hab w (m.compose ambient) v owned
    (ResourceInterpretation.modal_iff.mp hv)
  obtain ⟨target, ht, hc⟩ := hb.mode_mono (Mode.compose_le_right ambient hmn)
  exact ⟨target, ht.trans hm, ResourceInterpretation.modal_iff.mpr hc⟩

theorem ResourceLe.prod {a b c d m}
    (hac : ResourceLe (a.modal m) (c.modal m))
    (hbd : ResourceLe (b.modal m) (d.modal m)) :
    ResourceLe (.prod a b m) (.prod c d m) := by
  intro w ambient v owned hv
  cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv ⊢
  rename_i l x y
  obtain ⟨first, second, hx, hy, hcx, hcy, hxy, heq⟩ := hv.2.2.2
  obtain ⟨⟨first', hfirst, hx'⟩, ⟨second', hsecond, hy'⟩⟩ :=
    And.intro (hac w ambient x first (ResourceInterpretation.modal_iff.mpr hx))
      (hbd w ambient y second (ResourceInterpretation.modal_iff.mpr hy))
  have hsub : cellResources (m.compose ambient) l ∪ first' ∪ second' ⊆ owned :=
    heq ▸ Set.union_subset_union (Set.union_subset_union_right _ hfirst) hsecond
  exact ⟨_, hsub, hv.1, fun k hk => hv.2.1 k (hsub hk), hv.2.2.1,
    first', second', ResourceInterpretation.modal_iff.mp hx', ResourceInterpretation.modal_iff.mp hy',
    hcx.mono_right hfirst, hcy.mono_right hsecond, hxy.mono hfirst hsecond, rfl⟩

theorem ResourceLe.sum {a b c d m}
    (hac : ResourceLe (a.modal m) (c.modal m))
    (hbd : ResourceLe (b.modal m) (d.modal m)) :
    ResourceLe (.sum a b m) (.sum c d m) := by
  intro w ambient v owned hv
  cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv ⊢
  case inl x =>
    exact let ⟨target, ht, hx⟩ := hac w ambient x owned (ResourceInterpretation.modal_iff.mpr hv.2.2)
      ⟨target, ht, hv.1, fun k hk => hv.2.1 k (ht hk), ResourceInterpretation.modal_iff.mp hx⟩
  case inr x =>
    exact let ⟨target, ht, hx⟩ := hbd w ambient x owned (ResourceInterpretation.modal_iff.mpr hv.2.2)
      ⟨target, ht, hv.1, fun k hk => hv.2.1 k (ht hk), ResourceInterpretation.modal_iff.mp hx⟩

theorem ResourceLe.credit {m n : Mode}
    (hl : m.isLocal = true → n.isLocal = true)
    (hu : n.unique = true → m.unique = true) : ResourceLe (.credit m) (.credit n) := by
  intro w ambient v owned hv
  cases v <;> simp only [ResourceInterpretation, GroundTy.mode, and_false] at hv ⊢
  have haxes :
      ((m.compose ambient).isLocal = true → (n.compose ambient).isLocal = true) ∧
      ((n.compose ambient).unique = true → (m.compose ambient).unique = true) :=
    ⟨fun h => Bool.and_eq_true_iff.mpr
      ⟨hl (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩,
     fun h => Bool.and_eq_true_iff.mpr
      ⟨hu (Bool.and_eq_true_iff.mp h).1, (Bool.and_eq_true_iff.mp h).2⟩⟩
  exact let hc := hv.2.2.2 ▸ cellResources_mono haxes.2 _
    ⟨_, hc, hv.1, fun k hk => hv.2.1 k (hc hk), hv.2.2.1.imp haxes.1 id, rfl⟩

private def OptResourceLe : Option GroundTy → Option GroundTy → Prop
  | none, none => True
  | some a, some b => ResourceLe a b
  | _, _ => False

private theorem OptResourceLe.refl (a : Option GroundTy) : OptResourceLe a a :=
  match a with
  | none => trivial
  | some a => ResourceLe.refl a

private theorem OptResourceLe.trans {a b c} (hab : OptResourceLe a b) (hbc : OptResourceLe b c) :
    OptResourceLe a c := by
  cases a <;> cases b <;> cases c <;> simp only [OptResourceLe] at *
  all_goals first | trivial | exact ResourceLe.trans hab hbc

private theorem Subtype.optResourceLe_of_bounds {ρ Δ a b} (h : Subtype Δ a b)
    (hmodes : ModeModels Δ ρ.modes)
    (hbounds : ∀ a b, Constraint.sub a b ∈ Δ → OptResourceLe (a.realize ρ) (b.realize ρ)) :
    OptResourceLe (a.realize ρ) (b.realize ρ) := by
  induction h
  case fn a b c d m n _ _ hmode iha ihb =>
    have hmn := hmode.denote hmodes
    cases hm : m.eval (some ∘ ρ.modes) <;> cases hn : n.eval (some ∘ ρ.modes) <;>
      simp [ModExpr.Below, ModExpr.eval, ModExpr.top, hm, hn, Mode.le_iff, Mode.compose, Mode.top] at hmn
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      simp_all [OptResourceLe, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    exact ResourceLe.fn iha ihb hmn.1 hmn.2
  case prod a b c d m _ _ iha ihb | sum a b c d m _ _ iha ihb =>
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      cases hc : c.realize ρ <;> cases hd : d.realize ρ <;>
      cases hm : m.eval (some ∘ ρ.modes) <;>
      simp_all [OptResourceLe, TypeExpr.realize, GroundTy.modal, Mode.identity_compose]
    all_goals first | exact ResourceLe.prod iha ihb | exact ResourceLe.sum iha ihb
  case congr a b m n _ hmode ih =>
    obtain ⟨u, v, hm, hn, huv⟩ := hmode.denote hmodes
    cases ha : a.realize ρ <;> cases hb : b.realize ρ <;>
      simp_all [OptResourceLe, TypeExpr.realize]
    exact ResourceLe.modal ih huv
  all_goals try simp only [TypeExpr.realize_identity, TypeExpr.realize_compose]
  all_goals solve_by_elim [OptResourceLe.refl, OptResourceLe.trans]

private theorem Subtype.optResourceLe_empty {ρ a b} (h : Subtype [] a b) :
    OptResourceLe (a.realize ρ) (b.realize ρ) :=
  h.optResourceLe_of_bounds (by simp [ModeModels]) (by simp)

/-- All declarative subtyping rules, including modeled symbolic bounds, preserve
the instance-indexed interpretation under arbitrary inherited modalities. -/
theorem Subtype.resourceLe {ρ Δ a b x y} (h : Subtype Δ a b) (hΔ : GroundModels ρ Δ)
    (ha : a.realize ρ = some x) (hb : b.realize ρ = some y) : ResourceLe x y := by
  have hs : OptResourceLe (a.realize ρ) (b.realize ρ) :=
    h.optResourceLe_of_bounds hΔ.modeModels fun c d hcd => by
      obtain ⟨u, v, hc, hd, huv⟩ := hΔ _ hcd
      simpa only [hc, hd, GroundTy.realize_reify] using huv.optResourceLe_empty (ρ := ρ)
  simpa only [ha, hb] using hs

/-- Conversion may discard ownership but cannot introduce owned locations. -/
theorem Subtype.resource_semantic {ρ w Δ a b x y v ambient owned} (h : Subtype Δ a b)
    (hΔ : GroundModels ρ Δ) (ha : a.realize ρ = some x) (hb : b.realize ρ = some y)
    (hv : ResourceInterpretation w x ambient v owned) :
    ∃ target, target ⊆ owned ∧ ResourceInterpretation w y ambient v target :=
  h.resourceLe hΔ ha hb w ambient v owned hv

end ModalityInference
