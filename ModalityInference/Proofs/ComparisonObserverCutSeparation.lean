import ModalityInference.Proofs.ComparisonAlgebraOrder

/-! Boolean observers separate whole nonempty cuts. This is the compactness
step for lower and upper semantic shadows; it does not replace a non-principal
cut by any finite type. -/
namespace ModalityInference.ComparisonObserverCutSeparation

noncomputable section

open Order Set

private def liftIdeal {D : Type*} [DistribLattice D] (I : Ideal D) :
    Ideal (WithTop (WithBot D)) where
  carrier := {x | ∃ i ∈ I, x ≤ ((i : WithBot D) : WithTop (WithBot D))}
  lower' := by
    intro x y hxy hy
    obtain ⟨i,hi,hyi⟩ := hy
    exact ⟨i,hi,hxy.trans hyi⟩
  nonempty' := by
    obtain ⟨i,hi⟩ := I.nonempty
    exact ⟨((i : WithBot D) : WithTop (WithBot D)),i,hi,le_rfl⟩
  directed' := by
    intro x hx y hy
    obtain ⟨i,hi,hxi⟩ := hx
    obtain ⟨j,hj,hyj⟩ := hy
    refine ⟨(((i ⊔ j) : WithBot D) : WithTop (WithBot D)), ⟨i ⊔ j,I.sup_mem hi hj,le_rfl⟩, ?_, ?_⟩
    · exact hxi.trans (WithTop.coe_mono (WithBot.coe_mono (le_sup_left : i ≤ i ⊔ j)))
    · exact hyj.trans (WithTop.coe_mono (WithBot.coe_mono (le_sup_right : j ≤ i ⊔ j)))

private def liftFilter {D : Type*} [DistribLattice D] (F : PFilter D) :
    PFilter (WithTop (WithBot D)) :=
  (IsPFilter.of_def (F := {x | ∃ f ∈ F, ((f : WithBot D) : WithTop (WithBot D)) ≤ x})
    (by obtain ⟨f,hf⟩ := F.nonempty; exact ⟨((f : WithBot D) : WithTop (WithBot D)),f,hf,le_rfl⟩)
    (by
      intro x hx y hy
      obtain ⟨f,hf,hfx⟩ := hx
      obtain ⟨g,hg,hgy⟩ := hy
      refine ⟨(((f ⊓ g) : WithBot D) : WithTop (WithBot D)), ⟨f ⊓ g,F.inf_mem hf hg,le_rfl⟩, ?_, ?_⟩
      · exact (WithTop.coe_mono (WithBot.coe_mono (inf_le_left : f ⊓ g ≤ f))).trans hfx
      · exact (WithTop.coe_mono (WithBot.coe_mono (inf_le_right : f ⊓ g ≤ g))).trans hgy)
    (by
      intro x y hxy hx
      obtain ⟨f,hf,hfx⟩ := hx
      exact ⟨f,hf,hfx.trans hxy⟩)).toPFilter

/-- An arbitrary nonempty filter and ideal can be separated at once, including
when the distributive lattice has no least or greatest element. -/
theorem filter_ideal_separator {D : Type*} [DistribLattice D]
    (F : PFilter D) (I : Ideal D) (hd : Disjoint (F : Set D) (I : Set D)) :
    ∃ f : LatticeHom D Bool, (∀ x ∈ F, f x = true) ∧ (∀ x ∈ I, f x = false) := by
  classical
  have hdi : Disjoint (↑(liftFilter F) : Set (WithTop (WithBot D))) (↑(liftIdeal I) : Set (WithTop (WithBot D))) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,ha,hax⟩ := hx
    obtain ⟨b,hb,hxb⟩ := hy
    have hab : a ≤ b := by exact_mod_cast hax.trans hxb
    exact Set.disjoint_left.mp hd (F.mem_of_le hab ha) hb
  obtain ⟨J,hJ,hIJ,hFJ⟩ := DistribLattice.prime_ideal_of_disjoint_filter_ideal hdi
  let value := fun x : WithTop (WithBot D) => decide (x ∉ J)
  let g : LatticeHom (WithTop (WithBot D)) Bool :=
    { toFun := value
      map_sup' := by
        intro x y
        apply Bool.eq_iff_iff.mpr
        simp [value,Ideal.sup_mem_iff]
      map_inf' := by
        intro x y
        have he : x ⊓ y ∈ J ↔ x ∈ J ∨ y ∈ J :=
          ⟨hJ.mem_or_mem, fun h => h.elim (J.lower inf_le_left) (J.lower inf_le_right)⟩
        apply Bool.eq_iff_iff.mpr
        simp [value,he] }
  let f : LatticeHom D Bool :=
    { toFun := fun x => g ((x : WithBot D) : WithTop (WithBot D))
      map_sup' := by
        intro x y
        simpa only [← WithTop.coe_sup, ← WithBot.coe_sup] using
          g.map_sup' ((x : WithBot D) : WithTop (WithBot D)) ((y : WithBot D) : WithTop (WithBot D))
      map_inf' := by
        intro x y
        simpa only [← WithTop.coe_inf, ← WithBot.coe_inf] using
          g.map_inf' ((x : WithBot D) : WithTop (WithBot D)) ((y : WithBot D) : WithTop (WithBot D)) }
  refine ⟨f,?_,?_⟩
  · intro x hx
    exact decide_eq_true (Set.disjoint_left.mp hFJ (show ((x : WithBot D) : WithTop (WithBot D)) ∈ liftFilter F from ⟨x,hx,le_rfl⟩))
  · intro x hx
    exact decide_eq_false (not_not_intro (hIJ (show ((x : WithBot D) : WithTop (WithBot D)) ∈ liftIdeal I from ⟨x,hx,le_rfl⟩)))

/-- The cut below an ambient point is an ideal whenever it is inhabited. -/
def lowerCut {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) (p : L) (hp : ∃ d, e d ≤ p) : Ideal D where
  carrier := {d | e d ≤ p}
  lower' := fun _ _ h hq => (OrderHomClass.monotone e h).trans hq
  nonempty' := hp
  directed' := by
    intro d hd f hf
    exact ⟨d ⊔ f, by change e (d ⊔ f) ≤ p; rw [map_sup]; exact sup_le hd hf, le_sup_left, le_sup_right⟩

/-- The cut above an ambient point is a filter whenever it is inhabited. -/
def upperCut {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) (p : L) (hp : ∃ d, p ≤ e d) : PFilter D :=
  (IsPFilter.of_def (F := {d | p ≤ e d}) hp
    (by intro d hd f hf; exact ⟨d ⊓ f, by change p ≤ e (d ⊓ f); rw [map_inf]; exact le_inf hd hf, inf_le_left, inf_le_right⟩)
    (fun h hq => hq.trans (OrderHomClass.monotone e h))).toPFilter

/-- One observer separates all upper bounds of `p` from all lower bounds of `q`.
No principal-cut or finite-generation assumption is used. -/
theorem cut_separator {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) {p q : L} (hp : ∃ d, p ≤ e d) (hq : ∃ d, e d ≤ q)
    (hpq : ¬p ≤ q) :
    ∃ f : LatticeHom D Bool,
      (∀ d, p ≤ e d → f d = true) ∧ (∀ d, e d ≤ q → f d = false) := by
  apply filter_ideal_separator (upperCut e p hp) (lowerCut e q hq)
  exact Set.disjoint_left.mpr (fun _ h₁ h₂ => hpq (h₁.trans h₂))

def lowerShadow {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) (p : L) : Set (LatticeHom D Bool) :=
  {f | ∃ d, e d ≤ p ∧ f d = true}

def upperShadow {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) (p : L) : Set (LatticeHom D Bool) :=
  {f | ∀ d, p ≤ e d → f d = true}

/-- The order test needed for relative interval insertion is exact: an upper
shadow cannot lie below a lower shadow unless the ambient endpoints compare. -/
theorem shadow_saturation {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) {p q : L} (hp : ∃ d, p ≤ e d) (hq : ∃ d, e d ≤ q)
    (h : upperShadow e p ⊆ lowerShadow e q) : p ≤ q := by
  by_contra hpq
  obtain ⟨f,hf,hg⟩ := cut_separator e hp hq hpq
  obtain ⟨d,hd,he⟩ := h hf
  exact Bool.false_ne_true ((hg d hd).symm.trans he)

theorem shadow_consistent {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) (he : ∀{a b}, e a ≤ e b → a ≤ b) (p : L) :
    lowerShadow e p ⊆ upperShadow e p := by
  intro f hf d hd
  obtain ⟨c,hc,hv⟩ := hf
  have h := OrderHomClass.monotone f (he (hc.trans hd))
  exact (Bool.le_iff_imp.mp h) hv

theorem lowerShadow_mono {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) {p q : L} (h : p ≤ q) : lowerShadow e p ⊆ lowerShadow e q :=
  fun _ ⟨d,hd,hf⟩ => ⟨d,hd.trans h,hf⟩

theorem upperShadow_mono {D L : Type*} [DistribLattice D] [Lattice L]
    (e : LatticeHom D L) {p q : L} (h : p ≤ q) : upperShadow e p ⊆ upperShadow e q :=
  fun _ hf d hd => hf d (h.trans hd)

end
end ModalityInference.ComparisonObserverCutSeparation
