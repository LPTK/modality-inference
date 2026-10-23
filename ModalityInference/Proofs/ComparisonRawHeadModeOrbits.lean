import ModalityInference.Proofs.ComparisonObserverProfiles
import ModalityInference.Proofs.ComparisonRawHeadTables
import ModalityInference.Proofs.SymbolicSchemeModes

/-! A finite executable family of total modal labels covers every total label
on a fixed list of names. Label equivalence acts on arbitrary partial heads;
no equation is used inside a partial payload. -/
namespace ModalityInference.ComparisonRawHeadModeOrbits

open ComparisonControls ComparisonObserverProfiles

private def branch (i : Nat) (yes no : BoolExpr) : BoolExpr :=
  .or (.and (.atom i) yes) (.and (.imp (.atom i) (.const false)) no)

/-- All truth tables over these atoms, reified by their two cofactors. -/
def truthForms : List Nat → List BoolExpr
  | [] => [.const false, .const true]
  | i :: is => (truthForms is).flatMap fun yes =>
      (truthForms is).map fun no => branch i yes no

private def cofactor (e : BoolExpr) (i : Nat) (b : Bool) : BoolExpr :=
  SymbolicCNF.substitute (fun j => if j = i then .const b else .atom j) e

private theorem cofactor_support {e : BoolExpr} {i : Nat} {is : List Nat}
    (h : ∀ j ∈ e.atoms, j ∈ i :: is) (b : Bool) :
    ∀ j ∈ (cofactor e i b).atoms, j ∈ is := by
  intro j hj
  obtain ⟨k,hk,hj⟩ := SymbolicCNF.substitute_atoms hj
  by_cases hki : k = i
  · simp [hki, BoolExpr.atoms] at hj
  · simp only [if_neg hki, BoolExpr.atoms, List.mem_singleton] at hj
    subst j
    exact (List.mem_cons.mp (h k hk)).resolve_left hki

private theorem cofactor_self (e : BoolExpr) (i : Nat) (σ : Nat → Bool) :
    (cofactor e i (σ i)).eval σ = e.eval σ := by
  rw [cofactor, SymbolicCNF.substitute_eval]
  apply SymbolicModes.eval_congr
  intro j _
  by_cases hj : j = i <;> simp [hj, BoolExpr.eval]

/-- The enumeration covers all supported Boolean expressions extensionally. -/
theorem truthForms_complete (is : List Nat) (e : BoolExpr)
    (h : ∀ i ∈ e.atoms, i ∈ is) :
    ∃ f ∈ truthForms is, ∀ σ, f.eval σ = e.eval σ := by
  induction is generalizing e with
  | nil =>
    refine ⟨.const (e.eval (fun _ => false)), ?_, ?_⟩
    · cases e.eval (fun _ => false) <;> simp [truthForms]
    · intro σ
      exact SymbolicModes.eval_congr e (fun i hi => False.elim (List.not_mem_nil (h i hi)))
  | cons i is ih =>
    obtain ⟨yes,hy,ey⟩ := ih (cofactor e i true) (cofactor_support h true)
    obtain ⟨no,hn,en⟩ := ih (cofactor e i false) (cofactor_support h false)
    refine ⟨branch i yes no, List.mem_flatMap.mpr ⟨yes,hy,List.mem_map.mpr ⟨no,hn,rfl⟩⟩, ?_⟩
    intro σ
    cases hs : σ i
    · simpa only [branch, BoolExpr.eval, hs, Bool.false_and, Bool.not_false,
        Bool.false_or, Bool.or_false, Bool.true_and, en σ] using cofactor_self e i σ
    · simpa only [branch, BoolExpr.eval, hs, Bool.true_and, Bool.not_true,
        Bool.false_or, Bool.or_false, Bool.false_and, ey σ] using cofactor_self e i σ

theorem truthForms_support {is f} (h : f ∈ truthForms is) :
    ∀ i ∈ f.atoms, i ∈ is := by
  induction is generalizing f with
  | nil =>
    simp only [truthForms, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp [BoolExpr.atoms]
  | cons i is ih =>
    obtain ⟨yes,hy,h⟩ := List.mem_flatMap.mp h
    obtain ⟨no,hn,rfl⟩ := List.mem_map.mp h
    intro j hj
    simp only [branch, BoolExpr.atoms, List.mem_dedup, List.mem_append,
      List.mem_singleton, List.not_mem_nil, or_false] at hj
    rcases hj with (rfl | hj) | (rfl | hj)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hy j hj)
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hn j hj)


def channelAtoms : Channel → List ModVar → List Nat
  | .locality, names => names.map (fun v => v.atomIndex 0)
  | .affinity, names | .lower, names =>
      names.flatMap (fun v => [v.atomIndex 1, v.atomIndex 2])

theorem mem_channelAtoms (c : Channel) (names : List ModVar) (i : Nat) :
    i ∈ channelAtoms c names ↔ c.Accepts i ∧ SymbolicModes.atomVariable i ∈ names := by
  cases c with
  | locality =>
    constructor
    · rintro hi
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hi
      exact ⟨atomIndex_mod v 0 (by decide), by simpa only [atomVariable_atomIndex v 0 (by decide)] using hv⟩
    · rintro ⟨hi,hv⟩
      change i % 3 = 0 at hi
      exact List.mem_map.mpr ⟨SymbolicModes.atomVariable i,hv,by
        simpa only [hi] using SymbolicSchemeModes.atomVariable_reencode i⟩
  | affinity | lower =>
    constructor
    · intro hi
      obtain ⟨v,hv,hi⟩ := List.mem_flatMap.mp hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ⟨by simp [Channel.Accepts, atomIndex_mod v 1 (by decide)],
          by simpa only [atomVariable_atomIndex v 1 (by decide)] using hv⟩
      · exact ⟨by simp [Channel.Accepts, atomIndex_mod v 2 (by decide)],
          by simpa only [atomVariable_atomIndex v 2 (by decide)] using hv⟩
    · rintro ⟨hi,hv⟩
      have hb : i % 3 < 3 := Nat.mod_lt _ (by decide)
      have h0 : i % 3 ≠ 0 := hi
      obtain h1 | h2 : i % 3 = 1 ∨ i % 3 = 2 := by omega
      · exact List.mem_flatMap.mpr ⟨SymbolicModes.atomVariable i,hv,
          by simpa only [← h1, SymbolicSchemeModes.atomVariable_reencode] using
            (List.mem_cons_self : (SymbolicModes.atomVariable i).atomIndex 1 ∈
              [(SymbolicModes.atomVariable i).atomIndex 1, (SymbolicModes.atomVariable i).atomIndex 2])⟩
      · exact List.mem_flatMap.mpr ⟨SymbolicModes.atomVariable i,hv,
          by simpa only [← h2, SymbolicSchemeModes.atomVariable_reencode] using
            (List.mem_cons_of_mem _ List.mem_cons_self : (SymbolicModes.atomVariable i).atomIndex 2 ∈
              [(SymbolicModes.atomVariable i).atomIndex 1, (SymbolicModes.atomVariable i).atomIndex 2])⟩

private def combine (localPart affine unique : BoolExpr) : ModExpr :=
  .compose (band .locality localPart true)
    (.compose (band .affinity affine true) (band .lower unique false))

/-- The finite family is independent of the ambient assumptions. Every member
is globally total and uses only the supplied names. -/
def representatives (names : List ModVar) : List ModExpr :=
  (truthForms (channelAtoms .locality names)).flatMap fun localPart =>
    (truthForms (channelAtoms .affinity names)).flatMap fun affine =>
      (truthForms (channelAtoms .lower names)).map fun unique => combine localPart affine unique

private theorem forms_generated {names : List ModVar} {c f}
    (h : f ∈ truthForms (channelAtoms c names)) (p : Bool) :
    ComparisonObserverProfiles.Generated names.toFinset (band c f p) :=
  band_generated (fun i hi => let h := (mem_channelAtoms c names i).mp (truthForms_support h i hi)
    ⟨h.1,List.mem_toFinset.mpr h.2⟩) p

theorem representatives_generated {names r} (h : r ∈ representatives names) :
    ComparisonObserverProfiles.Generated names.toFinset r := by
  obtain ⟨localPart,hl,h⟩ := List.mem_flatMap.mp h
  obtain ⟨affine,ha,h⟩ := List.mem_flatMap.mp h
  obtain ⟨unique,hu,rfl⟩ := List.mem_map.mp h
  exact .compose (forms_generated hl true)
    (.compose (forms_generated ha true) (forms_generated hu false))

theorem representatives_total {Δ names r} (h : r ∈ representatives names) :
    Entails Δ (.defined r) := (representatives_generated h).defined

theorem representatives_support {names r} (h : r ∈ representatives names) :
    r.vars ⊆ names.toFinset := by
  have hg := representatives_generated h
  clear h
  induction hg with
  | const m => simp [ModExpr.vars]
  | control q hq => simpa only [control_vars,Finset.singleton_subset_iff] using hq
  | compose _ _ ih₁ ih₂ | join _ _ ih₁ ih₂ | meet _ _ ih₁ ih₂ =>
    exact Finset.union_subset ih₁ ih₂


private theorem forms_accepts {names c f} (h : f ∈ truthForms (channelAtoms c names)) :
    ∀ i ∈ f.atoms, c.Accepts i :=
  fun i hi => ((mem_channelAtoms c names i).mp (truthForms_support h i hi)).1

/-- Every supported label that is total under the assumptions has an equivalent
member of the finite globally total family. The payload is not part of this normalization. -/
theorem representatives_complete {Δ : Bounds} {names : List ModVar} {m : ModExpr}
    (hm : Entails Δ (.defined m)) (hs : m.vars ⊆ names.toFinset) :
    ∃ r ∈ representatives names, Submode Δ m r ∧ Submode Δ r m := by
  have hp := project_support m
  have hl : ∀ i ∈ m.project.locality.atoms, i ∈ channelAtoms .locality names := by
    intro i hi
    exact (mem_channelAtoms _ _ _).mpr ⟨(hp.1 i hi).1,
      List.mem_toFinset.mp (hs ((ModExpr.mem_freeVariables _ _).mp (hp.1 i hi).2))⟩
  have ha : ∀ i ∈ m.project.affinity.atoms, i ∈ channelAtoms .affinity names := by
    intro i hi
    exact (mem_channelAtoms _ _ _).mpr ⟨(hp.2.1 i hi).1,
      List.mem_toFinset.mp (hs ((ModExpr.mem_freeVariables _ _).mp (hp.2.1 i hi).2))⟩
  have hu : ∀ i ∈ m.project.uniqueness.atoms, i ∈ channelAtoms .lower names := by
    intro i hi
    exact (mem_channelAtoms _ _ _).mpr ⟨(hp.2.2 i hi).1,
      List.mem_toFinset.mp (hs ((ModExpr.mem_freeVariables _ _).mp (hp.2.2 i hi).2))⟩
  obtain ⟨lf,hlf,elf⟩ := truthForms_complete _ _ hl
  obtain ⟨af,haf,eaf⟩ := truthForms_complete _ _ ha
  obtain ⟨uf,huf,euf⟩ := truthForms_complete _ _ hu
  have hr : combine lf af uf ∈ representatives names :=
    List.mem_flatMap.mpr ⟨lf,hlf,List.mem_flatMap.mpr ⟨af,haf,List.mem_map.mpr ⟨uf,huf,rfl⟩⟩⟩
  have he (η : ModVar → Mode) (hη : ModeModels Δ η) :
      (combine lf af uf).eval (some ∘ η) = m.eval (some ∘ η) := by
    rw [← normal_eval hm hη]
    simp only [combine, normal, ModExpr.eval,
      band_eval (forms_accepts hlf), band_eval (forms_accepts haf), band_eval (forms_accepts huf),
      band_eval (c := .locality) (fun i hi => (hp.1 i hi).1), band_eval (c := .affinity) (fun i hi => (hp.2.1 i hi).1),
      band_eval (c := .lower) (fun i hi => (hp.2.2 i hi).1), elf, eaf, euf]
  refine ⟨combine lf af uf,hr,Submode.valid ?_,Submode.valid ?_⟩
  all_goals intro η hη
  all_goals simpa only [ModExpr.Below, he η hη] using (Submode.refl hm).denote hη

/-- Equivalent total labels can be exchanged on an arbitrary supported partial
head. No definedness assumption is made about the body. -/
theorem head_orbit_complete {Δ H names a m}
    (hc : ComparisonRawHeadRestriction.Carrier Δ H (.modal a m))
    (ha : CompareTy.WellShaped Δ a) (hm : Entails Δ (.defined m))
    (hs : m.vars ⊆ names.toFinset) :
    ∃ r ∈ representatives names,
      ComparisonRawHeadRestriction.Derivation Δ H (.modal a m) (.modal a r) ∧
      ComparisonRawHeadRestriction.Derivation Δ H (.modal a r) (.modal a m) := by
  obtain ⟨r,hr,hmr,hrm⟩ := representatives_complete hm hs
  have hg := (ComparisonRawHeadRestriction.carrier_modal_total hm).mp hc
  exact ⟨r,hr,ComparisonRawHeadRestriction.Derivation.mode_order hg ha hmr,
    ComparisonRawHeadRestriction.Derivation.mode_order hg ha hrm⟩


theorem truthForms_length (is : List Nat) : (truthForms is).length = 2 ^ (2 ^ is.length) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp [truthForms, List.length_flatMap, ih, ← Nat.pow_add, Nat.pow_succ, Nat.mul_two]

theorem channelAtoms_length (c : Channel) (names : List ModVar) :
    (channelAtoms c names).length = if c = .locality then names.length else 2 * names.length := by
  cases c <;> simp [channelAtoms, List.length_flatMap, Nat.mul_comm]

theorem representatives_length (names : List ModVar) :
    (representatives names).length = 2 ^ (2 ^ names.length + 2 * 2 ^ (2 * names.length)) := by
  simp [representatives, List.length_flatMap, truthForms_length, channelAtoms_length,
    ← Nat.pow_add, Nat.two_mul]


/-- Actual types in the finite action family of a finite list of heads. -/
def orbits (names : List ModVar) (heads : List CompareTy) : List CompareTy :=
  heads.flatMap fun a => (representatives names).map (CompareTy.modal a)

theorem orbits_complete {Δ H names heads a m} (hh : a ∈ heads)
    (hc : ComparisonRawHeadRestriction.Carrier Δ H (.modal a m))
    (ha : CompareTy.WellShaped Δ a) (hm : Entails Δ (.defined m))
    (hs : m.vars ⊆ names.toFinset) :
    ∃ b ∈ orbits names heads,
      ComparisonRawHeadRestriction.Derivation Δ H (.modal a m) b ∧
      ComparisonRawHeadRestriction.Derivation Δ H b (.modal a m) := by
  obtain ⟨r,hr,har,hra⟩ := head_orbit_complete hc ha hm hs
  exact ⟨.modal a r,List.mem_flatMap.mpr ⟨a,hh,List.mem_map.mpr ⟨r,hr,rfl⟩⟩,har,hra⟩

theorem orbits_length (names : List ModVar) (heads : List CompareTy) :
    (orbits names heads).length = heads.length *
      2 ^ (2 ^ names.length + 2 * 2 ^ (2 * names.length)) := by
  simp [orbits, List.length_flatMap, representatives_length]

end ModalityInference.ComparisonRawHeadModeOrbits
