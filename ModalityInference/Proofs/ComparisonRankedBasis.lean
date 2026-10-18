import ModalityInference.ComparisonRankedBasis
import ModalityInference.Proofs.ComparisonStructuralBasis
import ModalityInference.Proofs.ComparisonLatticeCompiler
import ModalityInference.Proofs.ComparisonInfeasibleShapes

namespace ModalityInference.ComparisonRankedBasis

open ComparisonAlgebra ComparisonControls ComparisonStructuralLattice ComparisonStructuralBasis

private theorem representable {Δ : Bounds}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) {a : CompareTy}
    (ha : a.DefinedUnder Δ) : Representable Δ .unit a :=
  ⟨a.wellShaped_of_no_models hn, ha, ComparisonShape.equivalent_of_no_models hn _ _⟩

theorem basis_modes (names : List TypeVar) (modes : List ModVar) (n : Nat) :
    (basis names modes n).modes = modes := by
  cases n <;> rfl

theorem head_mem_types {b : Basis} {a : CompareTy} (ha : a∈b.heads) : a∈b.types := by
  exact List.mem_map.mpr ⟨.head a, List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨a, ha, rfl⟩)), rfl⟩

private theorem types_of_heads {Δ : Bounds} {b : Basis}
    (hb : ∀a∈b.heads, Representable Δ .unit a) :
    ∀a∈b.types, Representable Δ .unit a := by
  obtain ⟨_, _, _, _, _, _, ht, _⟩ := b.carrier_interval CompareTy.var ModExpr.var
    (by simpa only [CompareTy.subst_id] using hb) (fun _ _ _ _ => rfl)
  simpa only [CompareTy.subst_id] using fun a ha => (ht a ha).1

theorem heads_representable {Δ : Bounds}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (names : List TypeVar) (modes : List ModVar)
    (n : Nat) : ∀a∈(basis names modes n).heads, Representable Δ .unit a := by
  have hunit : Representable Δ .unit .unit := representable hn (by
    intro η hη c hc; cases hc)
  induction n with
  | zero =>
    intro a ha
    simp only [basis, Basis.heads, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | rfl | ⟨v, _, rfl⟩
    · exact hunit
    · exact representable hn (by intro η hη c hc; cases hc)
    · exact representable hn (by intro η hη c hc; cases hc)
  | succ n ih =>
    have ht := types_of_heads ih
    have hp (k : Kind) : ∀a∈pairs k.op (basis names modes n).types
        (basis names modes n).types, Representable Δ .unit a := by
      intro a ha
      obtain ⟨x, hx, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      exact representable hn (k.op_representable (ht x hx) (ht y hy)).2.1
    intro a ha
    simp only [basis, Basis.heads, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ((ha | ha) | ha) | ha
    · exact hunit
    · exact ht a ha
    · exact hp .prod a ha
    · exact hp .sum a ha
    · exact hp .fn a ha

theorem types_representable {Δ : Bounds}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (names : List TypeVar) (modes : List ModVar)
    (n : Nat) : ∀a∈(basis names modes n).types, Representable Δ .unit a :=
  types_of_heads (heads_representable hn names modes n)

def Normal (Δ : Bounds) (names : List TypeVar) (modes : List ModVar)
    (n : Nat) (a : CompareTy) : Prop :=
  ∃t, LatticeForm (basis names modes n).types t ∧ Representable Δ .unit t ∧ Equiv Δ a t

theorem types_step {names : List TypeVar} {modes : List ModVar} {n : Nat}
    {a : CompareTy} (ha : a∈(basis names modes n).types) :
    a∈(basis names modes (n+1)).types := by
  apply head_mem_types
  simp only [basis, Basis.heads, List.mem_cons, List.mem_append]
  exact .inr (.inl (.inl (.inl ha)))

theorem types_mono {names : List TypeVar} {modes : List ModVar} {n k : Nat}
    (h : n≤k) {a : CompareTy} (ha : a∈(basis names modes n).types) :
    a∈(basis names modes k).types := by
  induction h with
  | refl => exact ha
  | step _ ih => exact types_step ih

theorem Normal.mono {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {n k : Nat} {a : CompareTy} (ha : Normal Δ names modes n a) (h : n≤k) :
    Normal Δ names modes k a := by
  obtain ⟨t, ht, htr, he⟩ := ha
  exact ⟨t, ht.mono (fun _ hx => types_mono h hx), htr, he⟩

theorem Normal.typeOp {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {n : Nat} {a b : CompareTy} (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (p : Bool)
    (ha : Normal Δ names modes n a) (hb : Normal Δ names modes n b) :
    Normal Δ names modes n (typeOp p a b) := by
  obtain ⟨x, hx, hxr, hxe⟩ := ha
  obtain ⟨y, hy, hyr, hye⟩ := hb
  exact ⟨ComparisonAlgebra.typeOp p x y, lattice_typeOp p hx hy, representable_typeOp p hxr hyr,
    Equiv.typeOp p hxe hye (ComparisonShape.equivalent_of_no_models hn _ _)⟩

theorem constructor_heads {names : List TypeVar} {modes : List ModVar} {n : Nat}
    (k : Kind) {a : CompareTy}
    (ha : a∈pairs k.op (basis names modes n).types (basis names modes n).types) :
    a∈(basis names modes (n+1)).heads := by
  simp only [basis, Basis.heads, List.mem_cons, List.mem_append]
  cases k
  · exact .inr (.inl (.inl (.inr ha)))
  · exact .inr (.inl (.inr ha))
  · exact .inr (.inr ha)

theorem Normal.constructor {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {n : Nat} {a b : CompareTy} (hn : ¬∃ρ, ComparisonShape.Models Δ ρ) (k : Kind)
    (ha : Normal Δ names modes n a) (hb : Normal Δ names modes n b) :
    Normal Δ names modes (n+1) (k.op a b) := by
  obtain ⟨x, hx, hxr, hxe⟩ := ha
  obtain ⟨y, hy, hyr, hye⟩ := hb
  obtain ⟨z, hz, hzr, hze⟩ := k.lattice hx hy
    (types_representable hn names modes n) (types_representable hn names modes n)
  exact ⟨z, hz.mono (fun _ h => head_mem_types (constructor_heads k h)),
    representable hn hzr.2.1, (k.congr hxe hye).trans hze⟩

theorem Normal.modal {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {n : Nat} {a : CompareTy} {m : ModExpr}
    (hn : ¬∃ρ, ComparisonShape.Models Δ ρ)
    (ha : Normal Δ names modes n a) (hm : DefinedMode Δ m)
    (hms : ∀v∈m.freeVariables, v∈modes) :
    Normal Δ names modes n (.modal a m) := by
  obtain ⟨x, hx, hxr, hxe⟩ := ha
  let b := basis names modes n
  obtain ⟨g, hg⟩ := hx.generated (fun _ => b.types_generated)
  let gm : ComparisonControls.Generated b := .modal g m (fun v hv => (basis_modes names modes n).symm ▸ hms v hv)
  have hgm : gm.term = .modal x m := by simp [gm, ComparisonControls.Generated.term, hg]
  have hgd : gm.term.DefinedUnder Δ := by
    rw [hgm]
    exact CompareTy.definedUnder_modal_iff.mpr ⟨hxr.2.1, hm⟩
  obtain ⟨t, ht, htr, hforward, hbackward⟩ :=
    gm.lattice_normal (heads_representable hn names modes n) hgd
  refine ⟨t, ht, htr, ?_⟩
  have hsm : Submode Δ m m := .refl hm
  rw [hgm] at hforward hbackward
  exact ⟨(AlgebraSubtype.congr hxe.1 hsm).trans hforward,
    hbackward.trans (.congr hxe.2 hsm)⟩

theorem normal_of_head {Δ : Bounds} {names : List TypeVar} {modes : List ModVar}
    {n : Nat} {a : CompareTy} (hn : ¬∃ρ, ComparisonShape.Models Δ ρ)
    (ha : a∈(basis names modes n).heads) : Normal Δ names modes n a := by
  have hr := heads_representable hn names modes n a ha
  exact ⟨a, .atom (head_mem_types ha), hr, .refl hr.1⟩

/-- Every defined finite input-supported type has a finite generator normal
form at its structural rank. Declared inequalities remain whole assumptions;
no recursive rigid name is unfolded or identified with a constructor. -/
theorem normal_of_supported {Δ : Bounds} (hn : ¬∃ρ, ComparisonShape.Models Δ ρ)
    (names : List TypeVar) (modes : List ModVar) {a : CompareTy}
    (hd : a.DefinedUnder Δ)
    (hs : ComparisonInterpolation.Supports (·∈names) (·∈modes) a) :
    Normal Δ names modes (rank a) a := by
  induction a with
  | var v =>
    apply normal_of_head hn
    simp only [rank, basis, Basis.heads, List.mem_cons, List.mem_map]
    exact .inr (.inr ⟨v, hs, rfl⟩)
  | unit => exact normal_of_head hn (List.mem_cons_self)
  | credit => exact normal_of_head hn (List.mem_cons_of_mem _ List.mem_cons_self)
  | prod a b iha ihb =>
    exact Normal.constructor hn .prod
      ((iha (CompareTy.definedUnder_prod_iff.mp hd).1 hs.1).mono (Nat.le_max_left _ _))
      ((ihb (CompareTy.definedUnder_prod_iff.mp hd).2 hs.2).mono (Nat.le_max_right _ _))
  | sum a b iha ihb =>
    exact Normal.constructor hn .sum
      ((iha (CompareTy.definedUnder_sum_iff.mp hd).1 hs.1).mono (Nat.le_max_left _ _))
      ((ihb (CompareTy.definedUnder_sum_iff.mp hd).2 hs.2).mono (Nat.le_max_right _ _))
  | fn a b iha ihb =>
    exact Normal.constructor hn .fn
      ((iha (CompareTy.definedUnder_fn_iff.mp hd).1 hs.1).mono (Nat.le_max_left _ _))
      ((ihb (CompareTy.definedUnder_fn_iff.mp hd).2 hs.2).mono (Nat.le_max_right _ _))
  | join a b iha ihb =>
    exact Normal.typeOp hn true
      ((iha (CompareTy.definedUnder_join_iff.mp hd).1 hs.1).mono (Nat.le_max_left _ _))
      ((ihb (CompareTy.definedUnder_join_iff.mp hd).2 hs.2).mono (Nat.le_max_right _ _))
  | meet a b iha ihb =>
    exact Normal.typeOp hn false
      ((iha (CompareTy.definedUnder_meet_iff.mp hd).1 hs.1).mono (Nat.le_max_left _ _))
      ((ihb (CompareTy.definedUnder_meet_iff.mp hd).2 hs.2).mono (Nat.le_max_right _ _))
  | modal a m ih =>
    exact Normal.modal hn (ih (CompareTy.definedUnder_modal_iff.mp hd).1 hs.1)
      (CompareTy.definedUnder_modal_iff.mp hd).2
      (fun v hv => hs.2 v ((m.mem_freeVariables v).mp hv))

/-- The normal form has the existing executable positive-CNF representation,
with a successful finite-type reconstruction and algebraic equivalence. -/
theorem polynomial_of_supported {Δ : Bounds} (hn : ¬∃ρ, ComparisonShape.Models Δ ρ)
    (names : List TypeVar) (modes : List ModVar) {a : CompareTy} {n : Nat}
    (hd : a.DefinedUnder Δ)
    (hs : ComparisonInterpolation.Supports (·∈names) (·∈modes) a)
    (hrank : rank a≤n) :
    ∃clauses t, Polynomial (basis names modes n) clauses ∧
      ComparisonPropagation.reify (basis names modes n).types clauses = some t ∧
      Representable Δ .unit t ∧ Equiv Δ a t := by
  obtain ⟨x, hx, _, he⟩ := (normal_of_supported hn names modes hd hs).mono hrank
  obtain ⟨clauses, hc⟩ := ComparisonLatticeCompiler.compile_complete hx
  obtain ⟨t, ht, htr, hte⟩ := ComparisonLatticeCompiler.compile_correct
    (types_representable hn names modes n) hc
  exact ⟨clauses, t, (ComparisonLatticeCompiler.compile_polynomial hc).2,
    ht, htr, he.trans hte.symm⟩

theorem heads_support (names : List TypeVar) (modes : List ModVar) (n : Nat) :
    ∀a∈(basis names modes n).heads,
      ComparisonInterpolation.Supports (·∈names) (·∈modes) a := by
  induction n with
  | zero =>
    intro a ha
    simp only [basis, Basis.heads, List.mem_cons, List.mem_map] at ha
    rcases ha with rfl | rfl | ⟨v, hv, rfl⟩
    · trivial
    · trivial
    · exact hv
  | succ n ih =>
    have ht : ∀a∈(basis names modes n).types,
        ComparisonInterpolation.Supports (·∈names) (·∈modes) a :=
      (basis names modes n).supports ih (fun _ hv => (basis_modes names modes n) ▸ hv)
    have hp (k : Kind) : ∀a∈pairs k.op (basis names modes n).types
        (basis names modes n).types,
        ComparisonInterpolation.Supports (·∈names) (·∈modes) a := by
      intro a ha
      obtain ⟨x, hx, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      cases k <;> exact ⟨ht x hx, ht y hy⟩
    intro a ha
    simp only [basis, Basis.heads, List.mem_cons, List.mem_append] at ha
    rcases ha with rfl | ((ha | ha) | ha) | ha
    · trivial
    · exact ht a ha
    · exact hp .prod a ha
    · exact hp .sum a ha
    · exact hp .fn a ha

theorem types_support (names : List TypeVar) (modes : List ModVar) (n : Nat) :
    ∀a∈(basis names modes n).types,
      ComparisonInterpolation.Supports (·∈names) (·∈modes) a :=
  (basis names modes n).supports (heads_support names modes n)
    (fun _ hv => (basis_modes names modes n) ▸ hv)

end ModalityInference.ComparisonRankedBasis
