import ModalityInference.Proofs.ComparisonRankedBasis
import ModalityInference.Proofs.ComparisonTypeModeClosure
import ModalityInference.Proofs.ComparisonStructuralEndpoints

/-! Instantiated public endpoints remain in a computable generator level once
the common image rank is fixed. Substitution retains the original finite name
support and does not introduce modality assumptions. -/
namespace ModalityInference.ComparisonRankedBasis

open ComparisonInterpolation ComparisonWitnessRestriction
open ComparisonControls ComparisonStructuralLattice ComparisonStructuralBasis

private theorem generated_rank {b : Basis} {n : Nat}
    (h : ∀ a ∈ b.heads, rank a ≤ n) (g : ComparisonControls.Generated b) :
    rank g.term ≤ n := by
  induction g <;> simp_all [ComparisonControls.Generated.term, rank]

private theorem types_rank_of_heads {b : Basis} {n : Nat}
    (h : ∀ a ∈ b.heads, rank a ≤ n) {a : CompareTy} (ha : a ∈ b.types) :
    rank a ≤ n :=
  Exists.elim (b.types_generated ha) (fun g hg => hg ▸ generated_rank h g)

theorem types_rank (names : List TypeVar) (modes : List ModVar) (n : Nat) :
    ∀ a ∈ (basis names modes n).types, rank a ≤ n := by
  induction n <;> intro a ha <;> apply types_rank_of_heads (b := _) ?_ ha
  · simp [basis, Basis.heads, rank]
  · simp_all only [basis, Basis.heads, pairs, List.forall_mem_cons,
      List.mem_append, or_imp, forall_and, List.forall_mem_flatMap,
      List.forall_mem_map, rank, Nat.add_le_add_iff_right, max_le_iff,
      Nat.zero_le, true_and, and_self, implies_true, and_true]
    rename_i n ih
    exact fun x hx => Nat.le_succ_of_le (ih x hx)

theorem lattice_rank {names : List TypeVar} {modes : List ModVar} {n : Nat}
    {a : CompareTy} (ha : LatticeForm (basis names modes n).types a) :
    rank a ≤ n := by
  induction ha with
  | atom h => exact types_rank names modes n _ h
  | join _ _ ih₁ ih₂ | meet _ _ ih₁ ih₂ => exact max_le ih₁ ih₂

theorem rank_subst_ofTy (types : TypeVar → CompareTy) (modes : ModVar → ModExpr)
    (a : Ty) (n : Nat) (h : ∀ v ∈ a.typeVars, rank (types v) ≤ n) :
    rank ((CompareTy.ofTy a).subst types modes) ≤ n + rank (.ofTy a) := by
  induction a <;> simp_all [CompareTy.ofTy,
    CompareTy.subst, rank, TypeExpr.typeVars, or_imp, forall_and]
  all_goals omega

theorem rank_ty (σ : CompareSubstitution) (a : Ty) (n : Nat)
    (h : ∀ v ∈ a.typeVars, rank (σ.type v) ≤ n) :
    rank (σ.ty a) ≤ n + rank (.ofTy a) :=
  rank_subst_ofTy σ.type σ.mode a n h

/-- One common ranked image family places each original endpoint in a level
computed from that rank and the written endpoint. Definedness is required under
the unchanged prepared assumptions. -/
theorem prepared_ty_normal {p : SchemePreparation.Prepared} {σ : CompareSubstitution}
    {n : Nat} (hn : ¬ ∃ ρ, ComparisonShape.Models p.assumptions ρ)
    (hs : Supported p σ)
    (hi : ∀ v ∈ inputTypes p,
      LatticeForm (basis (inputTypes p).toList (inputModes p).toList n).types (σ.type v))
    (a : Ty) (ht : a.typeVars ⊆ inputTypes p) (hm : a.modVars ⊆ inputModes p)
    (hd : (σ.ty a).DefinedUnder p.assumptions) :
    Normal p.assumptions (inputTypes p).toList (inputModes p).toList
      (n + rank (.ofTy a)) (σ.ty a) := by
  have hsupport : Supports (· ∈ inputTypes p) (· ∈ inputModes p) (σ.ty a) :=
    (ComparisonStructuralEndpoints.ofTy_supported a
      (fun _ hv => ht hv) (fun _ hv => hm hv)).subst
        (fun _ hv => hs.type hv) (fun _ hv => hs.mode hv)
  exact (normal_of_supported hn _ _ hd (hsupport.mono
    (fun _ hv => Finset.mem_toList.mpr hv) (fun _ hv => Finset.mem_toList.mpr hv))).mono
      (rank_ty σ a n (fun v hv => lattice_rank (hi v (ht hv))))

end ModalityInference.ComparisonRankedBasis
