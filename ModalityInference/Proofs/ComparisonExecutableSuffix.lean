import ModalityInference.Proofs.ComparisonRawCarrierSuffix

/-! Executable suffix normalization uses completed Boolean definedness tests.
The exact syntax below a partial suffix is retained. -/
namespace ModalityInference.ComparisonExecutableSuffix

open ComparisonRawCarrierSuffix

def normalize (total : ModExpr → Bool) (m : ModExpr) : Normalized :=
  if total m then ⟨none,m⟩ else
    match m with
    | .compose l r =>
        match (normalize total r).literal with
        | some p => ⟨some (.compose l p),(normalize total r).control⟩
        | none => ⟨(normalize total l).literal,
            .compose (normalize total l).control (normalize total r).control⟩
    | m => ⟨some m,.epsilon⟩

/-- Only composition children can cause further definedness tests. Residual
labels are tested as complete expressions. -/
def tests : ModExpr → List ModExpr
  | .compose l r => .compose l r :: tests l ++ tests r
  | m => [m]

theorem self_mem_tests (m : ModExpr) : m ∈ tests m := by
  cases m <;> exact List.mem_cons_self

def CorrectOn (Δ : Bounds) (total : ModExpr → Bool) (labels : List ModExpr) : Prop :=
  ∀ m ∈ labels, total m = true ↔ Entails Δ (.defined m)

theorem normalize_eq {Δ : Bounds} {total : ModExpr → Bool} {m : ModExpr}
    (h : CorrectOn Δ total (tests m)) : normalize total m = ComparisonRawCarrierSuffix.normalize Δ m := by
  induction m with
  | compose l r ihl ihr =>
    have hl : CorrectOn Δ total (tests l) := fun a ha =>
      h a (List.mem_cons_of_mem _ (List.mem_append_left _ ha))
    have hr : CorrectOn Δ total (tests r) := fun a ha =>
      h a (List.mem_cons_of_mem _ (List.mem_append_right _ ha))
    simp only [normalize,ComparisonRawCarrierSuffix.normalize,
      ← h _ (self_mem_tests _),ihl hl,ihr hr]
    split_ifs <;> rfl
  | _ =>
    simp only [normalize,ComparisonRawCarrierSuffix.normalize,← h _ (self_mem_tests _)]

theorem control_total {Δ : Bounds} {total : ModExpr → Bool} {m : ModExpr}
    (h : CorrectOn Δ total (tests m)) : Entails Δ (.defined (normalize total m).control) := by
  rw [normalize_eq h]
  exact ComparisonRawCarrierSuffix.control_total Δ m

theorem literal_none_iff {Δ : Bounds} {total : ModExpr → Bool} {m : ModExpr}
    (h : CorrectOn Δ total (tests m)) :
    (normalize total m).literal = none ↔ Entails Δ (.defined m) := by
  rw [normalize_eq h]
  exact ComparisonRawCarrierSuffix.literal_none_iff Δ m

end ModalityInference.ComparisonExecutableSuffix
