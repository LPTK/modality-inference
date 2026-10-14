import ModalityInference.Proofs.Backend

/-! Fuel stability and eventual completion of Boolean normalization. -/
namespace ModalityInference

theorem cnfOr_monotone {n a b cs} (h : cnfOr n a b = .success cs) :
    ∀ fuel ≥ n, cnfOr fuel a b = .success cs := by
  intro fuel hf
  simp only [cnfOr] at h ⊢
  split at h
  · contradiction
  · split
    · omega
    · exact h

theorem toCNF_monotone {n positive e cs} (h : toCNF n positive e = .success cs) :
    ∀ fuel ≥ n, toCNF fuel positive e = .success cs := by
  induction n generalizing positive e cs
  case zero => cases h
  case succ n ih =>
    rintro (_ | fuel) hFuel
    · omega
    have step (p e cs) (hs : toCNF n p e = .success cs) :
        toCNF fuel p e = .success cs := ih hs fuel (Nat.le_of_succ_le_succ hFuel)
    cases e
    all_goals simp only [toCNF, bind, pure, RunResult.bind] at h ⊢
    all_goals repeat' (split at h <;> try contradiction)
    all_goals simp_all
    all_goals exact cnfOr_monotone h _ (by omega)

/-- Normalization eventually returns the same clauses for every larger budget,
including the intermediate Cartesian-product size check. -/
theorem toCNF_complete (e : BoolExpr) (positive : Bool) :
    ∃ n cs, ∀ fuel ≥ n, toCNF fuel positive e = .success cs := by
  induction e generalizing positive with
  | const b => exact ⟨1, if b == positive then [] else [[]],
      fun fuel hf => by cases fuel <;> simp_all [toCNF]⟩
  | atom v => exact ⟨1, [[(v,positive)]],
      fun fuel hf => by cases fuel <;> simp_all [toCNF]⟩
  | and a b ia ib =>
    obtain ⟨na, ca, ha⟩ := ia positive
    obtain ⟨nb, cb, hb⟩ := ib positive
    refine ⟨na + nb + ca.length * cb.length + 1,
      if positive then cleanCNF (ca ++ cb)
        else cleanCNF (ca.flatMap fun x => cb.map (x ++ ·)), ?_⟩
    rintro (_ | fuel) hf
    · omega
    · cases positive <;> simp [toCNF, ha fuel (by omega), hb fuel (by omega),
        bind, pure, RunResult.bind, cnfOr, show ¬ca.length * cb.length > fuel + 1 by omega]
  | or a b ia ib =>
    obtain ⟨na, ca, ha⟩ := ia positive
    obtain ⟨nb, cb, hb⟩ := ib positive
    refine ⟨na + nb + ca.length * cb.length + 1,
      if positive then cleanCNF (ca.flatMap fun x => cb.map (x ++ ·))
        else cleanCNF (ca ++ cb), ?_⟩
    rintro (_ | fuel) hf
    · omega
    · cases positive <;> simp [toCNF, ha fuel (by omega), hb fuel (by omega),
        bind, pure, RunResult.bind, cnfOr, show ¬ca.length * cb.length > fuel + 1 by omega]
  | imp a b ia ib =>
    obtain ⟨na, ca, ha⟩ := ia (!positive)
    obtain ⟨nb, cb, hb⟩ := ib positive
    refine ⟨na + nb + ca.length * cb.length + 1,
      if positive then cleanCNF (ca.flatMap fun x => cb.map (x ++ ·))
        else cleanCNF (ca ++ cb), ?_⟩
    rintro (_ | fuel) hf
    · omega
    · cases positive <;> simp only [Bool.not_true, Bool.not_false] at ha <;>
        simp [toCNF, ha fuel (by omega), hb fuel (by omega),
        bind, pure, RunResult.bind, cnfOr, show ¬ca.length * cb.length > fuel + 1 by omega]

end ModalityInference
