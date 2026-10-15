import ModalityInference.Proofs.ComparisonPartialStructuredProvenance

namespace ModalityInference.ComparisonPartialStructuredCapsule

open ComparisonPartialCarrier

noncomputable section
attribute [local instance] Classical.propDecidable

def Public (a : CompareTy) : Prop := ∃ t : Ty, CompareTy.ofTy t = a

 theorem Public.modal_inv {a : CompareTy} {m : ModExpr} (h : Public (.modal a m)) : Public a := by
  obtain ⟨t, ht⟩ := h
  cases t <;> simp only [CompareTy.ofTy] at ht
  all_goals try contradiction
  case modal a' m' => exact ⟨a', (CompareTy.modal.inj ht).1⟩

 theorem Public.modal {a : CompareTy} (h : Public a) (m : ModExpr) : Public (.modal a m) := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨.modal t m, rfl⟩

 theorem Public.prod {a b : CompareTy} (ha : Public a) (hb : Public b) : Public (.prod a b) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  exact ⟨.prod s t, rfl⟩

 theorem Public.sum {a b : CompareTy} (ha : Public a) (hb : Public b) : Public (.sum a b) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  exact ⟨.sum s t, rfl⟩

/-- Root modal prefixes remain literal inside a frozen capsule. -/
inductive ModalPrefix (base : CompareTy) : CompareTy → Prop
  | refl : ModalPrefix base base
  | modal {a m} : ModalPrefix base a → ModalPrefix base (.modal a m)

 theorem ModalPrefix.trans {a b c : CompareTy} (h : ModalPrefix a b) (g : ModalPrefix b c) :
    ModalPrefix a c := by
  induction g with
  | refl => exact h
  | modal _ ih => exact .modal ih

 theorem ModalPrefix.public_base {a b : CompareTy} (h : ModalPrefix a b) (hb : Public b) : Public a := by
  induction h with
  | refl => exact hb
  | modal h ih => exact ih hb.modal_inv

 theorem token_prefix_of_frozen {Δ : Bounds} (a : CompareTy) (m : ModExpr)
    (h : ComparisonPartialCapsule.observe Δ (.modal a m) = {(a, m)}) :
    ∃ token, token ∈ ComparisonPartialCapsule.observe Δ (.modal a m) ∧ ModalPrefix a token.1 :=
  ⟨(a, m), by rw [h]; exact rfl, .refl⟩

 theorem partial_token_prefix {Δ : Bounds} {m : ModExpr}
    (hm : ¬Entails Δ (.defined m)) (a : CompareTy) :
    ∃ token, token ∈ ComparisonPartialCapsule.observe Δ (.modal a m) ∧ ModalPrefix a token.1 := by
  induction m generalizing a with
  | compose m n ihm ihn =>
    rw [ComparisonPartialCapsule.observe_compose]
    by_cases hn : Entails Δ (.defined n)
    · rw [ComparisonPartialCapsule.observe_modal_total hn]
      exact ihm (fun h => hm (Entails.defined_compose_iff.mpr ⟨h, hn⟩)) a
    · obtain ⟨token, ht, hp⟩ := ihn hn (.modal a m)
      exact ⟨token, ht, (ModalPrefix.modal (m := m) .refl).trans hp⟩
  | _ =>
    apply token_prefix_of_frozen
    rw [ComparisonPartialCapsule.observe]
    all_goals simp [ComparisonPartialCapsule.not_epsilon_of_partial hm, hm]

 theorem literal_partial_public {Δ : Bounds} {suffix : Suffix} {a : CompareTy}
    (hn : ¬suffix.total Δ)
    (hc : ∀ token ∈ (literal Δ a suffix).positive, Public token.2.1) : Public a := by
  cases suffix with
  | none => exact (hn trivial).elim
  | some m =>
    obtain ⟨token, ht, hp⟩ := partial_token_prefix hn a
    exact hp.public_base (hc ([], token) (⟨token, ht, rfl⟩))

def side (positive : Bool) (a : Observation) : Set Token :=
  if positive then a.positive else a.negative

/-- A partial inherited action exposes every internal lattice constructor as a
literal token. Public token operands therefore force the entire base to be
public, including through products, sums, and nested modal syntax. -/
 theorem public_of_partial_observation {Δ : Bounds} (a : CompareTy) (suffix : Suffix)
    (positive : Bool) (hn : ¬suffix.total Δ)
    (hc : ∀ token ∈ side positive (observe Δ a suffix), Public token.2.1) : Public a := by
  induction a generalizing suffix positive with
  | var v => exact ⟨.var v, rfl⟩
  | unit => exact ⟨.unit, rfl⟩
  | credit => exact ⟨.credit, rfl⟩
  | modal a m ih =>
    have hp : ¬(suffix.prepend m).total Δ := fun h => hn ((Suffix.total_prepend Δ suffix m).mp h).2
    exact (ih (suffix.prepend m) positive hp hc).modal m
  | prod a b ia ib =>
    have ha := ia suffix positive hn (fun token ht => by
      apply hc (false :: token.1, token.2)
      cases positive <;> exact Or.inl (⟨token, ht, rfl⟩))
    have hb := ib suffix positive hn (fun token ht => by
      apply hc (true :: token.1, token.2)
      cases positive <;> exact Or.inr (⟨token, ht, rfl⟩))
    exact ha.prod hb
  | sum a b ia ib =>
    have ha := ia suffix positive hn (fun token ht => by
      apply hc (false :: token.1, token.2)
      cases positive <;> exact Or.inl (⟨token, ht, rfl⟩))
    have hb := ib suffix positive hn (fun token ht => by
      apply hc (true :: token.1, token.2)
      cases positive <;> exact Or.inr (⟨token, ht, rfl⟩))
    exact ha.sum hb
  | fn a b ia ib | join a b ia ib | meet a b ia ib =>
    apply literal_partial_public hn
    intro token ht
    apply hc token
    simp only [observe, if_neg hn]
    cases positive <;> exact ht

/-- A bare comparison with a public endpoint cannot hide internal joins or
meets beneath a genuinely partial outer action. No carrier or total-image
premise is required of the internal base. -/
 theorem partial_context_public_below {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a : CompareTy} {b : Ty} {m : ModExpr} (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal a m) (.ofTy b)) : Public a := by
  apply public_of_partial_observation a (some m) true hm
  intro token ht
  have hb := (algebra_sound hΔ h).1 ht
  exact candidates_public b none ((observe_supported Δ (.ofTy b) none).1 token hb)

 theorem partial_context_public_above {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a : Ty} {b : CompareTy} {m : ModExpr} (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.ofTy a) (.modal b m)) : Public b := by
  apply public_of_partial_observation b (some m) false hm
  intro token ht
  have ha := (algebra_sound hΔ h).2 ht
  exact candidates_public a none ((observe_supported Δ (.ofTy a) none).2 token ha)

end
end ModalityInference.ComparisonPartialStructuredCapsule
