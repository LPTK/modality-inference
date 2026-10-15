import ModalityInference.ComparisonCapsuleIntervals
import ModalityInference.Proofs.ComparisonBody

namespace ModalityInference.ComparisonCapsuleIntervals

theorem plan_spec {total : ModExpr → Bool} {name fresh : Nat} {requests : List Request}
    {b : Binding} (h : plan total name fresh requests = some b) :
    b.name = name ∧ b.fresh = fresh ∧
      b.requests = requests.filter (fun r => r.name == name) ∧ b.requests ≠ [] ∧
      ∀ r ∈ b.requests, r.base total = b.base := by
  unfold plan at h
  dsimp only at h
  split at h
  · contradiction
  · next r rs hg =>
    split at h
    · next hs =>
      cases Option.some.inj h
      simp only [List.all_eq_true, beq_iff_eq] at hs
      refine ⟨rfl, rfl, rfl, ?_, ?_⟩
      · simpa only [hg] using List.cons_ne_nil r rs
      · intro s hmem
        change s ∈ requests.filter (fun r => r.name == name) at hmem
        rw [hg] at hmem
        rcases List.mem_cons.mp hmem with he | he
        · subst s
          rfl
        · exact hs s he
    · contradiction

def Request.Holds (Δ : Bounds) (r : Request) (image : Ty) : Prop :=
  if r.isLower then Subtype Δ r.endpoint (.modal image r.action)
  else Subtype Δ (.modal image r.action) r.endpoint

/-- The stopped base may be partial. Only the emitted scalar inequality is
needed to relate the reconstructed image to the original endpoint. -/
theorem request_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {r : Request} {base : Ty} {suffix : ModExpr} (hbase : r.base total = base)
    (h : Entails Δ (r.bound total suffix)) :
    r.Holds Δ (.modal base suffix) := by
  have hp := ComparisonBody.peel_correct total htotal r.endpoint
  change Subtype Δ r.endpoint (.modal (r.base total) (r.suffix total)) ∧
    Subtype Δ (.modal (r.base total) (r.suffix total)) r.endpoint at hp
  rw [hbase] at hp
  cases he : r.isLower <;> simp only [Request.Holds, Request.bound, he, Bool.false_eq_true,
    ↓reduceIte, Entails] at h ⊢
  · exact Subtype.compose.trans ((Subtype.congr .refl h).trans hp.2)
  · exact hp.1.trans ((Subtype.congr .refl h).trans .composeRev)

theorem plan_correct {Δ : Bounds} (total : ModExpr → Bool)
    (htotal : ∀ m, total m = true → Submode Δ m m)
    {name fresh : Nat} {requests : List Request} {b : Binding}
    (h : plan total name fresh requests = some b)
    (hb : EntailsAll Δ (b.bounds total)) :
    ∀ r ∈ b.requests, r.Holds Δ b.image := by
  intro r hr
  exact request_correct total htotal ((plan_spec h).2.2.2.2 r hr)
    (hb _ (List.mem_map.mpr ⟨r, hr, rfl⟩))

end ModalityInference.ComparisonCapsuleIntervals
