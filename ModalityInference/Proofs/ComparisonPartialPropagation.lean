import ModalityInference.ComparisonPartialPropagation
import ModalityInference.Proofs.ComparisonReductionAlgebra
import ModalityInference.Proofs.ComparisonShapeSolver

/-! Checked derivations for propagation over partial comparison envelopes. -/
namespace ModalityInference.ComparisonPartialPropagation

deriving instance ReflBEq for CompareTy
deriving instance LawfulBEq for CompareTy

theorem wellShaped_sound {Δ : Bounds} {shapes : TypeVar → ComparisonShape}
    (hshapes : ∀ a b, a.subst shapes = b.subst shapes → ComparisonShape.Equivalent Δ a b)
    {t : CompareTy} (h : wellShaped shapes t = true) : t.WellShaped Δ := by
  induction t with
  | var | unit | credit => trivial
  | modal a m ih => exact ih h
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
    simp only [wellShaped, Bool.and_eq_true] at h
    exact ⟨iha h.1, ihb h.2⟩
  | join a b iha ihb | meet a b iha ihb =>
    simp only [wellShaped, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    exact ⟨iha h.1, ihb h.2.1, hshapes _ _ h.2.2⟩

theorem wellShaped_prepared {fuel : Nat} {p : SchemePreparation.Prepared}
    {s : ComparisonShapeSolver.Solved}
    (hs : ComparisonShapeSolver.prepare fuel p = .success (.solved s))
    {t : CompareTy} (h : wellShaped s.fixedShapes t = true) :
    t.WellShaped p.assumptions :=
  wellShaped_sound (fun a b => (ComparisonShapeSolver.prepare_fixed_equivalent hs a b).mpr) h

theorem Certificate.check_sound {Δ : Bounds} {shape : CompareTy → Bool}
    {mode : ModExpr → ModExpr → Bool}
    (hshape : ∀ t, shape t = true → t.WellShaped Δ)
    (hmode : ∀ m n, mode m n = true → Submode Δ m n)
    {c : Certificate} (h : c.check shape mode Δ = true) :
    AlgebraSubtype Δ c.left c.right := by
  induction c with
  | refl a => exact .refl (hshape a h)
  | bound a b => exact .shaped (.bound (by simpa [Certificate.check] using h))
  | trans ab bc ihab ihbc =>
    simp only [Certificate.check, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    have hab := ihab h.1
    rw [h.2.2] at hab
    exact hab.trans (ihbc h.2.1)
  | congr ab m n ih =>
    simp only [Certificate.check, Bool.and_eq_true] at h
    exact .congr (ih h.1) (hmode m n h.2)
  | identity a reverse =>
    cases reverse
    · exact .identity (hshape a h)
    · exact .identityRev (hshape a h)
  | compose a m n reverse =>
    cases reverse
    · exact .compose (hshape a h)
    · exact .composeRev (hshape a h)
  | meetLeft a b => exact .shaped (.meetLeft (hshape (.meet a b) h))
  | meetRight a b => exact .shaped (.meetRight (hshape (.meet a b) h))
  | prod a b c d m n ac bd ihac ihbd =>
    simp only [Certificate.check, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨ha, hb, hm, hal, har, hbl, hbr⟩ := h
    exact AlgebraSubtype.prod_cross
      (by simpa only [hal, har] using ihac ha)
      (by simpa only [hbl, hbr] using ihbd hb) (hmode m n hm)
  | sum a b c d m n ac bd ihac ihbd =>
    simp only [Certificate.check, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨ha, hb, hm, hal, har, hbl, hbr⟩ := h
    exact AlgebraSubtype.sum_cross
      (by simpa only [hal, har] using ihac ha)
      (by simpa only [hbl, hbr] using ihbd hb) (hmode m n hm)
  | fn a b c d m n ca bd ihca ihbd =>
    simp only [Certificate.check, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨ha, hb, hm, hal, har, hbl, hbr⟩ := h
    exact AlgebraSubtype.fn
      (by simpa only [hal, har] using ihca ha)
      (by simpa only [hbl, hbr] using ihbd hb) (hmode m (.compose n .top) hm)

structure AttemptSpec (fuel : Nat) (p : SchemePreparation.Prepared) (r : Result) : Prop where
  sourceBounds : p.sourceBounds = []
  modeRange : p.firstMode = p.nextMode
  positive : ComparisonPartialPropagation.positive
    (fun n => p.firstType ≤ n && n < p.nextType) true p.sourceType = true
  shapes : ComparisonShapeSolver.prepare fuel p = .success (.solved r.shapes)
  action_eq : r.action = ComparisonPartialPropagation.action p r.shapes
  imageShapes : ∀ entry ∈ r.action.types, wellShaped r.shapes.fixedShapes entry.2 = true
  certificate : r.certificate.check (wellShaped r.shapes.fixedShapes)
    (fun a b => r.scalarEdges.contains (a, b)) p.assumptions = true
  left : r.certificate.left = r.action.ty p.sourceType
  right : r.certificate.right = .ofTy p.targetType
  query : r.query = .imp (boundsModeFormula p.assumptions)
    (boundsModeFormula (r.scalarEdges.map fun (a, b) => Constraint.mode a b))
  backend : ConcreteBackend.decideFormula fuel r.query = .success r.backend
  valid : r.backend.valid = true

theorem attempt_spec {fuel : Nat} {p : SchemePreparation.Prepared} {r : Result}
    (h : attempt fuel p = .success (some r)) : AttemptSpec fuel p r := by
  simp only [attempt, bind, pure, RunResult.bind] at h
  split at h
  · cases h
  · next hgate =>
    simp at hgate
    split at h
    · cases h
    · next hpositive =>
      simp at hpositive
      cases hs : ComparisonShapeSolver.prepare fuel p with
      | exhausted | rejected reason => simp [hs] at h
      | success solved =>
        cases solved with
        | infeasibleAssumptions => simp [hs] at h
        | solved shapes =>
          simp only [hs] at h
          split at h
          · cases h
          · next himages =>
            simp at himages
            cases he : modeEdges fuel p.assumptions (modeLabels (nodes p (action p shapes))) with
            | exhausted | rejected reason => simp [he] at h
            | success edges =>
              simp only [he] at h
              cases hc : saturate (fun a b => edges.contains (a, b))
                  ((action p shapes).ty p.sourceType) (.ofTy p.targetType) fuel
                  (initialGraph p.assumptions (nodes p (action p shapes))) with
              | exhausted | rejected reason => rw [hc] at h; cases h
              | success candidate =>
                cases candidate with
                | none => rw [hc] at h; cases h
                | some certificate =>
                  simp only [hc] at h
                  split at h
                  · cases h
                  · next hcertificate =>
                    simp only [Bool.not_eq_true, Bool.not_eq, Bool.not_eq_false, Bool.and_eq_true,
                      beq_iff_eq, and_assoc] at hcertificate
                    cases hr : ConcreteBackend.decideFormula fuel
                        (.imp (boundsModeFormula p.assumptions)
                          (boundsModeFormula (edges.map fun (a, b) => Constraint.mode a b))) with
                    | exhausted | rejected reason => rw [hr] at h; cases h
                    | success backend =>
                      simp only [hr] at h
                      split at h
                      · cases h
                      · next hvalid =>
                        cases h
                        exact
                          { sourceBounds := hgate.1
                            modeRange := hgate.2
                            positive := hpositive
                            shapes := hs
                            action_eq := rfl
                            imageShapes := fun entry hm => himages entry.1 entry.2 hm
                            certificate := hcertificate.2.2
                            left := hcertificate.1
                            right := hcertificate.2.1
                            query := rfl
                            backend := hr
                            valid := by
                              simpa only [Bool.not_eq_true, Bool.not_eq, Bool.not_eq_false] using hvalid }

theorem attempt_query_valid {fuel : Nat} {p : SchemePreparation.Prepared} {r : Result}
    (h : attempt fuel p = .success (some r)) : ∀ σ, r.query.eval σ = true :=
  (ConcreteBackend.decideFormula_correct (attempt_spec h).backend).mp (attempt_spec h).valid

theorem attempt_mode_models {fuel : Nat} {p : SchemePreparation.Prepared} {r : Result}
    (h : attempt fuel p = .success (some r)) :
    ∀ η, ModeModels p.assumptions η →
      ModeModels (r.scalarEdges.map fun (a, b) => Constraint.mode a b) η := by
  have hs := attempt_spec h
  have hb : ConcreteBackend.entails fuel p.assumptions
      (r.scalarEdges.map fun (a, b) => Constraint.mode a b) = .success r.backend := by
    change ConcreteBackend.decideFormula fuel _ = .success r.backend
    simpa only [hs.query] using hs.backend
  exact (ConcreteBackend.entails_correct hb).mp hs.valid

theorem attempt_scalar_edge {fuel : Nat} {p : SchemePreparation.Prepared} {r : Result}
    (h : attempt fuel p = .success (some r)) {a b : ModExpr}
    (he : (a, b) ∈ r.scalarEdges) : Submode p.assumptions a b :=
  .valid fun η hη => attempt_mode_models h η hη (.mode a b)
    (List.mem_map.mpr ⟨(a, b), he, rfl⟩)

theorem attempt_sound {fuel : Nat} {p : SchemePreparation.Prepared} {r : Result}
    (h : attempt fuel p = .success (some r)) :
    r.action.WellShaped p.assumptions ∧
      AlgebraEntailsAll p.assumptions (r.action.bounds p.sourceBounds) ∧
      AlgebraSubtype p.assumptions (r.action.ty p.sourceType) (.ofTy p.targetType) := by
  have hs := attempt_spec h
  refine ⟨fun entry he => wellShaped_prepared hs.shapes (hs.imageShapes entry he), ?_, ?_⟩
  · simp [AlgebraEntailsAll, CompareSubstitution.bounds, hs.sourceBounds]
  · have hc := Certificate.check_sound
      (fun t ht => wellShaped_prepared hs.shapes ht)
      (fun a b hab => attempt_scalar_edge h (a := a) (b := b) (by simpa using hab))
      hs.certificate
    simpa only [hs.left, hs.right] using hc

end ModalityInference.ComparisonPartialPropagation
