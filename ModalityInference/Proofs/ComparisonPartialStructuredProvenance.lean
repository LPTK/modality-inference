import ModalityInference.Proofs.ComparisonPartialStructuredCapsule
import ModalityInference.Proofs.ComparisonPartialCapsuleProvenance

namespace ModalityInference.ComparisonPartialStructuredCapsule

noncomputable section
attribute [local instance] Classical.propDecidable

def atPathList (side : Bool) (tokens : List Token) : List Token :=
  tokens.map fun t => (side :: t.1, t.2)

def literalCandidates (a : CompareTy) (suffix : Suffix) : List Token :=
  (ComparisonPartialCapsule.candidates (suffix.apply a)).map fun token => ([], token)

/-- A finite syntactic capsule basis; modal suffixes inherited from product and
sum ancestors remain part of each listed fragment. -/
def candidates : CompareTy → Suffix → List Token
  | .modal a m, suffix => candidates a (suffix.prepend m)
  | .prod a b, suffix | .sum a b, suffix =>
      atPathList false (candidates a suffix) ++ atPathList true (candidates b suffix)
  | .fn a b, suffix => literalCandidates (.fn a b) suffix ++
      atPathList false (candidates a none) ++ atPathList true (candidates b none)
  | .join a b, suffix => literalCandidates (.join a b) suffix ++ candidates a none ++ candidates b none
  | .meet a b, suffix => literalCandidates (.meet a b) suffix ++ candidates a none ++ candidates b none
  | a, suffix => literalCandidates a suffix

def Observation.Supported (a : Observation) (tokens : List Token) : Prop :=
  (∀ t ∈ a.positive, t ∈ tokens) ∧ (∀ t ∈ a.negative, t ∈ tokens)

 theorem Observation.Supported.mono {a : Observation} {xs ys : List Token}
    (h : a.Supported xs) (hxy : ∀ t ∈ xs, t ∈ ys) : a.Supported ys :=
  ⟨fun t ht => hxy t (h.1 t ht), fun t ht => hxy t (h.2 t ht)⟩

 theorem Observation.Supported.flip {a : Observation} {xs : List Token}
    (h : a.Supported xs) : a.flip.Supported xs := ⟨h.2, h.1⟩

 theorem Observation.Supported.fork {a b : Observation} {xs ys : List Token}
    (h : a.Supported xs) (g : b.Supported ys) :
    (a.fork b).Supported (atPathList false xs ++ atPathList true ys) := by
  constructor
  all_goals intro t ht
  · rcases ht with ht | ht
    · obtain ⟨u, hu, rfl⟩ := ht
      exact List.mem_append_left _ (List.mem_map.mpr ⟨u, h.1 u hu, rfl⟩)
    · obtain ⟨u, hu, rfl⟩ := ht
      exact List.mem_append_right _ (List.mem_map.mpr ⟨u, g.1 u hu, rfl⟩)
  · rcases ht with ht | ht
    · obtain ⟨u, hu, rfl⟩ := ht
      exact List.mem_append_left _ (List.mem_map.mpr ⟨u, h.2 u hu, rfl⟩)
    · obtain ⟨u, hu, rfl⟩ := ht
      exact List.mem_append_right _ (List.mem_map.mpr ⟨u, g.2 u hu, rfl⟩)

 theorem Observation.Supported.join {a b : Observation} {xs ys : List Token}
    (h : a.Supported xs) (g : b.Supported ys) : (a.join b).Supported (xs ++ ys) :=
  ⟨fun t ht => ht.elim (fun ht => List.mem_append_left _ (h.1 t ht))
    (fun ht => List.mem_append_right _ (g.1 t ht)),
   fun t ht => List.mem_append_left _ (h.2 t ht.1)⟩

 theorem Observation.Supported.meet {a b : Observation} {xs ys : List Token}
    (h : a.Supported xs) (g : b.Supported ys) : (a.meet b).Supported (xs ++ ys) :=
  ⟨fun t ht => List.mem_append_left _ (h.1 t ht.1),
   fun t ht => ht.elim (fun ht => List.mem_append_left _ (h.2 t ht))
    (fun ht => List.mem_append_right _ (g.2 t ht))⟩

 theorem literal_supported (Δ : Bounds) (a : CompareTy) (suffix : Suffix) :
    (literal Δ a suffix).Supported (literalCandidates a suffix) := by
  constructor
  all_goals intro t ht
  all_goals obtain ⟨token, ht, rfl⟩ := ht
  all_goals exact List.mem_map.mpr ⟨token,
    ComparisonPartialCapsule.observe_mem_candidates (suffix.apply a) ht, rfl⟩

 theorem observe_supported (Δ : Bounds) (a : CompareTy) (suffix : Suffix) :
    (observe Δ a suffix).Supported (candidates a suffix) := by
  induction a generalizing suffix with
  | var | unit | credit => exact literal_supported _ _ _
  | modal a m ih => exact ih (suffix.prepend m)
  | prod a b ia ib | sum a b ia ib => exact (ia suffix).fork (ib suffix)
  | fn a b ia ib =>
    simp only [observe]
    split
    · exact ((ia none).flip.fork (ib none)).mono fun t ht => by
        simpa only [candidates, List.append_assoc] using List.mem_append_right
          (literalCandidates (.fn a b) suffix) ht
    · exact (literal_supported Δ (.fn a b) suffix).mono fun t ht => by
        exact List.mem_append_left _ (List.mem_append_left _ ht)
  | join a b ia ib =>
    simp only [observe]
    split
    · exact ((ia none).join (ib none)).mono fun t ht => by
        simpa only [candidates, List.append_assoc] using List.mem_append_right
          (literalCandidates (.join a b) suffix) ht
    · exact (literal_supported Δ (.join a b) suffix).mono fun t ht => by
        exact List.mem_append_left _ (List.mem_append_left _ ht)
  | meet a b ia ib =>
    simp only [observe]
    split
    · exact ((ia none).meet (ib none)).mono fun t ht => by
        simpa only [candidates, List.append_assoc] using List.mem_append_right
          (literalCandidates (.meet a b) suffix) ht
    · exact (literal_supported Δ (.meet a b) suffix).mono fun t ht => by
        exact List.mem_append_left _ (List.mem_append_left _ ht)

 theorem literalCandidates_public (a : Ty) (suffix : Suffix) {t : Token}
    (h : t ∈ literalCandidates (.ofTy a) suffix) : ∃ b : Ty, CompareTy.ofTy b = t.2.1 := by
  obtain ⟨token, ht, rfl⟩ := List.mem_map.mp h
  cases suffix with
  | none => exact ComparisonPartialCapsule.candidates_ofTy_public a ht
  | some m => exact ComparisonPartialCapsule.candidates_ofTy_public (.modal a m) ht

 theorem candidates_public (a : Ty) (suffix : Suffix) {t : Token}
    (h : t ∈ candidates (.ofTy a) suffix) : ∃ b : Ty, CompareTy.ofTy b = t.2.1 := by
  induction a generalizing suffix t with
  | var v => exact literalCandidates_public (.var v) suffix h
  | unit => exact literalCandidates_public .unit suffix h
  | credit => exact literalCandidates_public .credit suffix h
  | modal a m ih => exact ih (suffix.prepend m) h
  | prod a b ia ib | sum a b ia ib =>
    rcases List.mem_append.mp h with h | h
    · obtain ⟨token, ht, rfl⟩ := List.mem_map.mp h
      exact ia suffix (t := token) ht
    · obtain ⟨token, ht, rfl⟩ := List.mem_map.mp h
      exact ib suffix (t := token) ht
  | fn a b ia ib =>
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · exact literalCandidates_public (.fn a b) suffix h
      · obtain ⟨token, ht, rfl⟩ := List.mem_map.mp h
        exact ia none (t := token) ht
    · obtain ⟨token, ht, rfl⟩ := List.mem_map.mp h
      exact ib none (t := token) ht

/-- A carrier compared with a public endpoint uses only that endpoint's finite
path-indexed capsule basis. Each frozen operand in this basis is public. -/
 theorem carrier_public_provenance {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a : CompareTy} {b : Ty} (ha : ComparisonPartialCarrier.Carrier Δ a)
    (h : AlgebraSubtype Δ a (.ofTy b)) {token : Token}
    (ht : token ∈ (observe Δ a none).positive) :
    token ∈ candidates (.ofTy b) none ∧ ∃ c : Ty, CompareTy.ofTy c = token.2.1 := by
  rw [carrier_observation_eq hΔ ha (ComparisonPartialCarrier.Carrier.of_public b) h] at ht
  have hc := (observe_supported Δ (.ofTy b) none).1 token ht
  exact ⟨hc, candidates_public b none hc⟩

 theorem public_carrier_provenance {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    {a : Ty} {b : CompareTy} (hb : ComparisonPartialCarrier.Carrier Δ b)
    (h : AlgebraSubtype Δ (.ofTy a) b) {token : Token}
    (ht : token ∈ (observe Δ b none).positive) :
    token ∈ candidates (.ofTy a) none ∧ ∃ c : Ty, CompareTy.ofTy c = token.2.1 := by
  rw [← carrier_observation_eq hΔ (ComparisonPartialCarrier.Carrier.of_public a) hb h] at ht
  have hc := (observe_supported Δ (.ofTy a) none).1 token ht
  exact ⟨hc, candidates_public a none hc⟩

end
end ModalityInference.ComparisonPartialStructuredCapsule
