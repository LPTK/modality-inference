import ModalityInference.Proofs.ComparisonPartialFrozenFragments

namespace ModalityInference.ComparisonPartialStructuredCapsule

/-- Literal type subtrees, including the root. -/
def subtrees (a : CompareTy) : List CompareTy :=
  a :: match a with
  | .prod b c | .sum b c | .fn b c | .join b c | .meet b c => subtrees b ++ subtrees c
  | .modal b _ => subtrees b
  | _ => []

 theorem image_mem_subtrees (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {v : TypeVar} (hv : v ∈ body.typeVars) :
    ts v ∈ subtrees ((CompareTy.ofTy body).subst ts ms) := by
  induction body with
  | var w =>
    have he : v = w := Finset.mem_singleton.mp hv
    subst v
    change ts w ∈ subtrees (ts w)
    cases ts w <;> exact List.mem_cons_self
  | unit | credit => exact (Finset.notMem_empty v hv).elim
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    apply List.mem_cons_of_mem
    exact (Finset.mem_union.mp hv).elim
      (fun h => List.mem_append_left _ (ia h))
      (fun h => List.mem_append_right _ (ib h))
  | modal a m ia => exact List.mem_cons_of_mem _ (ia hv)

 theorem subtrees_public {a : CompareTy} (ha : Public a) {b : CompareTy}
    (h : b ∈ subtrees a) : Public b := by
  obtain ⟨t, rfl⟩ := ha
  induction t with
  | var v | unit | credit => exact ⟨_, (List.mem_singleton.mp h).symm⟩
  | prod a b ia ib | sum a b ia ib | fn a b ia ib =>
    rcases List.mem_cons.mp h with h | h
    · exact ⟨_, h.symm⟩
    · exact (List.mem_append.mp h).elim ia ib
  | modal a m ia =>
    rcases List.mem_cons.mp h with h | h
    · exact ⟨_, h.symm⟩
    · exact ia h

/-- Exact images in a frozen source context are chosen from literal subtrees of
its endpoint's finite frozen fragments. The list is independent of a witness. -/
def frozenImageCandidates (endpoint : Ty) : List CompareTy :=
  (frozenFragments (.ofTy endpoint) none).flatMap subtrees

 theorem frozenImageCandidates_public (endpoint : Ty) {a : CompareTy}
    (ha : a ∈ frozenImageCandidates endpoint) : Public a := by
  obtain ⟨fragment, hf, ha⟩ := List.mem_flatMap.mp ha
  exact subtrees_public (frozenFragments_public endpoint none hf) ha

 theorem frozen_images_below {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr}
    (hh : FrozenHead ((CompareTy.ofTy body).subst ts ms))
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal ((CompareTy.ofTy body).subst ts ms) m) (.ofTy endpoint)) :
    ∀ v ∈ body.typeVars, ts v ∈ frozenImageCandidates endpoint := by
  intro v hv
  exact List.mem_flatMap.mpr ⟨_, frozen_fragment_below hΔ hh hm h,
    image_mem_subtrees body ts ms hv⟩

 theorem frozen_images_above {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr}
    (hh : FrozenHead ((CompareTy.ofTy body).subst ts ms))
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.ofTy endpoint) (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∀ v ∈ body.typeVars, ts v ∈ frozenImageCandidates endpoint := by
  intro v hv
  exact List.mem_flatMap.mpr ⟨_, frozen_fragment_above hΔ hh hm h,
    image_mem_subtrees body ts ms hv⟩

/-- One binding for every original variable key, with repeated occurrences
sharing the same literal image. -/
def frozenBindings (body : Ty) (ts : TypeVar → CompareTy) : List (TypeVar × CompareTy) :=
  body.typeVariables.map fun v => (v, ts v)

 theorem frozenBindings_keys (body : Ty) (ts : TypeVar → CompareTy) :
    (frozenBindings body ts).map Prod.fst = body.typeVariables := by
  simp only [frozenBindings, List.map_map, Function.comp_def]
  exact List.map_id _

 theorem frozenBindings_lookup (body : Ty) (ts : TypeVar → CompareTy) {v : TypeVar}
    (hv : v ∈ body.typeVars) : (frozenBindings body ts).lookup v = some (ts v) :=
  lookup_map_self _ _ ((body.mem_typeVariables v).mpr hv)

 theorem frozenBindings_members {body : Ty} {ts : TypeVar → CompareTy}
    {entry : TypeVar × CompareTy} (he : entry ∈ frozenBindings body ts) :
    entry.1 ∈ body.typeVars ∧ entry.2 = ts entry.1 := by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
  exact ⟨(body.mem_typeVariables v).mp hv, rfl⟩

 theorem frozen_bindings_below {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr}
    (hh : FrozenHead ((CompareTy.ofTy body).subst ts ms))
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.modal ((CompareTy.ofTy body).subst ts ms) m) (.ofTy endpoint)) :
    ∀ entry ∈ frozenBindings body ts, entry.2 ∈ frozenImageCandidates endpoint := by
  intro entry he
  obtain ⟨hv, hi⟩ := frozenBindings_members he
  rw [hi]
  exact frozen_images_below hΔ body ts ms hh hm h entry.1 hv

 theorem frozen_bindings_above {Δ : Bounds} (hΔ : Δ.TypeBoundsDefined)
    (body : Ty) (ts : TypeVar → CompareTy) (ms : ModVar → ModExpr)
    {endpoint : Ty} {m : ModExpr}
    (hh : FrozenHead ((CompareTy.ofTy body).subst ts ms))
    (hm : ¬Entails Δ (.defined m))
    (h : AlgebraSubtype Δ (.ofTy endpoint) (.modal ((CompareTy.ofTy body).subst ts ms) m)) :
    ∀ entry ∈ frozenBindings body ts, entry.2 ∈ frozenImageCandidates endpoint := by
  intro entry he
  obtain ⟨hv, hi⟩ := frozenBindings_members he
  rw [hi]
  exact frozen_images_above hΔ body ts ms hh hm h entry.1 hv

end ModalityInference.ComparisonPartialStructuredCapsule
