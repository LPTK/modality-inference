import ModalityInference.Proofs.ComparisonDeclaredCuts
import ModalityInference.Proofs.ComparisonModeRestriction

/-! Finite root paths through whole declared bounds. Action classes use only
modality names occurring in the original assumptions and public endpoints.
The crossing bound is independent of the input derivation. Constructor-child
comparisons remain full subtype premises; this module does not give a type
witness depth bound or a finite grammar for shared internal lattice images. -/

namespace ModalityInference.ComparisonDeclaredBoundary

/-- One literal declared edge with its guarded outer action. -/
structure Vertex (Δ : Bounds) where
  source : Ty
  target : Ty
  mode : ModExpr
  declared : Constraint.sub source target ∈ Δ
  defined : Entails Δ (.defined mode)

def Vertex.left (v : Vertex Δ) : Ty := .modal v.source v.mode
def Vertex.right (v : Vertex Δ) : Ty := .modal v.target v.mode

/-- A finite sequence of whole declared edges. Between edges, only constructor
segments are used; their child comparisons retain the full original relation. -/
inductive Walk (Δ : Bounds) : Ty → Ty → List (Vertex Δ) → Prop where
  | nil {s t} : Segment Δ s t → Walk Δ s t []
  | cons {s t vs} (v : Vertex Δ) : Segment Δ s v.left →
      Walk Δ v.right t vs → Walk Δ s t (v :: vs)

theorem Walk.subtype {Δ s t vs} (h : Walk Δ s t vs) : Subtype Δ s t := by
  induction h with
  | nil h => exact h.subtype
  | cons v h _ ih =>
    exact .trans h.subtype (.trans (.congr (.bound v.declared) (.refl v.defined)) ih)

theorem Walk.pre {Δ s t u vs} (h : Walk Δ s t vs) (hs : Segment Δ u s) :
    Walk Δ u t vs := by
  cases h with
  | nil h => exact .nil (.trans hs h)
  | cons v h tail => exact .cons v (.trans hs h) tail

theorem Walk.append {Δ s t u vs ws} (h : Walk Δ s t vs) (h' : Walk Δ t u ws) :
    Walk Δ s u (vs ++ ws) := by
  induction h with
  | nil h => exact h'.pre h
  | cons v h _ ih => exact .cons v h (ih h')

def Vertex.act (v : Vertex Δ) (m : ModExpr) (hm : Entails Δ (.defined m)) : Vertex Δ :=
  { v with mode := .compose v.mode m
           defined := Entails.defined_compose_iff.mpr ⟨v.defined, hm⟩ }

theorem Walk.congr {Δ s t vs m n} (h : Walk Δ s t vs) (hmn : Submode Δ m n) :
    ∃ ws, Walk Δ (.modal s m) (.modal t n) ws := by
  induction h with
  | nil h => exact ⟨[], .nil (.congr h hmn)⟩
  | cons v hs _ ih =>
    obtain ⟨ws, hw⟩ := ih
    refine ⟨v.act m hmn.defined.1 :: ws, .cons _ ?_ ?_⟩
    · exact .trans (.congr hs (.refl hmn.defined.1)) .compose
    · exact hw.pre .composeRev

/-- Every ordinary subtype derivation has a finite whole-edge trace; this does
not discard its full constructor-child premises. -/
theorem Subtype.walk {Δ s t} (h : Subtype Δ s t) : ∃ vs, Walk Δ s t vs := by
  induction h with
  | refl => exact ⟨[], .nil .refl⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨vs,hv⟩ := ih₁
    obtain ⟨ws,hw⟩ := ih₂
    exact ⟨vs ++ ws,hv.append hw⟩
  | @bound a b hc =>
    exact ⟨[⟨a,b,.epsilon,hc,fun _ _ => rfl⟩], .cons _ .identityRev (.nil .identity)⟩
  | identity => exact ⟨[], .nil .identity⟩
  | identityRev => exact ⟨[], .nil .identityRev⟩
  | compose => exact ⟨[], .nil .compose⟩
  | composeRev => exact ⟨[], .nil .composeRev⟩
  | congr _ hm ih => obtain ⟨vs,hv⟩ := ih; exact hv.congr hm
  | prod h₁ h₂ => exact ⟨[], .nil (.prod h₁ h₂)⟩
  | sum h₁ h₂ => exact ⟨[], .nil (.sum h₁ h₂)⟩
  | fn h₁ h₂ hm => exact ⟨[], .nil (.fn h₁ h₂ hm)⟩

theorem Walk.suffix {Δ s t} {pre post : List (Vertex Δ)} {v : Vertex Δ}
    (h : Walk Δ s t (pre ++ v :: post)) : Walk Δ v.right t post := by
  induction pre generalizing s with
  | nil => cases h with | cons _ _ h => exact h
  | cons a pre ih => cases h with | cons _ _ h => exact ih h

/-- Repeated output classes can be removed without replacing any declared
edge or inventing an action. The returned list is drawn from the input trace. -/
theorem Walk.simple {Δ s t vs} {K : Type*} (key : Vertex Δ → K)
    (h : Walk Δ s t vs)
    (same : ∀ u ∈ vs, ∀ v ∈ vs, key u = key v → Segment Δ u.right v.right) :
    ∃ ws, Walk Δ s t ws ∧ ws ⊆ vs ∧ (ws.map key).Nodup := by
  classical
  induction h with
  | nil h => exact ⟨[], .nil h, List.Subset.refl _, by simp⟩
  | @cons s t vs u hs ht ih =>
    obtain ⟨ws, hw, hsub, hn⟩ := ih (fun x hx y hy =>
      same x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    by_cases hu : key u ∈ ws.map key
    · obtain ⟨v, hv, he⟩ := List.mem_map.mp hu
      obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hv
      have hh := hw.suffix
      have hlink := same u (by simp) v (by simp only [List.mem_cons]; exact Or.inr (hsub (by simp))) he.symm
      have hn' := (List.nodup_append.mp (show ((pre.map key) ++ key v :: post.map key).Nodup by
        simpa using hn)).2.1
      refine ⟨u :: post, .cons u hs (hh.pre hlink), ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub (by simp [hx]))
      · simp only [List.map_cons, List.nodup_cons] at hn' ⊢
        exact ⟨he ▸ hn'.1, hn'.2⟩
    · refine ⟨u :: ws, .cons u hs hw, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub hx)
      · exact List.nodup_cons.mpr ⟨hu, hn⟩

private theorem public_fixed {ms : ModVar → ModExpr} (a : Ty)
    (h : ∀ v ∈ a.modVars, ms v = .var v) : a.subst TypeExpr.var ms = a := by
  calc
    _ = a.subst TypeExpr.var ModExpr.var := a.subst_congr (fun _ _ => rfl) h
    _ = a := a.subst_id

private theorem edge_source_fixed {Δ ms a b} (h : ComparisonModeRestriction.Fixed Δ ms)
    (hb : Constraint.sub a b ∈ Δ) : a.subst TypeExpr.var ms = a :=
  public_fixed a (fun v hv => h.fixed v ((Δ.mem_modVars_iff v).mpr
    ⟨.sub a b, hb, by simp [Constraint.modVars, hv]⟩))

private theorem edge_target_fixed {Δ ms a b} (h : ComparisonModeRestriction.Fixed Δ ms)
    (hb : Constraint.sub a b ∈ Δ) : b.subst TypeExpr.var ms = b :=
  public_fixed b (fun v hv => h.fixed v ((Δ.mem_modVars_iff v).mpr
    ⟨.sub a b, hb, by simp [Constraint.modVars, hv]⟩))

private theorem subtype_modes {Δ ms s t} (hm : ComparisonModeRestriction.Fixed Δ ms)
    (h : Subtype Δ s t) :
    Subtype Δ (s.subst TypeExpr.var ms) (t.subst TypeExpr.var ms) := by
  induction h <;> try simp only [TypeExpr.subst]
  case refl => exact .refl
  case trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  case bound h => rw [edge_source_fixed hm h, edge_target_fixed hm h]; exact .bound h
  case identity => exact .identity
  case identityRev => exact .identityRev
  case compose => exact .compose
  case composeRev => exact .composeRev
  case congr _ h ih => exact .congr ih (hm.submode h)
  case prod _ _ ih₁ ih₂ => exact .prod ih₁ ih₂
  case sum _ _ ih₁ ih₂ => exact .sum ih₁ ih₂
  case fn _ _ h ih₁ ih₂ => exact .fn ih₁ ih₂ (hm.submode h)

private theorem Segment.modes {Δ ms s t} (hm : ComparisonModeRestriction.Fixed Δ ms)
    (h : Segment Δ s t) :
    Segment Δ (s.subst TypeExpr.var ms) (t.subst TypeExpr.var ms) := by
  induction h <;> try simp only [TypeExpr.subst]
  case refl => exact .refl
  case trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  case identity => exact .identity
  case identityRev => exact .identityRev
  case compose => exact .compose
  case composeRev => exact .composeRev
  case congr _ h ih => exact .congr ih (hm.submode h)
  case prod h₁ h₂ => exact .prod (subtype_modes hm h₁) (subtype_modes hm h₂)
  case sum h₁ h₂ => exact .sum (subtype_modes hm h₁) (subtype_modes hm h₂)
  case fn h₁ h₂ h => exact .fn (subtype_modes hm h₁) (subtype_modes hm h₂) (hm.submode h)

def Vertex.restrict {Δ} (names : Finset ModVar) (hΔ : Δ.modVars ⊆ names)
    (v : Vertex Δ) : Vertex Δ :=
  {v with mode := v.mode.subst (ComparisonModeRestriction.restrict names)
          defined := (ComparisonModeRestriction.restrict_fixed Δ names hΔ).defined v.defined}

theorem Walk.restrict {Δ s t vs} (names : Finset ModVar) (hΔ : Δ.modVars ⊆ names)
    (h : Walk Δ s t vs) :
    Walk Δ (s.subst TypeExpr.var (ComparisonModeRestriction.restrict names))
      (t.subst TypeExpr.var (ComparisonModeRestriction.restrict names))
      (vs.map (Vertex.restrict names hΔ)) := by
  let hm := ComparisonModeRestriction.restrict_fixed Δ names hΔ
  induction h with
  | nil h => exact .nil (h.modes hm)
  | cons v hs ht ih =>
    refine .cons (v.restrict names hΔ) ?_ ?_
    · simpa only [Vertex.left, Vertex.restrict, TypeExpr.subst, edge_source_fixed hm v.declared]
        using hs.modes hm
    · simpa only [Vertex.right, Vertex.restrict, TypeExpr.subst, edge_target_fixed hm v.declared]
        using ih

private instance modeFintype : Fintype Mode where
  elems := Mode.all.toFinset
  complete := by
    intro ⟨l,o,u⟩
    cases l <;> cases o <;> cases u <;> decide

private def extend (names : Finset ModVar) (η : names → Mode) (v : ModVar) : Mode :=
  if h : v ∈ names then η ⟨v,h⟩ else Mode.identity

private def table (names : Finset ModVar) (m : ModExpr) : (names → Mode) → Option Mode :=
  fun η => m.eval (some ∘ extend names η)

private theorem table_eval {names : Finset ModVar} {m : ModExpr} (hs : m.vars ⊆ names)
    (η : ModVar → Mode) : table names m (fun v => η v) = m.eval (some ∘ η) := by
  apply m.eval_congr
  intro v hv
  simp [extend, hs hv]

private abbrev Key (Δ : Bounds) (names : Finset ModVar) :=
  ↥(Δ.toFinset) × ((names → Mode) → Option Mode)

private def key (names : Finset ModVar) (v : Vertex Δ) : Key Δ names :=
  (⟨.sub v.source v.target, List.mem_toFinset.mpr v.declared⟩, table names v.mode)

private theorem key_same {Δ names} {u v : Vertex Δ}
    (hu : u.mode.vars ⊆ names) (hv : v.mode.vars ⊆ names)
    (he : key names u = key names v) : Segment Δ u.right v.right := by
  have hb : Constraint.sub u.source u.target = .sub v.source v.target :=
    congrArg (fun k => k.1.val) he
  have ht : u.target = v.target := (Constraint.sub.inj hb).2
  apply Segment.congr (ht ▸ .refl)
  apply Submode.valid
  intro η hη
  have hm := congrFun (congrArg Prod.snd he) (fun w => η w)
  have hm' : u.mode.eval (some ∘ η) = v.mode.eval (some ∘ η) :=
    (table_eval hu η).symm.trans (hm.trans (table_eval hv η))
  obtain ⟨m,hme⟩ := Option.isSome_iff_exists.mp (u.defined η hη)
  exact ⟨m,m,hme,hm'.symm.trans hme,by simp [Mode.le]⟩

/-- The number of literal declared edges times the number of finite action
truth tables on the retained input names. -/
noncomputable def pathBudget (Δ : Bounds) (names : Finset ModVar) : Nat :=
  Fintype.card (Key Δ names)

theorem pathBudget_eq (Δ : Bounds) (names : Finset ModVar) :
    pathBudget Δ names = Δ.toFinset.card * 9 ^ (8 ^ names.card) := by
  classical
  have hm : Fintype.card Mode = 8 := by decide
  simp only [pathBudget, Key, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_option, Fintype.card_coe, hm]

theorem Walk.finite {Δ s t vs} {names : Finset ModVar} (h : Walk Δ s t vs)
    (hs : ∀ v ∈ vs, v.mode.vars ⊆ names) :
    ∃ ws, Walk Δ s t ws ∧ ws ⊆ vs ∧ ws.length ≤ pathBudget Δ names := by
  obtain ⟨ws,hw,hsub,hn⟩ := h.simple (key names) (fun u hu v hv he =>
    key_same (hs u hu) (hs v hv) he)
  refine ⟨ws,hw,hsub,?_⟩
  simpa only [List.length_map] using hn.length_le_card

/-- Every root declared-bound trace can be saturated using only input-relative
endpoint/action classes. This is a bound on whole declared-edge crossings;
constructor-child comparisons remain full derivations. -/
theorem Subtype.finite_walk {Δ s t} (h : Subtype Δ s t) :
    let names := Δ.modVars ∪ s.modVars ∪ t.modVars
    ∃ vs, Walk Δ s t vs ∧ (∀ v ∈ vs, v.mode.vars ⊆ names) ∧
      vs.length ≤ pathBudget Δ names := by
  let names := Δ.modVars ∪ s.modVars ∪ t.modVars
  have hΔ : Δ.modVars ⊆ names := by intro v hv; simp [names, hv]
  obtain ⟨vs,hv⟩ := ComparisonDeclaredBoundary.Subtype.walk h
  have hw := hv.restrict names hΔ
  have hs : s.subst TypeExpr.var (ComparisonModeRestriction.restrict names) = s :=
    public_fixed s (fun v hv => by simp [ComparisonModeRestriction.restrict, names, hv])
  have ht : t.subst TypeExpr.var (ComparisonModeRestriction.restrict names) = t :=
    public_fixed t (fun v hv => by simp [ComparisonModeRestriction.restrict, names, hv])
  rw [hs,ht] at hw
  have hsupport : ∀ v ∈ vs.map (Vertex.restrict names hΔ), v.mode.vars ⊆ names := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
    exact ComparisonModeRestriction.restrict_support names w.mode
  obtain ⟨ws,hws,hsub,hlen⟩ := hw.finite hsupport
  exact ⟨ws,hws,fun v hv => hsupport v (hsub hv),hlen⟩

/-- Exact root-path certificates, with an input-relative crossing budget. -/
theorem subtype_iff_finite_walk {Δ s t} :
    Subtype Δ s t ↔
      let names := Δ.modVars ∪ s.modVars ∪ t.modVars
      ∃ vs, Walk Δ s t vs ∧ (∀ v ∈ vs, v.mode.vars ⊆ names) ∧
        vs.length ≤ pathBudget Δ names := by
  constructor
  · exact ComparisonDeclaredBoundary.Subtype.finite_walk
  · rintro ⟨vs,h,_,_⟩
    exact h.subtype

end ModalityInference.ComparisonDeclaredBoundary
