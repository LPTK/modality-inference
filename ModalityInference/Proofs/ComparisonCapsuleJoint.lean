import ModalityInference.Proofs.ComparisonCapsuleCollected
import ModalityInference.Proofs.SchemeModeWitness
import ModalityInference.Proofs.ComparisonModeRestriction
import ModalityInference.Proofs.ComparisonReductionSupport

namespace ModalityInference.ComparisonCapsuleIntervals

/-- Instantiate the shared source modality action while retaining literal
public endpoints and the original request grouping. -/
def Request.mapAction (images : ModVar → ModExpr) (r : Request) : Request :=
  { r with action := r.action.subst images }

def Binding.mapActions (images : ModVar → ModExpr) (b : Binding) : Binding :=
  { b with requests := b.requests.map (Request.mapAction images) }

theorem filter_mapAction (images : ModVar → ModExpr) (name : Nat) (rs : List Request) :
    (rs.map (Request.mapAction images)).filter (fun r => r.name == name) =
      (rs.filter (fun r => r.name == name)).map (Request.mapAction images) := by
  simp only [List.filter_map, Function.comp_def, Request.mapAction]

theorem plan_mapAction (images : ModVar → ModExpr) (total : ModExpr → Bool)
    (name fresh : Nat) (rs : List Request) :
    plan total name fresh (rs.map (Request.mapAction images)) =
      (plan total name fresh rs).map (Binding.mapActions images) := by
  unfold plan
  rw [filter_mapAction]
  cases hg : rs.filter (fun r => r.name == name) with
  | nil => rfl
  | cons r rest =>
    simp only [List.map_cons, List.all_map, Function.comp_def,
      Request.mapAction, Request.base]
    split <;> rfl

theorem Request.suffix_support (total : ModExpr → Bool) (r : Request) :
    ∀ v ∈ (r.suffix total).vars, v ∈ r.endpoint.modVars :=
  ComparisonPartialModes.recompose_support _
    (ComparisonBody.peelFuel_modeSupport total _ r.endpoint (fun _ h => h)).2

end ModalityInference.ComparisonCapsuleIntervals

namespace ModalityInference.ComparisonCapsuleContext

open ComparisonCapsuleIntervals

/-- A proof witness uses the same source action everywhere and adds exactly
one expression at each fresh suffix coordinate. -/
def jointModes (images : ModVar → ModExpr) (fresh : List Nat)
    (suffix : Nat → ModExpr) : ModVar → ModExpr
  | .flex n => if fresh.contains n then suffix n else images (.flex n)
  | .rigid n => images (.rigid n)

theorem jointModes_fresh (images : ModVar → ModExpr) (fresh : List Nat)
    (suffix : Nat → ModExpr) {n : Nat} (hn : n ∈ fresh) :
    jointModes images fresh suffix (.flex n) = suffix n := by
  simp only [jointModes, List.contains_iff_mem.mpr hn, ↓reduceIte]

theorem jointModes_old (images : ModVar → ModExpr) (fresh : List Nat)
    (suffix : Nat → ModExpr) {v : ModVar} (hv : ∀ n ∈ fresh, v ≠ .flex n) :
    jointModes images fresh suffix v = images v := by
  cases v with
  | rigid n => rfl
  | flex n =>
    have hn : n ∉ fresh := fun hn => hv n hn rfl
    simp only [jointModes, List.contains_iff_mem, hn, ↓reduceIte]

theorem jointModes_fixed (images : ModVar → ModExpr) (source fresh : List Nat)
    (suffix : Nat → ModExpr)
    (hfixed : ∀ v, (∀ n ∈ source, v ≠ .flex n) → images v = .var v) :
    ∀ v, (∀ n ∈ source ++ fresh, v ≠ .flex n) →
      jointModes images fresh suffix v = .var v := by
  intro v hv
  rw [jointModes_old images fresh suffix (fun n hn => hv n (List.mem_append_right _ hn))]
  exact hfixed v (fun n hn => hv n (List.mem_append_left _ hn))

theorem jointModes_total {Δ : Bounds} (images : ModVar → ModExpr) (fresh : List Nat)
    (suffix : Nat → ModExpr)
    (hi : ∀ v, Entails Δ (.defined (images v)))
    (hq : ∀ n ∈ fresh, Entails Δ (.defined (suffix n))) :
    ∀ v, Entails Δ (.defined (jointModes images fresh suffix v)) := by
  intro v
  cases v with
  | rigid n => exact hi _
  | flex n =>
    simp only [jointModes]
    split
    · next hn => exact hq n (List.contains_iff_mem.mp hn)
    · exact hi _

/-- Original target suffixes remain fixed while each source occurrence uses the
shared source action and its group's one suffix image. -/
theorem request_bound_joint {total : ModExpr → Bool} {images : ModVar → ModExpr}
    {fresh : List Nat} {suffix : Nat → ModExpr} {r : Request} {n : Nat}
    (hn : n ∈ fresh)
    (hendpoint : ∀ v ∈ r.endpoint.modVars, images v = .var v)
    (hendpointFresh : ∀ v ∈ r.endpoint.modVars, ∀ k ∈ fresh, v ≠ .flex k)
    (hactionFresh : ∀ v ∈ r.action.vars, ∀ k ∈ fresh, v ≠ .flex k) :
    (r.bound total (.var (.flex n))).subst TypeExpr.var (jointModes images fresh suffix) =
      (r.mapAction images).bound total (suffix n) := by
  have hs : (r.suffix total).subst (jointModes images fresh suffix) = r.suffix total := by
    rw [ModExpr.subst_congr _ (τ := ModExpr.var) (fun v hv =>
      (jointModes_old images fresh suffix (hendpointFresh v (r.suffix_support total v hv))).trans
        (hendpoint v (r.suffix_support total v hv)))]
    exact ModExpr.subst_id _
  have ha : r.action.subst (jointModes images fresh suffix) = r.action.subst images :=
    ModExpr.subst_congr _ (fun v hv => jointModes_old images fresh suffix (hactionFresh v hv))
  simp only [Request.suffix] at hs
  cases hp : r.isLower <;>
    simp only [Request.bound, hp, Bool.false_eq_true, ↓reduceIte, Constraint.subst,
      ModExpr.subst, jointModes_fresh images fresh suffix hn, hs, ha,
      Request.mapAction, Request.suffix]

/-- A finite family of suffix solutions and one shared source action induce
one eventual production synthesis run for all binding goals together. -/
theorem run_complete_joint {Δ : Bounds} (total : ModExpr → Bool)
    (source : List Nat) (bs : List Binding) (images : ModVar → ModExpr)
    (suffix : Nat → ModExpr)
    (hfixed : ∀ v, (∀ n ∈ source, v ≠ .flex n) → images v = .var v)
    (hscope : ∀ v ∈ Δ.modVars, ∀ n ∈ source ++ bs.map Binding.fresh, v ≠ .flex n)
    (htotal : ∀ v, Entails Δ (.defined (images v)))
    (hsuffix : ∀ b ∈ bs, Entails Δ (.defined (suffix b.fresh)))
    (hendpoint : ∀ b ∈ bs, ∀ r ∈ b.requests,
      ∀ v ∈ r.endpoint.modVars, images v = .var v)
    (hendpointFresh : ∀ b ∈ bs, ∀ r ∈ b.requests,
      ∀ v ∈ r.endpoint.modVars, ∀ k ∈ bs.map Binding.fresh, v ≠ .flex k)
    (hactionFresh : ∀ b ∈ bs, ∀ r ∈ b.requests,
      ∀ v ∈ r.action.vars, ∀ k ∈ bs.map Binding.fresh, v ≠ .flex k)
    (hgoals : ∀ b ∈ bs, ∀ r ∈ b.requests,
      Entails Δ ((r.mapAction images).bound total (suffix b.fresh))) :
    ∃ n, ∀ fuel ≥ n, ∃ result, SchemeModeSynthesis.run fuel
      (source ++ bs.map Binding.fresh)
      (.imp (boundsModeFormula Δ) (boundsModeFormula (goals total bs))) = .success result := by
  apply SchemeModeSynthesis.run_complete_substituted
    (jointModes_fixed images source (bs.map Binding.fresh) suffix hfixed) hscope
  · intro η hη v
    apply jointModes_total images (bs.map Binding.fresh) suffix htotal _ v η hη
    intro k hk
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hk
    exact hsuffix b hb
  · intro η hη c hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    obtain ⟨b, hb, hd⟩ := List.mem_flatMap.mp hd
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hd
    rw [request_bound_joint (List.mem_map.mpr ⟨b, hb, rfl⟩)
      (hendpoint b hb r hr) (hendpointFresh b hb r hr) (hactionFresh b hb r hr)]
    have h := hgoals b hb r hr
    cases hp : r.isLower <;> simp only [Request.mapAction, Request.bound, hp,
      Bool.false_eq_true, ↓reduceIte, Entails, ModeSatisfies] at h ⊢ <;> exact h.denote hη

private theorem lookup_mem_keys_nodup {α : Type} {entries : List (Nat × α)}
    (hn : (entries.map Prod.fst).Nodup) {n : Nat} {a : α} (ha : (n, a) ∈ entries) :
    entries.lookup n = some a := by
  induction entries with
  | nil => contradiction
  | cons entry entries ih =>
    rcases entry with ⟨key, value⟩
    have hh := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with he | he
    · cases he
      simp
    · have hne : n ≠ key := by
        intro hn
        exact hh.1 (hn ▸ List.mem_map.mpr ⟨(n, a), he, rfl⟩)
      have hb : (n == key) = false := by simp [hne]
      simpa only [List.lookup_cons, hb] using ih hh.2 he

/-- Independent local existence proofs assemble into one suffix environment
because the bindings reserve distinct fresh coordinates. -/
theorem suffix_family {bs : List Binding} (hn : (bs.map Binding.fresh).Nodup)
    {R : Binding → ModExpr → Prop}
    (h : ∀ b ∈ bs, ∃ q, R b q) :
    ∃ suffix : Nat → ModExpr, ∀ b ∈ bs, R b (suffix b.fresh) := by
  classical
  let chosen : Binding → ModExpr := fun b =>
    if hb : b ∈ bs then Classical.choose (h b hb) else .epsilon
  have hchosen : ∀ b ∈ bs, R b (chosen b) := by
    intro b hb
    simpa only [chosen, dif_pos hb] using Classical.choose_spec (h b hb)
  let entries := bs.map (fun b => (b.fresh, chosen b))
  have hentries : (entries.map Prod.fst).Nodup := by
    simpa only [entries, List.map_map, Function.comp_def] using hn
  let suffix : Nat → ModExpr := fun n => (entries.lookup n).getD .epsilon
  refine ⟨suffix, ?_⟩
  intro b hb
  have he := lookup_mem_keys_nodup hentries (List.mem_map.mpr ⟨b, hb, rfl⟩)
  simpa only [suffix, he, Option.getD_some] using hchosen b hb

/-- Each binding may prove its own suffix exists; all of them still use the
same source-mode action in the single synthesis problem. -/
theorem run_complete_suffix_family {Δ : Bounds} (total : ModExpr → Bool)
    (source : List Nat) (bs : List Binding) (images : ModVar → ModExpr)
    (hn : (bs.map Binding.fresh).Nodup)
    (hfixed : ∀ v, (∀ n ∈ source, v ≠ .flex n) → images v = .var v)
    (hscope : ∀ v ∈ Δ.modVars, ∀ n ∈ source ++ bs.map Binding.fresh, v ≠ .flex n)
    (htotal : ∀ v, Entails Δ (.defined (images v)))
    (hendpoint : ∀ b ∈ bs, ∀ r ∈ b.requests,
      ∀ v ∈ r.endpoint.modVars, images v = .var v)
    (hendpointFresh : ∀ b ∈ bs, ∀ r ∈ b.requests,
      ∀ v ∈ r.endpoint.modVars, ∀ k ∈ bs.map Binding.fresh, v ≠ .flex k)
    (hactionFresh : ∀ b ∈ bs, ∀ r ∈ b.requests,
      ∀ v ∈ r.action.vars, ∀ k ∈ bs.map Binding.fresh, v ≠ .flex k)
    (hsolutions : ∀ b ∈ bs, ∃ q, Entails Δ (.defined q) ∧
      ∀ r ∈ b.requests, Entails Δ ((r.mapAction images).bound total q)) :
    ∃ n, ∀ fuel ≥ n, ∃ result, SchemeModeSynthesis.run fuel
      (source ++ bs.map Binding.fresh)
      (.imp (boundsModeFormula Δ) (boundsModeFormula (goals total bs))) = .success result := by
  obtain ⟨suffix, hs⟩ := suffix_family hn hsolutions
  exact run_complete_joint total source bs images suffix hfixed hscope htotal
    (fun b hb => (hs b hb).1) hendpoint hendpointFresh hactionFresh
    (fun b hb => (hs b hb).2)

end ModalityInference.ComparisonCapsuleContext
