import ModalityInference.Proofs.RewriteModels
import ModalityInference.Proofs.Substitution

namespace ModalityInference

def GroundAssignment.setType (ρ : GroundAssignment) (v : TypeVar) (a : GroundTy) : GroundAssignment :=
  {ρ with types := fun w => if w = v then a else ρ.types w}

theorem Substitution.singleType_realizes {ρ : GroundAssignment} {n t a}
    (ha : t.realize ρ = some a) (v : TypeVar) :
    (({types := [(n,t)]} : Substitution).type v).realize ρ =
      some ((ρ.setType (.flex n) a).types v) := by
  cases v
  case flex k =>
    cases hk : (k == n) <;>
      simp [Substitution.type, List.lookup_cons, hk, GroundAssignment.setType, ha, TypeExpr.realize]
    all_goals simp_all [beq_iff_eq]
  case rigid k => rfl

theorem TypeExpr.realize_setType {ρ : GroundAssignment} {n t a}
    (ha : t.realize ρ = some a) (b : Ty) :
    (({types := [(n,t)]} : Substitution).ty b).realize ρ = (b.realize (ρ.setType (.flex n) a)) :=
  b.realize_subst_congr (fun v _ => Substitution.singleType_realizes ha v)
    (fun v _ => by cases v <;> rfl)

theorem TypeExpr.realize_setType_fresh {ρ : GroundAssignment} {n a} (b : Ty)
    (hn : TypeVar.flex n ∉ b.typeVars) : b.realize (ρ.setType (.flex n) a) = b.realize ρ := by
  apply b.realize_congr
  · intro v hv
    simp only [GroundAssignment.setType]
    split
    · next h => exact False.elim (hn (h ▸ hv))
    · rfl
  · exact fun _ _ => rfl

private theorem lookup_map_values (xs : List (Nat × Ty)) (f : Ty → Ty) (n : Nat) :
    (xs.map (fun (k, v) => (k, f v))).lookup n = (xs.lookup n).map f := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨k, v⟩
    cases h : (n == k) <;> simp [List.lookup_cons, h, ih]

theorem Substitution.extendType_type {σ : Substitution} {n t}
    (hn : n ∉ σ.types.map Prod.fst) (v : TypeVar) :
    (σ.extendType n t).type v = ({types := [(n,t)]} : Substitution).ty (σ.type v) := by
  have hf : σ.types.filter (fun p => p.1 != n) = σ.types := by
    apply List.filter_eq_self.mpr
    intro p hp
    exact bne_iff_ne.mpr (fun he => hn (List.mem_map.mpr ⟨p, hp, he⟩))
  cases v
  case rigid k => rfl
  case flex k =>
    simp only [Substitution.extendType, Substitution.type, hf, List.lookup_cons, lookup_map_values]
    by_cases hk : k = n
    · subst k
      have hnone : σ.types.lookup n = none := List.lookup_eq_none_iff.mpr fun p hp => by
        simpa only [bne_iff_ne] using
          (fun he : n = p.1 => hn (List.mem_map.mpr ⟨p, hp, he.symm⟩))
      simp [hnone, Substitution.ty, TypeExpr.subst, Substitution.type]
    · have hkn : (k == n) = false := by simpa using hk
      cases σ.types.lookup k <;>
        simp [hkn, Substitution.ty, TypeExpr.subst, Substitution.type, List.lookup_cons]

theorem Substitution.ground_modes_of_no_modes {σ : Substitution} (hσ : σ.modes = [])
    (ρ : GroundAssignment) : (σ.ground ρ).modes = ρ.modes := by
  funext v
  cases v <;> simp [Substitution.ground, Substitution.mode, hσ, ModExpr.eval]

namespace Deferred

theorem ConfigModels.substitute {n t scope ρ} {s : RewriteConfig}
    (hn : TypeVar.flex n ∉ t.typeVars) (hk : n ∉ s.substitution.types.map Prod.fst) :
    ConfigModels scope {s with pending := .equal (.flex n) t :: s.pending} ρ ↔
    ConfigModels scope
      {pending := (Substitution.mk [(n,t)] []).bounds (s.constraints ++ t.wellFormedBounds)
       bounds := [], substitution := s.substitution.extendType n t} ρ := by
  constructor
  · rintro ⟨η, hη, htypes, hmodes⟩
    change GroundModels η (.equal (.flex n) t :: s.constraints) at hη
    obtain ⟨a, ha, hva, hav⟩ := hη (.equal (.flex n) t) (by simp)
    have heq : ∀ v, (η.types v).Equivalent ((η.setType (.flex n) a).types v) := by
      intro v
      by_cases hv : v = .flex n
      · subst v
        simpa [GroundAssignment.setType, GroundTy.Equivalent] using
          And.intro (GroundOrder.of_subtype hva) (GroundOrder.of_subtype hav)
      · simpa [GroundAssignment.setType, hv] using GroundTy.Equivalent.refl (η.types v)
    have hbase : GroundModels (η.setType (.flex n) a) s.constraints :=
      (GroundModels.equivalent _ (fun v _ => heq v) (fun _ _ => rfl)).mp
        (fun c hc => hη c (List.mem_cons_of_mem _ hc))
    have hw : GroundModels (η.setType (.flex n) a) t.wellFormedBounds :=
      (t.wellFormedBounds_ground _).mpr ((t.wellFormedBounds_spec _).mpr
        (by simp [(t.realize_setType_fresh hn).trans ha]))
    have hnew : GroundModels η ((Substitution.mk [(n,t)] []).bounds
        (s.constraints ++ t.wellFormedBounds)) :=
      (GroundModels.subst_congr _ (fun v _ => Substitution.singleType_realizes ha v)
        (fun v _ => by cases v <;> rfl)).mpr
        (by simpa [GroundModels, List.mem_append, or_imp, forall_and] using And.intro hbase hw)
    refine ⟨η, ?_, ?_, hmodes⟩
    · simpa [RewriteConfig.constraints] using hnew
    · intro v hv
      obtain ⟨b, hb, hbρ, hρb⟩ := htypes v hv
      obtain ⟨b', hb', hbb'⟩ := ((s.substitution.type v).realize_equivalent
        (fun v _ => heq v) (fun _ _ => rfl)).some_left hb
      refine ⟨b', ?_, hbb'.2.to_subtype.trans hbρ, hρb.trans hbb'.1.to_subtype⟩
      change ((s.substitution.extendType n t).type v).realize η = some b'
      rw [Substitution.extendType_type hk, TypeExpr.realize_setType ha]
      exact hb'
  · rintro ⟨η, hη, htypes, hmodes⟩
    let one : Substitution := {types := [(n,t)]}
    have hmodel : GroundModels η (one.bounds (s.constraints ++ t.wellFormedBounds)) := by
      simpa [RewriteConfig.constraints] using hη
    have hw : ModeModels t.wellFormedBounds η.modes := by
      have hp := hmodel.pullback.modeModels
      rw [Substitution.ground_modes_of_no_modes (σ := one) rfl η] at hp
      exact fun c hc => hp c (List.mem_append_right _ hc)
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ((t.wellFormedBounds_spec η).mp hw)
    have hback : GroundModels (η.setType (.flex n) a) (s.constraints ++ t.wellFormedBounds) :=
      (GroundModels.subst_congr _ (fun v _ => Substitution.singleType_realizes ha v)
        (fun v _ => by cases v <;> rfl)).mp hmodel
    refine ⟨η.setType (.flex n) a, ?_, ?_, hmodes⟩
    · change GroundModels (η.setType (.flex n) a) (.equal (.flex n) t :: s.constraints)
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · refine ⟨a, (t.realize_setType_fresh hn).trans ha, ?_⟩
        simpa [GroundAssignment.setType] using (Subtype.refl (Δ := []) (a := a.reify))
      · exact hback c (List.mem_append_left _ hc)
    · intro v hv
      obtain ⟨b, hb, hbρ, hρb⟩ := htypes v hv
      refine ⟨b, ?_, hbρ, hρb⟩
      change (s.substitution.type v).realize (η.setType (.flex n) a) = some b
      rw [← TypeExpr.realize_setType ha, ← Substitution.extendType_type hk]
      exact hb

end Deferred
end ModalityInference
