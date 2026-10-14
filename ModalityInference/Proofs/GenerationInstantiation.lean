import ModalityInference.Proofs.Generation
import ModalityInference.Proofs.BoundedSupport
import ModalityInference.Proofs.FlexibleSupport

/-! Fresh scheme instantiation and the identifier support used by generation. -/
namespace ModalityInference

theorem Scheme.freshSubstitution_instantiates (s : Scheme) (nt nm : Nat) (rigid : Bool) :
    Instantiates s (s.freshSubstitution nt nm rigid) := by
  simp [Instantiates, Scheme.freshSubstitution, List.map_map, Function.comp_def]

theorem Scheme.freshSubstitution_flexible (s : Scheme) (nt nm : Nat) :
    (s.freshSubstitution nt nm).Flexible := by
  constructor <;> intro n a ha <;>
    simp only [Scheme.freshSubstitution, Bool.false_eq_true, ↓reduceIte,
      List.mem_map, Prod.exists, Prod.mk.injEq] at ha
  all_goals obtain ⟨p, i, _, rfl, rfl⟩ := ha; exact ⟨_, rfl⟩

theorem Scheme.freshSubstitution_type_bounded (s : Scheme) (nt nm : Nat) {v : TypeVar}
    (hv : v.index < nt) :
    ((s.freshSubstitution nt nm).type v).Bounded
      (nt + s.typeParams.length) (nm + s.modParams.length) := by
  cases v with
  | rigid n => exact hv.trans_le (Nat.le_add_right _ _)
  | flex n =>
    cases he : (s.freshSubstitution nt nm).types.lookup n
    · simpa [Substitution.type, he, TypeExpr.Bounded, TypeVar.index] using
        hv.trans_le (Nat.le_add_right nt s.typeParams.length)
    · rename_i a
      obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
      obtain ⟨⟨p, i⟩, hi, hp⟩ := List.mem_map.mp
        (show (n, a) ∈ (s.freshSubstitution nt nm).types by simp [hh])
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hi)
      have ha : a = .var (.flex (nt + i)) := (congrArg Prod.snd hp).symm
      simpa [Substitution.type, he, ha, TypeExpr.Bounded, TypeVar.index]
        using Nat.add_lt_add_left hlt nt

theorem Scheme.freshSubstitution_mode_bounded (s : Scheme) (nt nm : Nat) {v : ModVar}
    (hv : v.index < nm) :
    ((s.freshSubstitution nt nm).mode v).Bounded (nm + s.modParams.length) := by
  cases v with
  | rigid n => exact hv.trans_le (Nat.le_add_right _ _)
  | flex n =>
    cases he : (s.freshSubstitution nt nm).modes.lookup n
    · simpa [Substitution.mode, he, ModExpr.Bounded, ModVar.index] using
        hv.trans_le (Nat.le_add_right nm s.modParams.length)
    · rename_i a
      obtain ⟨before, after, hh, _⟩ := List.lookup_eq_some_iff.mp he
      obtain ⟨⟨p, i⟩, hi, hp⟩ := List.mem_map.mp
        (show (n, a) ∈ (s.freshSubstitution nt nm).modes by simp [hh])
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hi)
      have ha : a = .var (.flex (nm + i)) := (congrArg Prod.snd hp).symm
      simpa [Substitution.mode, he, ha, ModExpr.Bounded, ModVar.index]
        using Nat.add_lt_add_left hlt nm

theorem Constraint.Bounded.substitute {c : Constraint} {σ : Substitution} {nt nm nt' nm'}
    (hc : c.Bounded nt nm)
    (ht : ∀ v, v.index < nt → (σ.type v).Bounded nt' nm')
    (hm : ∀ v, v.index < nm → (σ.mode v).Bounded nm') :
    (σ.constraint c).Bounded nt' nm' := by
  cases c <;> simp only [Substitution.constraint, Constraint.subst, Constraint.Bounded] at *
  case sub a b | equiv a b => exact ⟨hc.1.subst ht hm, hc.2.subst ht hm⟩
  case mode a b => exact ⟨hc.1.subst hm, hc.2.subst hm⟩
  case defined a => exact hc.subst hm
  case equal v a =>
    have hv := ht v hc.1
    have ha := hc.2.subst ht hm
    cases v with
    | rigid n => exact ⟨hv, ha⟩
    | flex n => cases he : σ.types.lookup n <;>
        simpa [he, Substitution.type, TypeExpr.Bounded] using And.intro hv ha

theorem Bounds.Bounded.substitute {cs : Bounds} {σ : Substitution} {nt nm nt' nm'}
    (hc : cs.Bounded nt nm)
    (ht : ∀ v, v.index < nt → (σ.type v).Bounded nt' nm')
    (hm : ∀ v, v.index < nm → (σ.mode v).Bounded nm') :
    (σ.bounds cs).Bounded nt' nm' := by
  simpa only [Bounds.Bounded, Substitution.bounds, List.forall_mem_map] using
    fun c h => (hc c h).substitute ht hm

def Scheme.Bounded (nt nm : Nat) (s : Scheme) : Prop :=
  s.body.Bounded nt nm ∧ s.bounds.Bounded nt nm

def Scheme.Flexible (s : Scheme) : Prop := s.body.Flexible ∧ s.bounds.Flexible

theorem Scheme.Bounded.instantiate {s : Scheme} {nt nm} (hs : s.Bounded nt nm) :
    let r := s.instantiate nt nm
    r.1.Bounded (nt + s.typeParams.length) (nm + s.modParams.length) ∧
      r.2.Bounded (nt + s.typeParams.length) (nm + s.modParams.length) :=
  ⟨hs.2.substitute (fun _ => s.freshSubstitution_type_bounded nt nm)
    (fun _ => s.freshSubstitution_mode_bounded nt nm),
   hs.1.subst (fun _ => s.freshSubstitution_type_bounded nt nm)
    (fun _ => s.freshSubstitution_mode_bounded nt nm)⟩

theorem Scheme.Flexible.instantiate {s : Scheme} (hs : s.Flexible) (nt nm : Nat) :
    (s.instantiate nt nm).1.Flexible ∧ (s.instantiate nt nm).2.Flexible :=
  ⟨(s.freshSubstitution_flexible nt nm).bounds hs.2,
    (s.freshSubstitution_flexible nt nm).ty hs.1⟩

theorem Scheme.Bounded.mono {s : Scheme} {nt nm nt' nm'} (hs : s.Bounded nt nm)
    (ht : nt ≤ nt') (hm : nm ≤ nm') : s.Bounded nt' nm' :=
  ⟨hs.1.mono ht hm, hs.2.mono ht hm⟩

theorem Scheme.Bounded.share {s : Scheme} {nt nm} (hs : s.Bounded nt nm) :
    s.share.Bounded nt nm := by
  simp_all [Scheme.Bounded, Scheme.share, Constraint.Bounded, TypeExpr.Bounded, ModExpr.Bounded]

theorem Scheme.Bounded.lock {s : Scheme} {nt nm m} (hs : s.Bounded nt nm)
    (hm : m.Bounded nm) : (s.lock m).Bounded nt nm := by
  simp_all [Scheme.Bounded, Scheme.lock, Constraint.Bounded, TypeExpr.Bounded, ModExpr.Bounded]

theorem Scheme.Flexible.share {s : Scheme} (hs : s.Flexible) : s.share.Flexible := by
  simp_all [Scheme.Flexible, Scheme.share, Constraint.Flexible, TypeExpr.Flexible, ModExpr.Flexible]

theorem Scheme.Flexible.lock {s : Scheme} {m} (hs : s.Flexible) (hm : m.Flexible) :
    (s.lock m).Flexible := by
  simp_all [Scheme.Flexible, Scheme.lock, Constraint.Flexible, TypeExpr.Flexible, ModExpr.Flexible]

end ModalityInference
