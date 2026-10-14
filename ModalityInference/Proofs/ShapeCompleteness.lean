import ModalityInference.Proofs.ShapeTermination
import ModalityInference.Proofs.GroundInstantiation
import ModalityInference.Proofs.GroundOrder

/-! The finite-shape precheck succeeds on every satisfiable input. -/
namespace ModalityInference

def TypeExpr.shapeUnder (ρ : TypeVar → Ty) : Ty → Ty
  | .var v => ρ v
  | .unit => .unit
  | .credit => .credit
  | .prod a b => .prod (a.shapeUnder ρ) (b.shapeUnder ρ)
  | .sum a b => .sum (a.shapeUnder ρ) (b.shapeUnder ρ)
  | .fn a b => .fn (a.shapeUnder ρ) (b.shapeUnder ρ)
  | .modal a _ => a.shapeUnder ρ

def GroundTy.shape : GroundTy → Ty
  | .unit _ => .unit
  | .credit _ => .credit
  | .prod a b _ => .prod a.shape b.shape
  | .sum a b _ => .sum a.shape b.shape
  | .fn a b _ => .fn a.shape b.shape

@[simp] theorem GroundTy.shape_modal (a : GroundTy) (m : Mode) :
    (a.modal m).shape = a.shape := by
  cases a <;> rfl

theorem TypeExpr.shapeUnder_subst (a : Ty) (ρ σ : TypeVar → Ty) (μ : ModVar → ModExpr) :
    (a.subst σ μ).shapeUnder ρ = a.shapeUnder (fun v => (σ v).shapeUnder ρ) := by
  induction a <;> simp_all [TypeExpr.subst, TypeExpr.shapeUnder]

@[simp] theorem TypeExpr.shapeUnder_eraseModes (a : Ty) (ρ : TypeVar → Ty) :
    a.eraseModes.shapeUnder ρ = a.shapeUnder ρ := by
  induction a <;> simp_all [TypeExpr.eraseModes, TypeExpr.shapeUnder]

@[simp] theorem TypeExpr.eraseModes_idem (a : Ty) : a.eraseModes.eraseModes = a.eraseModes := by
  induction a <;> simp_all [TypeExpr.eraseModes]

theorem TypeExpr.shapeUnder_occurs_le (a : Ty) (ρ : TypeVar → Ty) {v : TypeVar}
    (hv : v ∈ a.typeVars) : (ρ v).shapeSize ≤ (a.shapeUnder ρ).shapeSize := by
  induction a <;> simp_all [TypeExpr.typeVars, TypeExpr.shapeUnder, TypeExpr.shapeSize]
  all_goals rcases hv with hv | hv <;> simp_all <;> omega

theorem TypeExpr.eraseModes_not_modal (a b : Ty) (m : ModExpr) :
    a.eraseModes ≠ .modal b m := by
  induction a <;> simp_all [TypeExpr.eraseModes]

theorem TypeExpr.shapeUnder_occurs_lt (a : Ty) (ρ : TypeVar → Ty) {v : TypeVar}
    (hv : v ∈ a.typeVars) (hp : a.eraseModes = a) (hne : a ≠ .var v) :
    (ρ v).shapeSize < (a.shapeUnder ρ).shapeSize := by
  cases a <;> simp_all [TypeExpr.typeVars, TypeExpr.shapeUnder, TypeExpr.shapeSize]
  case modal a m => exact False.elim (a.eraseModes_not_modal a m hp)
  all_goals rcases hv with hv | hv <;> have hle := TypeExpr.shapeUnder_occurs_le _ ρ hv <;> omega

theorem TypeExpr.eraseModes_subst (a : Ty) (σ : TypeVar → Ty) (μ : ModVar → ModExpr) :
    (a.subst σ μ).eraseModes = a.eraseModes.subst (fun v => (σ v).eraseModes) ModExpr.var := by
  induction a <;> simp_all [TypeExpr.subst, TypeExpr.eraseModes]

namespace ShapePairs

def Compatible (ρ : TypeVar → Ty) (ps : List (Ty × Ty)) : Prop :=
  ∀ a b, (a, b) ∈ ps → a.eraseModes = a ∧ b.eraseModes = b ∧ a.shapeUnder ρ = b.shapeUnder ρ

@[simp] theorem compatible_cons {ρ a b ps} : Compatible ρ ((a, b) :: ps) ↔
    (a.eraseModes = a ∧ b.eraseModes = b ∧ a.shapeUnder ρ = b.shapeUnder ρ) ∧ Compatible ρ ps := by
  constructor
  · intro h
    exact ⟨h a b List.mem_cons_self, fun x y hxy => h x y (List.mem_cons_of_mem _ hxy)⟩
  · rintro ⟨hab, hr⟩ x y hxy
    rcases List.mem_cons.mp hxy with he | hxy
    · cases he; exact hab
    · exact hr x y hxy

theorem Compatible.replace {ρ ps v t} (h : Compatible ρ ps) (ht : t.eraseModes = t)
    (he : ρ v = t.shapeUnder ρ) :
    Compatible ρ (ps.map fun (a, b) =>
      (a.subst (replace v t) ModExpr.var, b.subst (replace v t) ModExpr.var)) := by
  intro a b hab
  obtain ⟨⟨x, y⟩, hxy, hab⟩ := List.mem_map.mp hab
  cases hab
  obtain ⟨hx, hy, hxy⟩ := h x y hxy
  have hp : (fun w => (ShapePairs.replace v t w).eraseModes) = ShapePairs.replace v t := by
    funext w
    by_cases hw : w = v <;> simp [ShapePairs.replace, hw, ht, TypeExpr.eraseModes]
  have hv : (fun w => (ShapePairs.replace v t w).shapeUnder ρ) = ρ := by
    funext w
    by_cases hw : w = v <;> simp [ShapePairs.replace, hw, he, TypeExpr.shapeUnder]
  simp only [TypeExpr.eraseModes_subst, TypeExpr.shapeUnder_subst, hp, hv, hx, hy, hxy, and_self]

theorem Compatible.check {ρ ps} (h : Compatible ρ ps) (fuel : Nat) :
    checkShapePairs fuel ps = .exhausted ∨ checkShapePairs fuel ps = .success () := by
  induction fuel generalizing ps with
  | zero => exact .inl rfl
  | succ fuel ih =>
    cases ps with
    | nil => exact .inr rfl
    | cons pair ps =>
      rcases pair with ⟨a, b⟩
      obtain ⟨⟨ha, hb, hab⟩, hr⟩ := compatible_cons.mp h
      by_cases he : a = b
      · simpa [checkShapePairs, he] using ih hr
      have hne : (a == b) = false := by simp [he]
      by_cases hva : ∃ v, a = .var v
      · obtain ⟨v, rfl⟩ := hva
        have hoc : v ∉ b.typeVars := by
          intro hv
          have hn := b.shapeUnder_occurs_lt ρ hv hb (Ne.symm he)
          simp only [TypeExpr.shapeUnder] at hab
          rw [hab] at hn
          exact (Nat.lt_irrefl _) hn
        have hh := ih (hr.replace hb hab)
        unfold ShapePairs.replace at hh
        simpa [checkShapePairs, hne, hoc] using hh
      by_cases hvb : ∃ v, b = .var v
      · obtain ⟨v, rfl⟩ := hvb
        have hoc : v ∉ a.typeVars := by
          intro hv
          have hn := a.shapeUnder_occurs_lt ρ hv ha he
          simp only [TypeExpr.shapeUnder] at hab
          rw [hab] at hn
          exact (Nat.lt_irrefl _) hn
        have hh := ih (hr.replace ha hab.symm)
        unfold ShapePairs.replace at hh
        cases a <;> simp_all [checkShapePairs]
      have ham (x : Ty) (m : ModExpr) : a ≠ .modal x m :=
        fun he => a.eraseModes_not_modal x m (ha.trans he)
      have hbm (x : Ty) (m : ModExpr) : b ≠ .modal x m :=
        fun he => b.eraseModes_not_modal x m (hb.trans he)
      cases a <;> cases b <;> simp_all [TypeExpr.shapeUnder, TypeExpr.eraseModes]
      all_goals
        have hh := ih (compatible_cons.mpr ⟨⟨ha.1, hb.1, h.1⟩,
          compatible_cons.mpr ⟨⟨ha.2, hb.2, h.2⟩, hr⟩⟩)
        simpa [checkShapePairs, show ¬ (_ ∧ _) from fun ⟨hx, hy⟩ => he hx hy] using hh

end ShapePairs

theorem GroundOrder.shape_eq {a b} (h : GroundOrder a b) : a.shape = b.shape := by
  induction h <;> simp_all [GroundTy.shape]

theorem TypeExpr.realize_shape {a : Ty} {ρ : GroundAssignment} {t : GroundTy}
    (h : a.realize ρ = some t) : a.shapeUnder (fun v => (ρ.types v).shape) = t.shape := by
  induction a generalizing t <;>
    simp only [TypeExpr.realize, bind, pure, Option.bind_eq_some_iff] at h
  all_goals aesop (add simp [TypeExpr.shapeUnder, GroundTy.shape])

theorem GroundModels.checkShapes {ρ cs} (h : GroundModels ρ cs) (fuel : Nat) :
    checkShapes fuel cs = .exhausted ∨ checkShapes fuel cs = .success () := by
  unfold ModalityInference.checkShapes
  apply ShapePairs.Compatible.check (ρ := fun v => (ρ.types v).shape)
  intro a b hab
  obtain ⟨c, hc, he⟩ := List.mem_filterMap.mp hab
  have hs := h c hc
  cases c <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at he
  all_goals rcases he with ⟨rfl, rfl⟩
  all_goals simp only [TypeExpr.eraseModes_idem, TypeExpr.shapeUnder_eraseModes,
    TypeExpr.eraseModes, TypeExpr.shapeUnder, true_and]
  case sub x y =>
    obtain ⟨x, y, hx, hy, hxy⟩ := hs
    rw [TypeExpr.realize_shape hx, TypeExpr.realize_shape hy]
    exact (GroundOrder.of_subtype hxy).shape_eq
  case equiv x y =>
    obtain ⟨x, y, hx, hy, hxy, _⟩ := hs
    rw [TypeExpr.realize_shape hx, TypeExpr.realize_shape hy]
    exact (GroundOrder.of_subtype hxy).shape_eq
  case equal v t =>
    obtain ⟨y, hy, hxy, _⟩ := hs
    rw [TypeExpr.realize_shape hy]
    exact (GroundOrder.of_subtype hxy).shape_eq

theorem checkShapes_complete {cs : Bounds} (h : BoundsSatisfiable cs) :
    ∃ n, ∀ fuel ≥ n, checkShapes fuel cs = .success () := by
  obtain ⟨ρ, hρ⟩ := h.ground
  obtain ⟨n, result, hn, he⟩ := checkShapes_eventually cs
  have hc := hρ.checkShapes n
  rw [he n (Nat.le_refl n)] at hc
  rcases hc with hc | hc
  · exact False.elim (hn hc)
  · exact ⟨n, fun fuel hf => (he fuel hf).trans hc⟩

end ModalityInference
