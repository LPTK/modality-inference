import ModalityInference.Proofs.ComparisonNestedAnchors
import ModalityInference.Proofs.ComparisonDefinedCovers

/-! Matching a declared endpoint through an arbitrary finite public context
produces the exact variance-correct demands for its shared source parameter. -/
namespace ModalityInference.ComparisonNestedAnchors

open ComparisonDeclaredAnchors (fixed)
open ComparisonDefinedCovers (Refines)

private theorem fixed_var {p : SchemePreparation.Prepared} {v : TypeVar}
    (h : fixed p (.var v) = true) : ComparisonShapeSolver.sourceAllowed p v = false := by
  simpa [fixed, TypeExpr.typeVariables] using h

theorem variableDemand_fixed {p : SchemePreparation.Prepared} {a b : Ty}
    (h : fixed p a = true) (lower : Bool) : variableDemand p lower a b = [] := by
  cases a <;> try rfl
  next v =>
    cases v
    · simp only [variableDemand, fixed_var h, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · rfl

theorem matchTypes_fixed_self {p : SchemePreparation.Prepared} {a : Ty}
    (h : fixed p a = true) : matchTypes p a a = [] := by
  induction a with
  | var v | unit | credit =>
      simp only [matchTypes, variableDemand_fixed h, List.append_nil]
  | modal a m ih =>
      simpa only [matchTypes, beq_self_eq_true, ↓reduceIte] using ih h
  | prod a b iha ihb | sum a b iha ihb | fn a b iha ihb =>
      have h' : fixed p a = true ∧ fixed p b = true := by
        simpa [fixed, TypeExpr.typeVariables, List.all_eq_true, List.mem_dedup,
          List.mem_append, or_imp, forall_and] using h
      simp only [matchTypes, iha h'.1, ihb h'.2, List.append_nil]

theorem matchTypes_variable {p : SchemePreparation.Prepared} {name : Nat} {a : Ty}
    (hn : ComparisonShapeSolver.sourceAllowed p (.flex name) = true)
    (ha : fixed p a = true) :
    matchTypes p a (.var (.flex name)) = [⟨name,true,a⟩] ∧
      matchTypes p (.var (.flex name)) a = [⟨name,false,a⟩] := by
  have ht : ∀lower, variableDemand p lower (.var (.flex name)) a = [⟨name,lower,a⟩] := by
    intro lower
    simp [variableDemand, hn, ha]
  cases a <;> simp only [matchTypes, variableDemand_fixed ha, ht, List.nil_append,
    List.append_nil, and_self]

inductive Context where
  | hole
  | closed (a : Ty)
  | prod (a b : Context)
  | sum (a b : Context)
  | fn (a b : Context)
  | modal (a : Context) (m : ModExpr)

def Context.plug : Context → Ty → Ty
  | .hole, a => a
  | .closed a, _ => a
  | .prod a b, t => .prod (a.plug t) (b.plug t)
  | .sum a b, t => .sum (a.plug t) (b.plug t)
  | .fn a b, t => .fn (a.plug t) (b.plug t)
  | .modal a m, t => .modal (a.plug t) m

def Context.Fixed (p : SchemePreparation.Prepared) : Context → Prop
  | .hole => True
  | .closed a => fixed p a = true
  | .prod a b | .sum a b | .fn a b => a.Fixed p ∧ b.Fixed p
  | .modal a _ => a.Fixed p

def Context.requests (name : Nat) (endpoint : Ty) : Context → Bool → List Demand
  | .hole, lower => [⟨name,lower,endpoint⟩]
  | .closed _, _ => []
  | .prod a b, lower | .sum a b, lower =>
      a.requests name endpoint lower ++ b.requests name endpoint lower
  | .fn a b, lower => a.requests name endpoint (!lower) ++ b.requests name endpoint lower
  | .modal a _, lower => a.requests name endpoint lower

/-- The same source parameter is preserved at every occurrence, including
opposite variances within one nested context. -/
theorem Context.matchTypes_exact {p : SchemePreparation.Prepared} {name : Nat} {a : Ty}
    (hn : ComparisonShapeSolver.sourceAllowed p (.flex name) = true)
    (ha : fixed p a = true) (c : Context) (hc : c.Fixed p) (lower : Bool) :
    (if lower then matchTypes p (c.plug a) (c.plug (.var (.flex name)))
      else matchTypes p (c.plug (.var (.flex name))) (c.plug a)) =
      c.requests name a lower := by
  induction c generalizing lower with
  | hole =>
      cases lower
      · exact (matchTypes_variable hn ha).2
      · exact (matchTypes_variable hn ha).1
  | closed t => cases lower <;> exact matchTypes_fixed_self hc
  | prod a b iha ihb | sum a b iha ihb =>
      cases lower
      · simpa only [Context.plug, Context.requests, Bool.false_eq_true, ↓reduceIte,
          matchTypes] using congrArg₂ (· ++ ·) (iha hc.1 false) (ihb hc.2 false)
      · simpa only [Context.plug, Context.requests, ↓reduceIte,
          matchTypes] using congrArg₂ (· ++ ·) (iha hc.1 true) (ihb hc.2 true)
  | fn a b iha ihb =>
      cases lower
      · simpa only [Context.plug, Context.requests, Bool.false_eq_true, ↓reduceIte,
          matchTypes, Bool.not_false] using congrArg₂ (· ++ ·) (iha hc.1 true) (ihb hc.2 false)
      · simpa only [Context.plug, Context.requests, Bool.false_eq_true, ↓reduceIte,
          matchTypes, Bool.not_true] using congrArg₂ (· ++ ·) (iha hc.1 false) (ihb hc.2 true)
  | modal a m ih =>
      cases lower
      · simpa only [Context.plug, Context.requests, Bool.false_eq_true,
          ↓reduceIte, matchTypes, beq_self_eq_true] using ih hc false
      · simpa only [Context.plug, Context.requests, ↓reduceIte,
          matchTypes, beq_self_eq_true] using ih hc true

def Context.image : Context → CompareTy → CompareTy
  | .hole, a => a
  | .closed a, _ => .ofTy a
  | .prod a b, t => .prod (a.image t) (b.image t)
  | .sum a b, t => .sum (a.image t) (b.image t)
  | .fn a b, t => .fn (a.image t) (b.image t)
  | .modal a m, t => .modal (a.image t) m

@[simp] theorem Context.image_ofTy (c : Context) (a : Ty) :
    c.image (.ofTy a) = .ofTy (c.plug a) := by
  induction c <;> simp_all [Context.image, Context.plug, CompareTy.ofTy]

def Demand.Holds (Δ : Bounds) (images : Nat → CompareTy) (d : Demand) : Prop :=
  Refines Δ d.lower (.ofTy d.endpoint) (images d.name)

/-- Structural reconstruction uses every occurrence demand with its original
variance. Definedness of the written endpoint supplies the modal guards. -/
theorem Context.requests_lift {Δ : Bounds} {name : Nat} {endpoint : Ty}
    {images : Nat → CompareTy} (c : Context) (lower : Bool)
    (hd : (c.plug endpoint).DefinedUnder Δ)
    (h : ∀d ∈ c.requests name endpoint lower, d.Holds Δ images) :
    Refines Δ lower (.ofTy (c.plug endpoint)) (c.image (images name)) := by
  induction c generalizing lower with
  | hole => exact h ⟨name,lower,endpoint⟩ (by simp [Context.requests])
  | closed a => exact Refines.refl lower (CompareTy.wellShaped_ofTy a Δ)
  | prod a b iha ihb =>
      have hd' := TypeExpr.definedUnder_prod.mp hd
      exact Refines.prod (iha lower hd'.1 (fun d hm => h d (List.mem_append_left _ hm)))
        (ihb lower hd'.2 (fun d hm => h d (List.mem_append_right _ hm)))
  | sum a b iha ihb =>
      have hd' := TypeExpr.definedUnder_sum.mp hd
      exact Refines.sum (iha lower hd'.1 (fun d hm => h d (List.mem_append_left _ hm)))
        (ihb lower hd'.2 (fun d hm => h d (List.mem_append_right _ hm)))
  | fn a b iha ihb =>
      have hd' := TypeExpr.definedUnder_fn.mp hd
      exact Refines.fn (iha (!lower) hd'.1 (fun d hm => h d (List.mem_append_left _ hm)))
        (ihb lower hd'.2 (fun d hm => h d (List.mem_append_right _ hm)))
  | modal a m ih =>
      have hd' := TypeExpr.definedUnder_modal.mp hd
      have hh := ih lower hd'.1 h
      cases lower <;> exact AlgebraSubtype.congr hh (.refl hd'.2)

theorem Context.matchTypes_sound {p : SchemePreparation.Prepared} {name : Nat}
    {endpoint : Ty} {images : Nat → CompareTy}
    (hn : ComparisonShapeSolver.sourceAllowed p (.flex name) = true)
    (he : fixed p endpoint = true) (c : Context) (hc : c.Fixed p) (lower : Bool)
    (hd : (c.plug endpoint).DefinedUnder p.assumptions)
    (h : ∀d ∈ (if lower then matchTypes p (c.plug endpoint) (c.plug (.var (.flex name)))
      else matchTypes p (c.plug (.var (.flex name))) (c.plug endpoint)),
      d.Holds p.assumptions images) :
    Refines p.assumptions lower (.ofTy (c.plug endpoint)) (c.image (images name)) := by
  rw [c.matchTypes_exact hn he hc lower] at h
  exact c.requests_lift lower hd h

/-- A whole declared edge is followed by a certified structural comparison;
its endpoint is never decomposed as an assumed subtype premise. -/
theorem Context.after_declared {p : SchemePreparation.Prepared} {name : Nat}
    {start endpoint : Ty} {images : Nat → CompareTy}
    (hn : ComparisonShapeSolver.sourceAllowed p (.flex name) = true)
    (he : fixed p endpoint = true) (hs : fixed p start = true)
    (c : Context) (hc : c.Fixed p)
    (hedge : Constraint.sub start (c.plug endpoint) ∈ p.assumptions)
    (hd : (c.plug endpoint).DefinedUnder p.assumptions)
    (h : ∀d ∈ demandsFor p start (c.plug (.var (.flex name))),
      d.Holds p.assumptions images) :
    AlgebraSubtype p.assumptions (.ofTy start) (c.image (images name)) := by
  apply (AlgebraSubtype.shaped (.bound hedge)).trans
  apply c.matchTypes_sound hn he hc true hd
  intro d hm
  apply h d
  apply List.mem_append_right
  refine List.mem_flatMap.mpr ⟨(start,c.plug endpoint), ?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨.sub start (c.plug endpoint),hedge,by simp [pairs]⟩
  · apply List.mem_append_left
    simpa [hs] using hm

theorem Context.before_declared {p : SchemePreparation.Prepared} {name : Nat}
    {endpoint finish : Ty} {images : Nat → CompareTy}
    (hn : ComparisonShapeSolver.sourceAllowed p (.flex name) = true)
    (he : fixed p endpoint = true) (hf : fixed p finish = true)
    (c : Context) (hc : c.Fixed p)
    (hedge : Constraint.sub (c.plug endpoint) finish ∈ p.assumptions)
    (hd : (c.plug endpoint).DefinedUnder p.assumptions)
    (h : ∀d ∈ demandsFor p (c.plug (.var (.flex name))) finish,
      d.Holds p.assumptions images) :
    AlgebraSubtype p.assumptions (c.image (images name)) (.ofTy finish) := by
  apply AlgebraSubtype.trans (b := .ofTy (c.plug endpoint))
  · apply c.matchTypes_sound hn he hc false hd
    intro d hm
    apply h d
    apply List.mem_append_right
    refine List.mem_flatMap.mpr ⟨(c.plug endpoint,finish), ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨.sub (c.plug endpoint) finish,hedge,by simp [pairs]⟩
    · apply List.mem_append_right
      simpa [hf] using hm
  · exact .shaped (.bound hedge)

end ModalityInference.ComparisonNestedAnchors
