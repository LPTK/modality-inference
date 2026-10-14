import ModalityInference.Rewriting

/-! Symbolic scheme witnesses must be types in the declared grammar. Projected
bounds alone do not supply such a witness. These examples also distinguish fixed
free variables and unguarded body subtyping from guarded constraint entailment. -/
namespace ModalityInference.SchemeReconstruction

/-- Modal wrappers preserve the underlying variable; constructed types have no
variable at their head. -/
def baseVariable : Ty → Option TypeVar
  | .var v => some v
  | .modal a _ => baseVariable a
  | _ => none

/-- Any preorder on base variables respected by the declared bounds is preserved
by every declarative subtype derivation. -/
theorem subtype_baseRelation {Δ a b} {R : Option TypeVar → Option TypeVar → Prop}
    (hrefl : ∀ x, R x x) (htrans : ∀ {x y z}, R x y → R y z → R x z)
    (hb : ∀ x y, Constraint.sub x y ∈ Δ → R (baseVariable x) (baseVariable y))
    (h : Subtype Δ a b) : R (baseVariable a) (baseVariable b) := by
  induction h
  case trans _ _ _ _ _ ih ih' => exact htrans ih ih'
  case bound h => exact hb _ _ h
  case congr _ _ ih => exact ih
  all_goals exact hrefl _

def rigidBounds : Bounds :=
  [.sub (.var (.rigid 0)) (.var (.rigid 2)),
   .sub (.var (.rigid 0)) (.var (.rigid 3)),
   .sub (.var (.rigid 1)) (.var (.rigid 2)),
   .sub (.var (.rigid 1)) (.var (.rigid 3))]

/-- The four rigid bounds form a poset with two lower and two upper elements,
and no element between both lower and both upper elements. -/
def baseReachable (x y : Option TypeVar) : Prop := x = y ∨
  (x = some (.rigid 0) ∨ x = some (.rigid 1)) ∧
  (y = some (.rigid 2) ∨ y = some (.rigid 3))

theorem baseReachable_trans {x y z} :
    baseReachable x y → baseReachable y z → baseReachable x z := by
  rintro (hxy | ⟨hx, hy⟩) (hyz | ⟨hy', hz⟩)
  · exact .inl (hxy.trans hyz)
  · exact .inr ⟨hxy ▸ hy', hz⟩
  · exact .inr ⟨hx, hyz ▸ hy⟩
  · rcases hy with h | h <;> rcases hy' with h' | h' <;> simp_all

theorem bound_baseReachable {a b} (h : Constraint.sub a b ∈ rigidBounds) :
    baseReachable (baseVariable a) (baseVariable b) := by
  simp [rigidBounds] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp [baseReachable, baseVariable]

theorem subtype_baseReachable {a b} (h : Subtype rigidBounds a b) :
    baseReachable (baseVariable a) (baseVariable b) :=
  subtype_baseRelation (fun _ => .inl rfl) baseReachable_trans
    (fun _ _ => bound_baseReachable) h

/-- Every lower-to-upper consequence of eliminating the proposed intermediate
type is already a declared assumption, including its definedness guards. -/
theorem crossed_consequences : EntailsAll rigidBounds rigidBounds := by
  intro c hc
  have he := hc
  simp only [rigidBounds, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals
    exact ⟨.bound hc, by simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels],
      by simp [TypeExpr.DefinedUnder, TypeExpr.wellFormedBounds, ModeModels]⟩

/-- Each Boolean coordinate admits the usual lower-bound join. Applying the same
fact to the reversed bounds gives the corresponding past-coordinate witness. -/
theorem projected_join_witness : ∀ a b c d : Bool,
    a ≤ c → a ≤ d → b ≤ c → b ≤ d →
    a ≤ (a || b) ∧ b ≤ (a || b) ∧ (a || b) ≤ c ∧ (a || b) ≤ d := by decide

/-- No type in the current grammar realizes the intermediate element, even
though all crossed rigid consequences and projected coordinate witnesses exist. -/
theorem no_interpolant (t : Ty)
    (ha : Subtype rigidBounds (.var (.rigid 0)) t)
    (hb : Subtype rigidBounds (.var (.rigid 1)) t)
    (hc : Subtype rigidBounds t (.var (.rigid 2)))
    (hd : Subtype rigidBounds t (.var (.rigid 3))) : False := by
  have ha := subtype_baseReachable ha
  have hb := subtype_baseReachable hb
  have hc := subtype_baseReachable hc
  have hd := subtype_baseReachable hd
  simp only [baseVariable] at ha hb hc hd
  rcases ha with he | ⟨_, he | he⟩
  · simp [baseReachable, ← he] at hb
  · simp [baseReachable, he] at hd
  · simp [baseReachable, he] at hc

def sandwichSource : Scheme :=
  {typeParams := [0], body := .unit, bounds :=
    [.sub (.var (.rigid 0)) (.var (.flex 0)),
     .sub (.var (.rigid 1)) (.var (.flex 0)),
     .sub (.var (.flex 0)) (.var (.rigid 2)),
     .sub (.var (.flex 0)) (.var (.rigid 3))]}

def sandwichTarget : Scheme := {body := .unit, bounds := rigidBounds}

/-- The example satisfies exactly the parameter and residual-context premises of
the scheme-checker soundness and completeness contracts. -/
theorem sandwich_contract_premises :
    (sandwichSource.typeParams.Nodup ∧ sandwichSource.modParams.Nodup) ∧
    (sandwichTarget.typeParams.Nodup ∧ sandwichTarget.modParams.Nodup) ∧
    Residual sandwichTarget.bounds := by
  simp [sandwichSource, sandwichTarget, Residual, rigidBounds, TypeExpr.outer]

theorem sandwich_no_subsumes : ¬ Subsumes [] sandwichSource sandwichTarget := by
  rintro ⟨σ, _, hb, _⟩
  change EntailsAll rigidBounds
    [.sub (.var (.rigid 0)) (σ.type (.flex 0)),
     .sub (.var (.rigid 1)) (σ.type (.flex 0)),
     .sub (σ.type (.flex 0)) (.var (.rigid 2)),
     .sub (σ.type (.flex 0)) (.var (.rigid 3))] at hb
  apply no_interpolant (σ.type (.flex 0))
  · exact (hb (.sub (.var (.rigid 0)) (σ.type (.flex 0))) (by simp)).1
  · exact (hb (.sub (.var (.rigid 1)) (σ.type (.flex 0))) (by simp)).1
  · exact (hb (.sub (σ.type (.flex 0)) (.var (.rigid 2))) (by simp)).1
  · exact (hb (.sub (σ.type (.flex 0)) (.var (.rigid 3))) (by simp)).1

def freeVariable : Scheme := .mono (.var (.flex 0))
def unitScheme : Scheme := .mono .unit

theorem free_variable_contract_premises :
    (freeVariable.typeParams.Nodup ∧ freeVariable.modParams.Nodup) ∧
    (unitScheme.typeParams.Nodup ∧ unitScheme.modParams.Nodup) ∧
    Residual unitScheme.bounds := by
  simp [freeVariable, unitScheme, Scheme.mono, Residual]

/-- A free flexible identifier is fixed by scheme instantiation just as a rigid
identifier is. In particular, its shape cannot be chosen by the checker. -/
theorem free_variable_not_unit : ¬ Subsumes [] freeVariable unitScheme := by
  rintro ⟨⟨ts, ms⟩, hi, _, ht⟩
  simp [Instantiates, freeVariable, Scheme.mono] at hi
  rcases hi with ⟨rfl, rfl⟩
  change Subtype [] (.var (.flex 0)) .unit at ht
  have hh := subtype_baseRelation (R := Eq) (fun _ => rfl)
    (fun h h' => h.trans h') (by simp) ht
  cases hh

def undefinedMode : ModExpr := .leftResidual (.const Mode.identity) (.const Mode.global)
def undefinedScheme : Scheme := .mono (.modal .unit undefinedMode)

theorem undefined_contract_premises :
    (undefinedScheme.typeParams.Nodup ∧ undefinedScheme.modParams.Nodup) ∧
    (undefinedScheme.typeParams.Nodup ∧ undefinedScheme.modParams.Nodup) ∧
    Residual undefinedScheme.bounds := by
  simp [undefinedScheme, Scheme.mono, Residual]

theorem undefined_body_not_defined : ¬ undefinedScheme.body.DefinedUnder [] := by
  simp [TypeExpr.DefinedUnder, undefinedScheme, Scheme.mono, TypeExpr.wellFormedBounds,
    ModeModels, ModeSatisfies, ModExpr.WellFormed, undefinedMode, ModExpr.eval,
    Mode.leftResidual, Mode.identity, Mode.global]

/-- The body comparison in `Subsumes` is an unguarded subtype judgment. Its
reflexivity remains available even when that body is not defined. -/
theorem undefined_reflexive : Subsumes [] undefinedScheme undefinedScheme := by
  refine ⟨{}, ?_, ?_, ?_⟩
  · simp [Instantiates, undefinedScheme, Scheme.mono]
  · simp [undefinedScheme, Scheme.mono, EntailsAll, Substitution.bounds]
  · exact .refl

end ModalityInference.SchemeReconstruction
