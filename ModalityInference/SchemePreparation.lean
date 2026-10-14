import ModalityInference.Declarative

/-! Scope-preserving preparation of a symbolic scheme comparison.
Only quantified identifiers are renamed. The target contributes its original
type assumptions, both directions of equalities, and written definedness guards.
The source body remains a subtyping goal, separate from guarded source bounds.
-/
namespace ModalityInference.SchemePreparation

structure Prepared where
  sourceRenaming : Substitution
  targetRenaming : Substitution
  assumptions : Bounds
  sourceBounds : Bounds
  sourceType : Ty
  targetType : Ty
  firstType : Nat
  firstMode : Nat
  nextType : Nat
  nextMode : Nat
  deriving Repr

def prepare (ambient : Bounds) (source target : Scheme) : Prepared :=
  let (nt, nm) := source.subsumptionIndices ambient target
  let targetRenaming := target.freshSubstitution nt nm true
  let ft := nt + target.typeParams.length
  let fm := nm + target.modParams.length
  let sourceRenaming := source.freshSubstitution ft fm
  { sourceRenaming, targetRenaming
    assumptions := ambient ++ (targetRenaming.bounds target.bounds).assumptions
    sourceBounds := sourceRenaming.bounds source.bounds
    sourceType := sourceRenaming.ty source.body
    targetType := targetRenaming.ty target.body
    firstType := ft
    firstMode := fm
    nextType := ft + source.typeParams.length
    nextMode := fm + source.modParams.length }

/-- Return exactly the source quantifier domain, applying the solved symbolic
action to fresh images rather than extending its domain with free identifiers. -/
def reconstruct (p : Prepared) (action : Substitution) : Substitution :=
  { types := p.sourceRenaming.types.map fun (n, a) => (n, action.ty a)
    modes := p.sourceRenaming.modes.map fun (n, m) => (n, m.subst action.mode) }

end ModalityInference.SchemePreparation
