import ModalityInference.Proofs.PolymorphicCapture
import ModalityInference.Proofs.Substitution

/-! Binder transport for a polymorphic value nested inside another closure. -/
namespace ModalityInference.ScopedCaptures

def package : SchemeValue := ⟨PolymorphicCapture.functionScheme, PolymorphicCapture.value⟩

def nested : Value := .closure [package.value] [some package.scheme] (.var 1)

def renamedCredit : Scheme := .mono (.modal .credit (.var (.flex 1)))
def renamedFunction : Scheme := {modParams := [1], body := .fn .unit renamedCredit.body}
def renamedValue : Value := .closure [.credit (.heap 0)] [some renamedCredit] (.var 1)

theorem package_scheme : (package.subst {}).scheme = renamedFunction := rfl

theorem package_value : (package.subst {}).value = renamedValue := by
  simp [package, SchemeValue.subst, Value.substCapturedTypes, renamedValue, renamedCredit,
    PolymorphicCapture.value, PolymorphicCapture.creditScheme, PolymorphicCapture.functionScheme,
    Scheme.substitutionAction, Scheme.binderRenaming, Scheme.fresheningIndices,
    Scheme.subst, Scheme.instantiate, Scheme.freshSubstitution, Scheme.mono,
    Substitution.compose, Substitution.bounds, Substitution.ty, Substitution.mode,
    TypeExpr.subst, ModExpr.subst, AnnotatedTerm.substTypes, Term.mapAnnotation,
    TypeExpr.modeVariables, Bounds.modeVariables, ModExpr.freeVariables, ModVar.index]

theorem nested_transport : nested.substCapturedTypes {} =
    .closure [renamedValue] [some renamedFunction] (.var 1) := by
  have hs : package.scheme.subst {} = renamedFunction := package_scheme
  simpa [nested, Value.substCapturedTypes, SchemeValue.subst, AnnotatedTerm.substTypes,
    Term.mapAnnotation, hs] using
    congrArg (fun v => Value.closure [v] [some renamedFunction] (.var 1)) package_value

/-- Uniform substitution renames the outer capture scheme but leaves the
quantified variable in the captured value's metadata at its old name. -/
theorem uniform_transport : nested.substTypes {} =
    .closure [PolymorphicCapture.value] [some renamedFunction] (.var 1) := by
  simp [nested, Value.substTypes, Value.mapAnnotation, package,
    PolymorphicCapture.value, PolymorphicCapture.creditScheme, PolymorphicCapture.functionScheme,
    renamedFunction, renamedCredit, Scheme.mono, Scheme.subst, Scheme.fresheningIndices,
    Scheme.instantiate, Scheme.freshSubstitution, Substitution.bounds, Substitution.ty,
    Substitution.mode, TypeExpr.subst, ModExpr.subst, Term.mapAnnotation,
    TypeExpr.modeVariables, Bounds.modeVariables, ModExpr.freeVariables, ModVar.index]

theorem uniform_and_scoped_differ : nested.substTypes {} ≠ nested.substCapturedTypes {} := by
  rw [uniform_transport, nested_transport]
  intro h
  cases h

theorem same_runtime : ValueErasure (nested.substTypes {}) (nested.substCapturedTypes {}) := by
  rw [uniform_transport, nested_transport]
  exact .closure (.cons (.closure (.cons .credit .nil) rfl) .nil) rfl

end ModalityInference.ScopedCaptures
