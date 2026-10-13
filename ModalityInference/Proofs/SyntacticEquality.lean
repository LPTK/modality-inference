import ModalityInference.Core.Syntax

/-! Kernel-checked laws for the syntax's derived Boolean equality functions. -/
namespace ModalityInference

deriving instance ReflBEq for Mode, ModVar, ModExpr, TypeVar, TypeExpr, Constraint
deriving instance LawfulBEq for Mode, ModVar, ModExpr, TypeVar, TypeExpr, Constraint

end ModalityInference
