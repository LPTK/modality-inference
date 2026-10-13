import ModalityInference.Core.Syntax

/-! Kernel-checked laws for the syntax's derived Boolean equality functions. -/
namespace ModalityInference

deriving instance ReflBEq for Mode, ModVar, ModExpr, TypeVar, TypeExpr
deriving instance LawfulBEq for Mode, ModVar, ModExpr, TypeVar, TypeExpr

end ModalityInference
