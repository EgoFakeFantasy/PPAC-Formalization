import PPAC.Migration.Internal.SyntaxMixedFormulaCaseTyping

/-! 给定原源/目标构造字段后的规范项关系；成员式显式保留原零符号及两端符号相等。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaKnownFieldsSyntax
open Source SourceAlgebra SourceLogic

def equalOperands {m} (w r s a b c d x y X Y : Fin m) : Formula m :=
  (SyntaxCodedMixedTermSyntax.substituted w r s a b c d x X).conj (SyntaxCodedMixedTermSyntax.substituted w r s a b c d y Y)

def memberOperands {m} (w r s a b c d z Z x y X Y : Fin m) : Formula m :=
  (SyntaxAtomSyntax.zeroScalar w z).conj ((Formula.equal z Z).conj (equalOperands w r s a b c d x y X Y))

theorem equalOperands_rename {m k} (w r s a b c d x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (equalOperands w r s a b c d x y X Y).rename ρ = equalOperands (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [equalOperands, Formula.rename, SyntaxCodedMixedTermSyntax.substituted_rename]

theorem memberOperands_rename {m k} (w r s a b c d z Z x y X Y : Fin m) (ρ : Fin m → Fin k) :
    (memberOperands w r s a b c d z Z x y X Y).rename ρ = memberOperands (ρ w) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) (ρ z) (ρ Z) (ρ x) (ρ y) (ρ X) (ρ Y) := by
  simp only [memberOperands, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, equalOperands_rename]

end PPAC.Migration.Internal.SyntaxMixedFormulaKnownFieldsSyntax
