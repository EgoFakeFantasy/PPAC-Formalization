import PPAC.Migration.Internal.SyntaxMixedFormulaTagCases

/-! 原逻辑字段和普通/提升子判断的对象等词替换。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaLogicalSubst
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax

theorem check_source {m} {Γ : Context m} (advance : Bool) (w x r s a b c d q z1 : Fin m)
    (he : Derives Γ (.equal x z1)) (hp : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d q)) : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w z1 r s a b c d q) := by
  let P := SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc (Fin.last m) r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc q.castSucc
  have e0 : P.instantiate x = SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d q := by
    simp only [P, Formula.instantiate, SyntaxMixedFormulaRecursiveSyntax.check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxMixedFormulaRecursiveSyntax.check advance w z1 r s a b c d q := by
    simp only [P, Formula.instantiate, SyntaxMixedFormulaRecursiveSyntax.check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem single_child {m} {Γ : Context m} (tag : Nat) (w x n z1 : Fin m)
    (he : Derives Γ (.equal x z1)) (hp : Derives Γ (SyntaxLogicalSyntax.singleCode tag w x n)) : Derives Γ (SyntaxLogicalSyntax.singleCode tag w z1 n) := by
  let P := SyntaxLogicalSyntax.singleCode tag w.castSucc (Fin.last m) n.castSucc
  have e0 : P.instantiate x = SyntaxLogicalSyntax.singleCode tag w x n := by
    simp only [P, Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxLogicalSyntax.singleCode tag w z1 n := by
    simp only [P, Formula.instantiate, SyntaxLogicalSyntax.singleCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem binary_x {m} {Γ : Context m} (kind : Fin 4) (w x y n z1 : Fin m)
    (he : Derives Γ (.equal x z1)) (hp : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w z1 y n) := by
  let P := SyntaxLogicalSyntax.binaryCode kind w.castSucc (Fin.last m) y.castSucc n.castSucc
  have e0 : P.instantiate x = SyntaxLogicalSyntax.binaryCode kind w x y n := by
    simp only [P, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxLogicalSyntax.binaryCode kind w z1 y n := by
    simp only [P, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem binary_y {m} {Γ : Context m} (kind : Fin 4) (w x y n z1 : Fin m)
    (he : Derives Γ (.equal y z1)) (hp : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x y n)) : Derives Γ (SyntaxLogicalSyntax.binaryCode kind w x z1 n) := by
  let P := SyntaxLogicalSyntax.binaryCode kind w.castSucc x.castSucc (Fin.last m) n.castSucc
  have e0 : P.instantiate y = SyntaxLogicalSyntax.binaryCode kind w x y n := by
    simp only [P, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxLogicalSyntax.binaryCode kind w x z1 n := by
    simp only [P, Formula.instantiate, SyntaxLogicalSyntax.binaryCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

end PPAC.Migration.Internal.SyntaxMixedFormulaLogicalSubst
