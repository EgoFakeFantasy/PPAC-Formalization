import PPAC.Migration.Internal.ObjectSyntaxRenameTotal

/-! 子判断的目标字段替换，保持实际映射码、完整图及两端作用域。 -/
namespace PPAC.Migration.Internal.SyntaxRenameEndpointSubst
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax

theorem term_target {m} {Γ : Context m}  (w r s a b c d n q q1 : Fin m)
    (he : Derives Γ (.equal q q1)) (hp : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d n q)) : Derives Γ (SyntaxRenameTermSyntax.renamed w r s a b c d n q1) := by
  let P := SyntaxRenameTermSyntax.renamed w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  have e0 : P.instantiate q = SyntaxRenameTermSyntax.renamed w r s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate q1 = SyntaxRenameTermSyntax.renamed w r s a b c d n q1 := by
    simp only [P, Formula.instantiate, SyntaxRenameTermSyntax.renamed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

theorem check_target {m} {Γ : Context m} (advance : Bool) (w x r s a b c d q q1 : Fin m)
    (he : Derives Γ (.equal q q1)) (hp : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q)) : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q1) := by
  let P := SyntaxRenameRecursiveSyntax.check advance w.castSucc x.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m)
  have e0 : P.instantiate q = SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q := by
    simp only [P, Formula.instantiate, SyntaxRenameRecursiveSyntax.check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate q1 = SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q1 := by
    simp only [P, Formula.instantiate, SyntaxRenameRecursiveSyntax.check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

end PPAC.Migration.Internal.SyntaxRenameEndpointSubst
