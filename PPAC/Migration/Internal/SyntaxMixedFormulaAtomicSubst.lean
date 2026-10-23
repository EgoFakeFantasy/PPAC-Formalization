import PPAC.Migration.Internal.SyntaxMixedFormulaAtomicCases

namespace PPAC.Migration.Internal.SyntaxMixedFormulaAtomicSubst
open Source SourceAlgebra SourceLogic SyntaxRenameQuerySyntax

theorem term_source {m} {Γ : Context m} (w r s a b c d n q z1 : Fin m)
    (he : Derives Γ (.equal n z1)) (hp : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w r s a b c d n q)) :
    Derives Γ (SyntaxCodedMixedTermSyntax.substituted w r s a b c d z1 q) := by
  let P := SyntaxCodedMixedTermSyntax.substituted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) q.castSucc
  have e0 : P.instantiate n = SyntaxCodedMixedTermSyntax.substituted w r s a b c d n q := by
    simp only [P, Formula.instantiate, SyntaxCodedMixedTermSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate z1 = SyntaxCodedMixedTermSyntax.substituted w r s a b c d z1 q := by
    simp only [P, Formula.instantiate, SyntaxCodedMixedTermSyntax.substituted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hp))

end PPAC.Migration.Internal.SyntaxMixedFormulaAtomicSubst
