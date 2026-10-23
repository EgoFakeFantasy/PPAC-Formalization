import PPAC.Migration.Internal.ObjectOriginalMemberProgram

/-! 实际原子程序源字段的对象等词对齐；不调用宿主字段数组。 -/
namespace PPAC.Migration.Internal.AtomicProgramAlignment
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

theorem member_symbol_subst {m} {Γ : Context m} (w s t x y n : Fin m)
    (he : Derives Γ (.equal s t)) (hn : Derives Γ (SyntaxAtomSyntax.memberCode w s x y n)) :
    Derives Γ (SyntaxAtomSyntax.memberCode w t x y n) := by
  let P := SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) x.castSucc y.castSucc n.castSucc
  have h0 : P.instantiate s = SyntaxAtomSyntax.memberCode w s x y n := by simp only [P, Formula.instantiate, SyntaxAtomSyntax.memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have h1 : P.instantiate t = SyntaxAtomSyntax.memberCode w t x y n := by simp only [P, Formula.instantiate, SyntaxAtomSyntax.memberCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hn))

end PPAC.Migration.Internal.AtomicProgramAlignment
