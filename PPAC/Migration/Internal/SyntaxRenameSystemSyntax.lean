import PPAC.Migration.Internal.SyntaxRenameRecursive

/-! 固定重命名关系的八个内部参数全称递归定律及实际ω/载体/递归系统。 -/
namespace PPAC.Migration.Internal.SyntaxRenameSystemSyntax
open Source SourceAlgebra SourceLogic SyntaxRenameJudgmentSyntax SyntaxRenameRecursiveSyntax

def universalLaw {m} (w : Fin m) : Formula m := .all (.all (.all (.all (.all (.all (.all (.all ((renamed w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc (Fin.last (m+6)).castSucc (Fin.last (m+7))).iff (criterion w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc (Fin.last (m+6)).castSucc (Fin.last (m+7)))))))))))

def system {m} (w : Fin m) : Formula m := (SyntaxRenameRecursionSyntax.actualRecursors w).conj (universalLaw w)

def existsSystem : Source.Sentence := .ex ((OmegaSyntax.omega (Fin.last 0)).conj (system (Fin.last 0)))

theorem universalLaw_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (universalLaw w).rename ρ = universalLaw (ρ w) := by
  simp only [universalLaw, Formula.rename, Formula.iff, renamed_rename, criterion_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem system_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (system w).rename ρ = system (ρ w) := by
  simp only [system, Formula.rename, SyntaxRenameRecursionSyntax.actualRecursors_rename, universalLaw_rename]
end PPAC.Migration.Internal.SyntaxRenameSystemSyntax
