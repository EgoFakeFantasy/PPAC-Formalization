import PPAC.Migration.Internal.SyntaxTypeRecursive

/-! 全内部码/上下文的统一类型递归定律及实际系统存在句子；均为有限纯对象公式。 -/
namespace PPAC.Migration.Internal.SyntaxTypeSystemSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxContextCarrierSyntax SyntaxTypeRecursionSyntax SyntaxTypeJudgmentSyntax SyntaxTypeRecursiveSyntax

def universalLaw {m} (w c : Fin m) : Formula m := .all (.all (.all
  ((typed w.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2))).iff
    (criterion w.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2))))))

def systemBody {m} (w : Fin m) : Formula (m+3) :=
  (tower w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
    ((recursors w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).conj
      (universalLaw w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc))
def system {m} (w : Fin m) : Formula m := .ex (.ex (.ex (systemBody w)))
def existsSystem : Source.Sentence := .ex ((omega (Fin.last 0)).conj (system (Fin.last 0)))

theorem universalLaw_rename {m k} (w c : Fin m) (r : Fin m → Fin k) :
    (universalLaw w c).rename r = universalLaw (r w) (r c) := by
  simp only [universalLaw, Formula.rename, Formula.iff, typed_rename, criterion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem system_rename {m k} (w : Fin m) (r : Fin m → Fin k) :
    (system w).rename r = system (r w) := by
  simp only [system, systemBody, Formula.rename, tower_rename, recursors_rename, universalLaw_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
end PPAC.Migration.Internal.SyntaxTypeSystemSyntax
