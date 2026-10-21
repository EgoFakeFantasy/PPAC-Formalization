import PPAC.Migration.Internal.ObjectSyntaxLogical
import PPAC.Migration.PowerSetLogic

/-! 全内部上下文对和上下文状态集合的实际三层幂集载体。 -/
namespace PPAC.Migration.Internal.SyntaxContextCarrierSyntax
open Source SourceAlgebra SourceLogic PowerSetSyntax PairSyntax

def tower {m} (w a c u : Fin m) : Formula m :=
  (powerOf a w).conj ((powerOf c a).conj (powerOf u c))
def existsTower {m} (w : Fin m) : Formula m := .ex (.ex (.ex
  (tower w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))
def pairExistsIn {m} (c b f : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) c.castSucc).conj (ordered (Fin.last m) b.castSucc f.castSucc))

theorem tower_rename {m k} (w a c u : Fin m) (r : Fin m → Fin k) :
    (tower w a c u).rename r = tower (r w) (r a) (r c) (r u) := by
  simp only [tower, Formula.rename, powerOf_rename]

theorem existsTower_rename {m k} (w : Fin m) (r : Fin m → Fin k) :
    (existsTower w).rename r = existsTower (r w) := by
  simp only [existsTower, Formula.rename, tower_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem pairExistsIn_rename {m k} (c b f : Fin m) (r : Fin m → Fin k) :
    (pairExistsIn c b f).rename r = pairExistsIn (r c) (r b) (r f) := by
  simp only [pairExistsIn, Formula.rename, ordered_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
end PPAC.Migration.Internal.SyntaxContextCarrierSyntax
