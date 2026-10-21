import PPAC.Migration.Internal.StructuralListTracePrefix

/-! 有效列表的精确一步分解；尾码有效性仍为实际内部有限轨迹。 -/
namespace PPAC.Migration.Internal.StructuralListDecodeSyntax
open Source SourceAlgebra SourceLogic StructuralListSyntax StructuralListTraceSyntax

def tailCase {m} (w n : Fin m) : Formula m := .ex
  ((valid w.castSucc (Fin.last m)).conj (step w.castSucc (Fin.last m) n.castSucc))
def decomposition {m} (w n : Fin m) : Formula m := (nilCode w n).disj (tailCase w n)

theorem tailCase_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (tailCase w n).rename r = tailCase (r w) (r n) := by
  simp only [tailCase, Formula.rename, valid_rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem decomposition_rename {m k} (w n : Fin m) (r : Fin m → Fin k) : (decomposition w n).rename r = decomposition (r w) (r n) := by
  simp only [decomposition, Formula.rename, nilCode_rename, tailCase_rename]

theorem intro_tail {m} {Γ : Context m} (w n t : Fin m) (ht : Derives Γ (valid w t)) (hs : Derives Γ (step w t n)) : Derives Γ (tailCase w n) := by
  apply Derives.exI t
  simp only [Formula.instantiate, Formula.rename, valid_rename, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ht hs
end PPAC.Migration.Internal.StructuralListDecodeSyntax
