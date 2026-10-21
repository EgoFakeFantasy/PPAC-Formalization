import PPAC.Migration.Internal.SyntaxNodeInjective

/-! 实际变量索引识别/唯一解码的纯对象公式；唯一性遍历所有内部候选索引。 -/
namespace PPAC.Migration.Internal.SyntaxVariableDecodeSyntax
open Source SourceAlgebra SourceLogic SyntaxVariableSyntax

def recognized {m} (bound : Bool) (w n : Fin m) : Formula m := .ex (code bound w.castSucc (Fin.last m) n.castSucc)

def uniqueIndex {m} (bound : Bool) (w n i : Fin m) : Formula m := .all
  ((code bound w.castSucc (Fin.last m) n.castSucc).imp (.equal (Fin.last m) i.castSucc))

def indexFiber {m} (bound : Bool) (w n : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (code bound w.castSucc (Fin.last m) n.castSucc)).conj
    (uniqueIndex bound w.castSucc n.castSucc (Fin.last m)))

theorem recognized_rename {m k} (bound : Bool) (w n : Fin m) (s : Fin m → Fin k) : (recognized bound w n).rename s = recognized bound (s w) (s n) := by
  simp only [recognized, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueIndex_rename {m k} (bound : Bool) (w n i : Fin m) (s : Fin m → Fin k) : (uniqueIndex bound w n i).rename s = uniqueIndex bound (s w) (s n) (s i) := by
  simp only [uniqueIndex, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem indexFiber_rename {m k} (bound : Bool) (w n : Fin m) (s : Fin m → Fin k) : (indexFiber bound w n).rename s = indexFiber bound (s w) (s n) := by
  simp only [indexFiber, Formula.rename, code_rename, uniqueIndex_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_recognized {m} {Γ : Context m} (bound : Bool) (w n i : Fin m) (hc : Derives Γ (code bound w i n)) : Derives Γ (recognized bound w n) := by
  apply Derives.exI i
  simpa only [Formula.instantiate, code_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hc

theorem intro_fiber {m} {Γ : Context m} (bound : Bool) (w n i : Fin m) (hi : Derives Γ (.mem i w))
    (hc : Derives Γ (code bound w i n)) (hu : Derives Γ (uniqueIndex bound w n i)) : Derives Γ (indexFiber bound w n) := by
  apply Derives.exI i
  simp only [Formula.instantiate, Formula.rename, code_rename, uniqueIndex_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hi hc) hu
end PPAC.Migration.Internal.SyntaxVariableDecodeSyntax
