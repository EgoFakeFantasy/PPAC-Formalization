import PPAC.Migration.Internal.FreeSubstProgramCorrectness

/-! 受检程序的实际结果及比较全部内部候选的唯一纤维。 -/
namespace PPAC.Migration.Internal.FreeSubstProgramValueSyntax
open Source SourceAlgebra SourceLogic FreeSubstProgramSyntax

def inputGuard {m} (w b a c L n : Fin m) : Formula m :=
  (FormulaCodeSyntax.formulaCode w n b a).conj (SyntaxFreeSubstSyntax.termList w a c L)

theorem inputGuard_rename {m k} (w b a c L n : Fin m) (ρ : Fin m → Fin k) :
    (inputGuard w b a c L n).rename ρ = inputGuard (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) := by
  simp only [inputGuard, Formula.rename, FormulaCodeSyntax.formulaCode_rename, SyntaxFreeSubstSyntax.termList_rename]

def uniqueOutput {m} (w b a c L n q : Fin m) : Formula m := .all
  ((executed w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def value {m} (w b a c L n q : Fin m) : Formula m :=
  (executed w b a c L n q).conj ((FormulaCodeSyntax.formulaCode w q b c).conj
    ((Formula.mem q w).conj (uniqueOutput w b a c L n q)))

def fiber {m} (w b a c L n : Fin m) : Formula m := .ex
  (value w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m))

theorem uniqueOutput_rename {m k} (w b a c L n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w b a c L n q).rename ρ = uniqueOutput (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (w b a c L n q : Fin m) (ρ : Fin m → Fin k) :
    (value w b a c L n q).rename ρ = value (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) (ρ q) := by
  simp only [value, Formula.rename, executed_rename, FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename]

theorem fiber_rename {m k} (w b a c L n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w b a c L n).rename ρ = fiber (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) := by
  simp only [fiber, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w b a c L n q : Fin m) (hq : Derives Γ (value w b a c L n q)) :
    Derives Γ (fiber w b a c L n) := by
  apply Derives.exI q
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

end PPAC.Migration.Internal.FreeSubstProgramValueSyntax
