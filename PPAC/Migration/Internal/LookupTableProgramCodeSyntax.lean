import PPAC.Migration.Internal.LookupTableCorrectness

/-! 固定编译程序的原树编码及全部运行时参数的对象量化。不是任意内部程序的通用解释器。 -/
namespace PPAC.Migration.Internal.LookupTableProgramCodeSyntax
open Source SourceAlgebra SourceLogic LookupTableProgramSyntax

def code {m} (w P : Fin m) : Formula m := OriginalTreeQuotationSyntax.tree (programTree lookupProgram) w P

def encodedExecution {m} (w P n i y : Fin m) : Formula m :=
  (code w P).conj (LookupTableExecutionSyntax.executed w n i y)

def correctAt {m} (w P n i y : Fin m) : Formula m :=
  (encodedExecution w P n i y).iff (StrictLookupSyntax.checked w n i y)

def uniform {m} (w P : Fin m) : Formula m := .all (.all (.all
  (correctAt w.castSucc.castSucc.castSucc P.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))


def uniqueCode {m} (w P : Fin m) : Formula m := .all
  ((code w.castSucc (Fin.last m)).imp (.equal (Fin.last m) P.castSucc))

def programValue {m} (w P : Fin m) : Formula m :=
  (Formula.mem P w).conj ((code w P).conj ((uniform w P).conj (uniqueCode w P)))

def existsProgram {m} (w : Fin m) : Formula m := .ex (programValue w.castSucc (Fin.last m))

theorem code_rename {m k} (w P : Fin m) (ρ : Fin m → Fin k) :
    (code w P).rename ρ = code (ρ w) (ρ P) := OriginalTreeQuotationSyntax.tree_rename _ _ _ _

theorem encodedExecution_rename {m k} (w P n i y : Fin m) (ρ : Fin m → Fin k) :
    (encodedExecution w P n i y).rename ρ = encodedExecution (ρ w) (ρ P) (ρ n) (ρ i) (ρ y) := by
  simp only [encodedExecution, Formula.rename, code_rename, LookupTableExecutionSyntax.executed_rename]

theorem correctAt_rename {m k} (w P n i y : Fin m) (ρ : Fin m → Fin k) :
    (correctAt w P n i y).rename ρ = correctAt (ρ w) (ρ P) (ρ n) (ρ i) (ρ y) := by
  simp only [correctAt, Formula.iff, Formula.rename, encodedExecution_rename, StrictLookupSyntax.checked_rename]

theorem uniform_rename {m k} (w P : Fin m) (ρ : Fin m → Fin k) :
    (uniform w P).rename ρ = uniform (ρ w) (ρ P) := by
  simp only [uniform, Formula.rename, correctAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueCode_rename {m k} (w P : Fin m) (ρ : Fin m → Fin k) :
    (uniqueCode w P).rename ρ = uniqueCode (ρ w) (ρ P) := by
  simp only [uniqueCode, Formula.rename, code_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem programValue_rename {m k} (w P : Fin m) (ρ : Fin m → Fin k) :
    (programValue w P).rename ρ = programValue (ρ w) (ρ P) := by
  simp only [programValue, Formula.rename, code_rename, uniform_rename, uniqueCode_rename]

theorem existsProgram_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) :
    (existsProgram w).rename ρ = existsProgram (ρ w) := by
  simp only [existsProgram, Formula.rename, programValue_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_existsProgram {m} {Γ : Context m} (w P : Fin m) (hp : Derives Γ (programValue w P)) :
    Derives Γ (existsProgram w) := by
  apply Derives.exI P
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, programValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp

end PPAC.Migration.Internal.LookupTableProgramCodeSyntax
