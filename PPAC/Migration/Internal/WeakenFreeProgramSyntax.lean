import PPAC.Migration.Internal.FreeSubstProgramValue
import PPAC.Migration.Internal.SyntaxWeakenFreeUnique

/-! 原free头槽弱化的独立程序特化，实际恒等/位移码及双项像表在对象量词内取得。 -/
namespace PPAC.Migration.Internal.WeakenFreeProgramSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def ready {m} (w a b B n q I J R S : Fin m) : Formula m :=
  (SyntaxIdentityMapSyntax.identityCode w a I).conj ((SyntaxFreeShiftSyntax.shiftCode w b B J).conj
    ((IndexTermImageCodeSyntax.environment w I J R S a b a B).conj
      (FormulaTransformExecutionSyntax.executed w R S a b a B n q)))

def body {m} (w a b B n q : Fin m) : Formula (m+4) :=
  ready w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))

def executed {m} (w a b B n q : Fin m) : Formula m := .ex (.ex (.ex (.ex (body w a b B n q))))

theorem ready_rename {m k} (w a b B n q I J R S : Fin m) (ρ : Fin m → Fin k) :
    (ready w a b B n q I J R S).rename ρ = ready (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) (ρ q) (ρ I) (ρ J) (ρ R) (ρ S) := by
  simp only [ready, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename, SyntaxFreeShiftSyntax.shiftCode_rename, IndexTermImageCodeSyntax.environment_rename, FormulaTransformExecutionSyntax.executed_rename]

theorem executed_rename {m k} (w a b B n q : Fin m) (ρ : Fin m → Fin k) :
    (executed w a b B n q).rename ρ = executed (ρ w) (ρ a) (ρ b) (ρ B) (ρ n) (ρ q) := by
  simp only [executed, body, Formula.rename, ready_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_executed {m} {Γ : Context m} (w a b B n q I J R S : Fin m)
    (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w a I))
    (hj : Derives Γ (SyntaxFreeShiftSyntax.shiftCode w b B J))
    (he : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b a B))
    (hq : Derives Γ (FormulaTransformExecutionSyntax.executed w R S a b a B n q)) :
    Derives Γ (executed w a b B n q) := by
  have hd : Derives Γ (ready w a b B n q I J R S) := .conjI hi (.conjI hj (.conjI he hq))
  apply Derives.exI I
  apply Derives.exI J
  apply Derives.exI R
  apply Derives.exI S
  exact of_eq (by simp only [body, Formula.instantiate, ready_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hd

end PPAC.Migration.Internal.WeakenFreeProgramSyntax
