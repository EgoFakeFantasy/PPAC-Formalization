import PPAC.Migration.Internal.FreeSubstImageCode

/-! 原自由替换参数L的独立程序特化：仅实际bound恒等像表内部存在，free项表保持同一L。 -/
namespace PPAC.Migration.Internal.FreeSubstProgramSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def ready {m} (w b a c L n q I R : Fin m) : Formula m :=
  (SyntaxIdentityMapSyntax.identityCode w b I).conj
    ((IndexTermImageCodeSyntax.converted true w I R b b c).conj
      (FormulaTransformExecutionSyntax.executed w R L b a b c n q))

def body {m} (w b a c L n q : Fin m) : Formula (m+2) :=
  ready w.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def executed {m} (w b a c L n q : Fin m) : Formula m :=
  (SyntaxFreeSubstSyntax.termList w a c L).conj (.ex (.ex (body w b a c L n q)))

theorem ready_rename {m k} (w b a c L n q I R : Fin m) (ρ : Fin m → Fin k) :
    (ready w b a c L n q I R).rename ρ = ready (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) (ρ q) (ρ I) (ρ R) := by
  simp only [ready, Formula.rename, SyntaxIdentityMapSyntax.identityCode_rename, IndexTermImageCodeSyntax.converted_rename, FormulaTransformExecutionSyntax.executed_rename]

theorem executed_rename {m k} (w b a c L n q : Fin m) (ρ : Fin m → Fin k) :
    (executed w b a c L n q).rename ρ = executed (ρ w) (ρ b) (ρ a) (ρ c) (ρ L) (ρ n) (ρ q) := by
  simp only [executed, body, Formula.rename, SyntaxFreeSubstSyntax.termList_rename, ready_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_executed {m} {Γ : Context m} (w b a c L n q I R : Fin m)
    (hl : Derives Γ (SyntaxFreeSubstSyntax.termList w a c L))
    (hi : Derives Γ (SyntaxIdentityMapSyntax.identityCode w b I))
    (hr : Derives Γ (IndexTermImageCodeSyntax.converted true w I R b b c))
    (hq : Derives Γ (FormulaTransformExecutionSyntax.executed w R L b a b c n q)) :
    Derives Γ (executed w b a c L n q) := by
  have hd : Derives Γ (ready w b a c L n q I R) := .conjI hi (.conjI hr hq)
  apply Derives.conjI hl
  apply Derives.exI I
  apply Derives.exI R
  exact of_eq (by simp only [body, Formula.instantiate, ready_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hd

end PPAC.Migration.Internal.FreeSubstProgramSyntax
