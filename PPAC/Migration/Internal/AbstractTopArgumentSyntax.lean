import PPAC.Migration.Internal.AbstractTopArgumentFields

/-! 受检首槽参数列抽象：真实源列表类型、实际码表及独立逐项程序，码表内部存在绑定。 -/
namespace PPAC.Migration.Internal.AbstractTopArgumentSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def state {m} (w a b A B n q k R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).conj
    (ArgumentProgramFieldSyntax.mapped w R S k A b n q)

def body {m} (w a b A B n q k : Fin m) : Formula (m+2) :=
  state w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc
    n.castSucc.castSucc q.castSucc.castSucc k.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))

def abstracted {m} (w a b A B n q k : Fin m) : Formula m :=
  (SyntaxMixedImageCodeSyntax.termList w k a B n).conj (.ex (.ex (body w a b A B n q k)))

theorem state_rename {m l} (w a b A B n q k R S : Fin m) (ρ : Fin m → Fin l) :
    (state w a b A B n q k R S).rename ρ = state (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) (ρ q) (ρ k) (ρ R) (ρ S) := by
  simp only [state, Formula.rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename, ArgumentProgramFieldSyntax.mapped_rename]

theorem abstracted_rename {m l} (w a b A B n q k : Fin m) (ρ : Fin m → Fin l) :
    (abstracted w a b A B n q k).rename ρ = abstracted (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) (ρ q) (ρ k) := by
  simp only [abstracted, body, Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename, state_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_abstracted {m} {Γ : Context m} (w a b A B n q k R S : Fin m)
    (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a B n))
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hm : Derives Γ (ArgumentProgramFieldSyntax.mapped w R S k A b n q)) :
    Derives Γ (abstracted w a b A B n q k) := by
  apply Derives.conjI hL
  have hs : Derives Γ (state w a b A B n q k R S) := .conjI he hm
  apply Derives.exI R
  apply Derives.exI S
  simpa only [body, Formula.instantiate, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hs

end PPAC.Migration.Internal.AbstractTopArgumentSyntax
