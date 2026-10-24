import PPAC.Migration.Internal.AbstractTopTerm

/-! 首槽抽象的纯项判断：直接使用实际码表与原混合项替换，码表全部内部EX。 -/
namespace PPAC.Migration.Internal.AbstractTopTermSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def state {m} (w a b A B n q R S : Fin m) : Formula m :=
  (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S).conj
    (SyntaxCodedMixedTermSyntax.substituted w R S a B A b n q)

def body {m} (w a b A B n q : Fin m) : Formula (m+2) :=
  state w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1))

def abstracted {m} (w a b A B n q : Fin m) : Formula m := .ex (.ex (body w a b A B n q))

theorem state_rename {m l} (w a b A B n q R S : Fin m) (ρ : Fin m → Fin l) :
    (state w a b A B n q R S).rename ρ = state (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) (ρ q) (ρ R) (ρ S) := by
  simp only [state, Formula.rename, SyntaxTopCodedEnvironmentSyntax.abstractCoded_rename, SyntaxCodedMixedTermSyntax.substituted_rename]

theorem abstracted_rename {m l} (w a b A B n q : Fin m) (ρ : Fin m → Fin l) :
    (abstracted w a b A B n q).rename ρ = abstracted (ρ w) (ρ a) (ρ b) (ρ A) (ρ B) (ρ n) (ρ q) := by
  simp only [abstracted, body, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_abstracted {m} {Γ : Context m} (w a b A B n q R S : Fin m)
    (he : Derives Γ (SyntaxTopCodedEnvironmentSyntax.abstractCoded w a b A B R S))
    (hq : Derives Γ (SyntaxCodedMixedTermSyntax.substituted w R S a B A b n q)) :
    Derives Γ (abstracted w a b A B n q) := by
  have hs : Derives Γ (state w a b A B n q R S) := .conjI he hq
  apply Derives.exI R
  apply Derives.exI S
  simpa only [body, Formula.instantiate, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hs

end PPAC.Migration.Internal.AbstractTopTermSyntax
