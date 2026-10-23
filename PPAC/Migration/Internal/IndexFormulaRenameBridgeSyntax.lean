import PPAC.Migration.Internal.IndexTermCodedBinderTransport

/-! 所有内部元数据上的公式重命名传输归纳命题；递归指标为内部源码。 -/
namespace PPAC.Migration.Internal.IndexFormulaRenameBridgeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def statement {m} (w I J R S a b c d n q : Fin m) : Formula m :=
  (IndexTermImageCodeSyntax.environment w I J R S a b c d).imp
    ((SyntaxRenameJudgmentSyntax.renamed w I J a b c d n q).imp (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))

def property {m} (w n : Fin m) : Formula m :=
  .all (.all (.all (.all (.all (.all (.all (.all (.all (statement w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc.castSucc (Fin.last (m+6)).castSucc.castSucc (Fin.last (m+7)).castSucc n.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+8)))))))))))

def earlier {m} (w n : Fin m) : Formula m := .all
  (((Formula.mem (Fin.last m) w.castSucc).conj (.mem (Fin.last m) n.castSucc)).imp (property w.castSucc (Fin.last m)))

theorem statement_rename {m k} (w I J R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (statement w I J R S a b c d n q).rename ρ = statement (ρ w) (ρ I) (ρ J) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [statement, Formula.rename, IndexTermImageCodeSyntax.environment_rename, SyntaxRenameJudgmentSyntax.renamed_rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]

theorem property_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (property w n).rename ρ = property (ρ w) (ρ n) := by
  simp only [property, Formula.rename, statement_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (ρ : Fin m → Fin k) :
    (earlier w n).rename ρ = earlier (ρ w) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_at {m} {Γ : Context m} (w I J R S a b c d n q : Fin m)
    (hp : Derives Γ (property w n)) : Derives Γ (statement w I J R S a b c d n q) :=
  of_eq (by simp only [Formula.instantiate, statement_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (Derives.allE q (Derives.allE d (Derives.allE c (Derives.allE b (Derives.allE a (Derives.allE S (Derives.allE R (Derives.allE J (Derives.allE I (hp))))))))))

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (he : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x w)) (hxn : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have hp := Derives.allE x he
  have hi : Derives Γ (((Formula.mem x w).conj (.mem x n)).imp (property w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hp
  exact .impE hi (.conjI hx hxn)

theorem transfer_child {m} {Γ : Context m} (w I J R S a b c d n x q : Fin m)
    (he : Derives Γ (earlier w n)) (hxn : Derives Γ (.mem x n))
    (hEnv : Derives Γ (IndexTermImageCodeSyntax.environment w I J R S a b c d))
    (hOld : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w I J a b c d x q)) :
    Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d x q) :=
  .impE (.impE (property_at w I J R S a b c d x q (earlier_at w n x he (.conjL hOld) hxn)) hEnv) hOld

end PPAC.Migration.Internal.IndexFormulaRenameBridgeSyntax
