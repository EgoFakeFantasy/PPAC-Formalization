import PPAC.Migration.Internal.OriginalHistoryRead

/-! 严格有类型子码的对象执行归纳假设，以及实际历史和完整比较公式的内部存在包。 -/
namespace PPAC.Migration.Internal.OriginalFormulaInductionSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def prefixIH {m} (w mode depth parameter R S a b c d n : Fin m) : Formula m := .all (.all
  (((Formula.mem (Fin.last m).castSucc n.castSucc.castSucc).conj
    (FormulaCodeSyntax.formulaCode w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc b.castSucc.castSucc)).imp
      ((OriginalTransformRowSyntax.run 3 w.castSucc.castSucc mode.castSucc.castSucc depth.castSucc.castSucc parameter.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
        (FormulaTransformExecutionSyntax.executed w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

theorem prefixIH_rename {m j} (w mode depth parameter R S a b c d n : Fin m) (ρ : Fin m → Fin j) :
    (prefixIH w mode depth parameter R S a b c d n).rename ρ = prefixIH (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [prefixIH, Formula.rename, Formula.iff, FormulaCodeSyntax.formulaCode_rename, OriginalTransformRowSyntax.run_rename, FormulaTransformExecutionSyntax.executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem prefixIH_at {m} {Γ : Context m} (w mode depth parameter R S a b c d n x X : Fin m)
    (hi : Derives Γ (prefixIH w mode depth parameter R S a b c d n))
    (hx : Derives Γ (.mem x n)) (ht : Derives Γ (FormulaCodeSyntax.formulaCode w x a b)) :
    Derives Γ ((OriginalTransformRowSyntax.run 3 w mode depth parameter x X).iff (FormulaTransformExecutionSyntax.executed w R S a b c d x X)) := by
  have hh := Derives.allE X (Derives.allE x hi)
  have he : Derives Γ (((Formula.mem x n).conj (FormulaCodeSyntax.formulaCode w x a b)).imp ((OriginalTransformRowSyntax.run 3 w mode depth parameter x X).iff (FormulaTransformExecutionSyntax.executed w R S a b c d x X))) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, Formula.iff, FormulaCodeSyntax.formulaCode_rename, OriginalTransformRowSyntax.run_rename, FormulaTransformExecutionSyntax.executed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hh
  exact .impE he (.conjI hx ht)

def body {m} (w mode depth parameter R S a b c d n : Fin m) : Formula (m+1) :=
  (FormulaTransformRecursionSyntax.graph w.castSucc (Fin.last m) n.castSucc).conj
    (OriginalFormulaHistoryAgreementSyntax.agreement w.castSucc mode.castSucc depth.castSucc parameter.castSucc (Fin.last m) R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc)

def agreedHistory {m} (w mode depth parameter R S a b c d n : Fin m) : Formula m := .ex (body w mode depth parameter R S a b c d n)

theorem agreedHistory_rename {m j} (w mode depth parameter R S a b c d n : Fin m) (ρ : Fin m → Fin j) :
    (agreedHistory w mode depth parameter R S a b c d n).rename ρ = agreedHistory (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [agreedHistory, body, Formula.rename, FormulaTransformRecursionSyntax.graph_rename, OriginalFormulaHistoryAgreementSyntax.agreement_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_agreedHistory {m} {Γ : Context m} (w mode depth parameter R S a b c d n h : Fin m)
    (hg : Derives Γ (FormulaTransformRecursionSyntax.graph w h n))
    (ha : Derives Γ (OriginalFormulaHistoryAgreementSyntax.agreement w mode depth parameter h R S a b c d n)) :
    Derives Γ (agreedHistory w mode depth parameter R S a b c d n) := by
  apply Derives.exI h
  exact of_eq (by simp only [body, Formula.instantiate, Formula.rename, FormulaTransformRecursionSyntax.graph_rename, OriginalFormulaHistoryAgreementSyntax.agreement_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hg ha)

theorem eliminate_agreedHistory {m} {Γ : Context m} (w mode depth parameter R S a b c d n : Fin m) (P : Formula m)
    (he : Derives Γ (agreedHistory w mode depth parameter R S a b c d n))
    (hc : Derives (Context.add (body w mode depth parameter R S a b c d n) (Context.image Formula.raise Γ)) P.raise) :
    Derives Γ P := .exE he hc

end PPAC.Migration.Internal.OriginalFormulaInductionSyntax
