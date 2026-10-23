import PPAC.Migration.Internal.NativeFormulaQuotationCorrespondence

/-! 原生全公式替换的实际联合输出：原数值判断、准确quotation和原目标FormulaCode同值成立。 -/
namespace PPAC.Migration.Internal.NativeFormulaQuotationValueSyntax
open Source SourceAlgebra SourceLogic NativeSubstitutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

def value {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w R S a b c d n q : Fin m) : Formula m :=
  (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q).conj
    ((PureQuotationSyntax.formula (input.substituteMapped σ τ) w q).conj (FormulaCodeSyntax.formulaCode w q c d))

def fiber {m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w R S a b c d n : Fin m) : Formula m := .ex
  ((value input σ τ w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)).conj
    (SyntaxMixedFormulaOutputSyntax.uniqueOutput w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)))

theorem value_rename {m k} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w R S a b c d n q : Fin m) (ρ : Fin m → Fin k) :
    (value input σ τ w R S a b c d n q).rename ρ = value input σ τ (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [value, Formula.rename, SyntaxMixedFormulaJudgmentSyntax.substituted_rename, PureQuotationSyntax.formula_rename, FormulaCodeSyntax.formulaCode_rename]

theorem fiber_rename {m k} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w R S a b c d n : Fin m) (ρ : Fin m → Fin k) :
    (fiber input σ τ w R S a b c d n).rename ρ = fiber input σ τ (ρ w) (ρ R) (ρ S) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [fiber, Formula.rename, value_rename, SyntaxMixedFormulaOutputSyntax.uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} {sb sf tb tf : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w R S a b c d n q : Fin m) (hv : Derives Γ (value input σ τ w R S a b c d n q))
    (hu : Derives Γ (SyntaxMixedFormulaOutputSyntax.uniqueOutput w R S a b c d n q)) :
    Derives Γ (fiber input σ τ w R S a b c d n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, value_rename, SyntaxMixedFormulaOutputSyntax.uniqueOutput_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hv hu)

end PPAC.Migration.Internal.NativeFormulaQuotationValueSyntax
